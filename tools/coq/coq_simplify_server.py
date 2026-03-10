#!/usr/bin/env python3
import json
import os
import re
import subprocess
import tempfile
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
COQ_DIR = ROOT / 'tools' / 'coq'
KERNEL = COQ_DIR / 'ltl_kernel.v'

COQ_ENV = 'rh1'
HOST = '127.0.0.1'
PORT = int(os.environ.get('COQ_SIMPLIFY_PORT', '8081'))


def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True, check=False)


def ensure_kernel_compiled():
    cmd = ['conda', 'run', '-n', COQ_ENV, 'coqc', '-Q', str(COQ_DIR), 'DSL4FSM', str(KERNEL)]
    p = run(cmd)
    if p.returncode != 0:
        raise RuntimeError(f'Failed to compile ltl_kernel.v:\n{p.stdout}\n{p.stderr}')


def strip_outer_parens(s: str) -> str:
    s = s.strip()
    while s.startswith('(') and s.endswith(')'):
        depth = 0
        ok = True
        for i, ch in enumerate(s):
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    ok = False
                    break
        if ok and depth == 0:
            s = s[1:-1].strip()
        else:
            break
    return s


def split_top_level(s: str, op: str):
    depth = 0
    i = 0
    while i <= len(s) - len(op):
        ch = s[i]
        if ch == '(':
            depth += 1
            i += 1
            continue
        if ch == ')':
            depth -= 1
            i += 1
            continue
        if depth == 0 and s.startswith(op, i):
            return s[:i].strip(), s[i + len(op):].strip()
        i += 1
    return None


def parse_ltl_expr(s: str):
    s = strip_outer_parens(s.strip())
    if not s:
        raise ValueError('empty formula')

    low = s.lower()
    if low == 'true':
        return ('true',)
    if low == 'false':
        return ('false',)

    split_imp = split_top_level(s, '->')
    if split_imp:
        l, r = split_imp
        return ('imp', parse_ltl_expr(l), parse_ltl_expr(r))

    if s.startswith('G(') and s.endswith(')'):
        return ('glob', parse_ltl_expr(s[2:-1]))
    if s.startswith('X(') and s.endswith(')'):
        return ('next', parse_ltl_expr(s[2:-1]))

    if s.startswith('!'):
        rest = s[1:].strip()
        if rest.startswith('(') and rest.endswith(')'):
            return ('not', parse_ltl_expr(rest[1:-1]))
        return ('not', parse_ltl_expr(rest))

    # Base proposition (state/event/constraint symbolized or textual)
    atom = re.sub(r'\s+', ' ', s).strip()
    return ('atom', atom)


def ast_to_coq(ast, atom_to_id):
    tag = ast[0]
    if tag == 'true':
        return 'LTrue'
    if tag == 'false':
        return 'LFalse'
    if tag == 'atom':
        a = ast[1]
        if a not in atom_to_id:
            atom_to_id[a] = len(atom_to_id) + 1
        return f"Atom {atom_to_id[a]}"
    if tag == 'not':
        return f"LNot ({ast_to_coq(ast[1], atom_to_id)})"
    if tag == 'next':
        return f"LNext ({ast_to_coq(ast[1], atom_to_id)})"
    if tag == 'glob':
        return f"Glob ({ast_to_coq(ast[1], atom_to_id)})"
    if tag == 'imp':
        return f"LImp ({ast_to_coq(ast[1], atom_to_id)}) ({ast_to_coq(ast[2], atom_to_id)})"
    raise ValueError(f'unsupported AST node: {tag}')


def build_list_term(formulas):
    atom_to_id = {}
    id_to_atom = {}
    terms = []

    for f in formulas:
        ast = parse_ltl_expr(f)
        term = ast_to_coq(ast, atom_to_id)
        terms.append(term)

    for k, v in atom_to_id.items():
        id_to_atom[v] = k

    return '[' + '; '.join(terms) + ']', id_to_atom


def parse_simplified_list(coqc_output):
    m = re.search(r"=\s*(\[[\s\S]*?\])\s*\n\s*: list ltl", coqc_output)
    if not m:
        raise RuntimeError(f'Unable to parse Coq output:\n{coqc_output}')
    return m.group(1).strip()


def split_list_items(inner: str):
    items = []
    depth = 0
    cur = []
    for ch in inner:
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        if ch == ';' and depth == 0:
            item = ''.join(cur).strip()
            if item:
                items.append(item)
            cur = []
        else:
            cur.append(ch)
    tail = ''.join(cur).strip()
    if tail:
        items.append(tail)
    return items


def tokenize_coq_term(s: str):
    s = s.strip()
    toks = re.findall(r"Atom|LTrue|LFalse|LNot|LAnd|LImp|LNext|Glob|\(|\)|\d+", s)
    if ''.join(toks).replace('Atom', 'Atom').replace('LTrue', 'LTrue').replace('LFalse', 'LFalse').replace('LNot', 'LNot').replace('LAnd', 'LAnd').replace('LImp', 'LImp').replace('LNext', 'LNext').replace('Glob', 'Glob') == '':
        return toks
    return toks


def parse_coq_term_tokens(toks, i=0):
    if i >= len(toks):
        raise ValueError('unexpected end of tokens')
    t = toks[i]

    if t in ('LTrue', 'LFalse'):
        return (('true',) if t == 'LTrue' else ('false',), i + 1)

    if t == 'Atom':
        if i + 1 >= len(toks) or not toks[i + 1].isdigit():
            raise ValueError('Atom without index')
        return (('atom_id', int(toks[i + 1])), i + 2)

    if t in ('LNot', 'LNext', 'Glob'):
        if i + 1 >= len(toks) or toks[i + 1] != '(':
            raise ValueError(f'{t} expects (')
        sub, j = parse_coq_term_tokens(toks, i + 2)
        if j >= len(toks) or toks[j] != ')':
            raise ValueError(f'{t} missing )')
        tag = {'LNot': 'not', 'LNext': 'next', 'Glob': 'glob'}[t]
        return ((tag, sub), j + 1)

    if t in ('LAnd', 'LImp'):
        if i + 1 >= len(toks) or toks[i + 1] != '(':
            raise ValueError(f'{t} expects first (')
        left, j = parse_coq_term_tokens(toks, i + 2)
        if j >= len(toks) or toks[j] != ')':
            raise ValueError(f'{t} missing first )')
        if j + 1 >= len(toks) or toks[j + 1] != '(':
            raise ValueError(f'{t} expects second (')
        right, k = parse_coq_term_tokens(toks, j + 2)
        if k >= len(toks) or toks[k] != ')':
            raise ValueError(f'{t} missing second )')
        tag = 'and' if t == 'LAnd' else 'imp'
        return ((tag, left, right), k + 1)

    raise ValueError(f'unexpected token: {t}')


def parse_coq_term(s: str):
    toks = tokenize_coq_term(s)
    ast, j = parse_coq_term_tokens(toks, 0)
    if j != len(toks):
        raise ValueError(f'unparsed tokens in term: {toks[j:]}')
    return ast


def ast_to_ltl_string(ast, id_to_atom):
    tag = ast[0]
    if tag == 'true':
        return 'true'
    if tag == 'false':
        return 'false'
    if tag == 'atom_id':
        idx = ast[1]
        if idx not in id_to_atom:
            raise ValueError(f'unknown Atom id {idx}')
        return id_to_atom[idx]
    if tag == 'not':
        return f"!({ast_to_ltl_string(ast[1], id_to_atom)})"
    if tag == 'next':
        return f"X({ast_to_ltl_string(ast[1], id_to_atom)})"
    if tag == 'glob':
        return f"G({ast_to_ltl_string(ast[1], id_to_atom)})"
    if tag == 'imp':
        return f"({ast_to_ltl_string(ast[1], id_to_atom)}) -> ({ast_to_ltl_string(ast[2], id_to_atom)})"
    if tag == 'and':
        return f"({ast_to_ltl_string(ast[1], id_to_atom)}) && ({ast_to_ltl_string(ast[2], id_to_atom)})"
    raise ValueError(f'unsupported AST tag {tag}')


def decode_list_term_ast(list_term):
    if list_term == '[]':
        return []
    if not (list_term.startswith('[') and list_term.endswith(']')):
        raise RuntimeError(f'Unexpected list term: {list_term}')
    inner = list_term[1:-1].strip()
    if not inner:
        return []

    out = []
    for item in split_list_items(inner):
        out.append(parse_coq_term(item))
    return out


def is_not_of(a, b):
    return a[0] == 'not' and a[1] == b


def are_complements(a, b):
    if a == ('not', b) or b == ('not', a):
        return True
    if a[0] == 'next' and b[0] == 'next':
        return are_complements(a[1], b[1])
    if a[0] == 'glob' and b[0] == 'glob':
        return are_complements(a[1], b[1])
    return False


def simplify_formula_ast(ast):
    tag = ast[0]
    if tag in ('true', 'false', 'atom_id'):
        return ast
    if tag in ('not', 'next', 'glob'):
        sub = simplify_formula_ast(ast[1])
        if tag == 'not':
            if sub[0] == 'true':
                return ('false',)
            if sub[0] == 'false':
                return ('true',)
            if sub[0] == 'not':
                return simplify_formula_ast(sub[1])
        if tag == 'next':
            if sub[0] == 'true':
                return ('true',)
            if sub[0] == 'false':
                return ('false',)
        if tag == 'glob':
            if sub[0] == 'true':
                return ('true',)
            if sub[0] == 'false':
                return ('false',)
        return (tag, sub)
    if tag in ('and', 'imp'):
        left = simplify_formula_ast(ast[1])
        right = simplify_formula_ast(ast[2])
        if tag == 'and':
            if left[0] == 'false' or right[0] == 'false':
                return ('false',)
            if left[0] == 'true':
                return right
            if right[0] == 'true':
                return left
            if left == right:
                return left
            if is_not_of(left, right) or is_not_of(right, left):
                return ('false',)
            return ('and', left, right)
        # implication
        if left[0] == 'false' or right[0] == 'true':
            return ('true',)
        if left[0] == 'true':
            return right
        if right[0] == 'false':
            return simplify_formula_ast(('not', left))
        if left == right:
            return ('true',)
        return ('imp', left, right)
    return ast


def normalize_conj_list(asts):
    out = []
    seen = set()
    for f in asts:
        sf = simplify_formula_ast(f)
        if sf[0] == 'true':
            continue
        if sf in seen:
            continue
        out.append(sf)
        seen.add(sf)
    if any(f[0] == 'false' for f in out):
        return [('false',)]
    return out


def has_direct_contradiction(asts):
    for i in range(len(asts)):
        for j in range(i + 1, len(asts)):
            if are_complements(asts[i], asts[j]):
                return True
    return False


def strengthen_once(asts):
    asts = normalize_conj_list(asts)
    if asts == [('false',)] or has_direct_contradiction(asts):
        return [('false',)]

    s = set(asts)
    derived = []
    removable = set()

    imps = [f for f in asts if f[0] == 'imp']
    globs = [f for f in asts if f[0] == 'glob']
    glob_imps = [g for g in globs if g[1][0] == 'imp']

    for imp in imps:
        p, q = imp[1], imp[2]
        if p in s:
            derived.append(q)
        if ('not', q) in s:
            derived.append(('not', p))
        if q in s or ('not', p) in s:
            removable.add(imp)

    for i in range(len(imps)):
        p, q = imps[i][1], imps[i][2]
        for j in range(i + 1, len(imps)):
            p2, q2 = imps[j][1], imps[j][2]
            if p == p2 and are_complements(q, q2):
                derived.append(('not', p))
            if q == p2:
                derived.append(('imp', p, q2))
            if q2 == p:
                derived.append(('imp', p2, q))

    for g in glob_imps:
        imp = g[1]
        p, q = imp[1], imp[2]
        gp = ('glob', p)
        gq = ('glob', q)
        gnq = ('glob', ('not', q))
        if gp in s:
            derived.append(gq)
        if gnq in s:
            derived.append(('glob', ('not', p)))
        if gq in s or ('glob', ('not', p)) in s:
            removable.add(g)

    for i in range(len(glob_imps)):
        p, q = glob_imps[i][1][1], glob_imps[i][1][2]
        for j in range(i + 1, len(glob_imps)):
            p2, q2 = glob_imps[j][1][1], glob_imps[j][1][2]
            if p == p2 and are_complements(q, q2):
                derived.append(('glob', ('not', p)))
            if q == p2:
                derived.append(('glob', ('imp', p, q2)))
            if q2 == p:
                derived.append(('glob', ('imp', p2, q)))

    next_asts = [f for f in asts if f not in removable]
    next_asts.extend(derived)
    next_asts = normalize_conj_list(next_asts)
    if next_asts == [('false',)] or has_direct_contradiction(next_asts):
        return [('false',)]
    return next_asts


def strengthen_simplified_asts(asts):
    cur = normalize_conj_list(asts)
    for _ in range(256):
        nxt = strengthen_once(cur)
        if nxt == cur:
            return cur
        cur = nxt
    return cur


def asts_to_ltl_strings(asts, id_to_atom):
    return [ast_to_ltl_string(a, id_to_atom) for a in asts]


def coq_simplify_formulas(formulas):
    list_term, id_to_atom = build_list_term(formulas)

    with tempfile.NamedTemporaryFile('w', suffix='.v', prefix='coqtmp', delete=False) as tf:
        tmp = Path(tf.name)
        tf.write('From Coq Require Import List.\n')
        tf.write('Import ListNotations.\n')
        tf.write('From DSL4FSM Require Import ltl_kernel.\n\n')
        tf.write(f'Definition input_conj : list ltl := {list_term}.\n')
        tf.write('Eval vm_compute in (simplify_conj input_conj).\n')

    try:
        cmd = ['conda', 'run', '-n', COQ_ENV, 'coqc', '-Q', str(COQ_DIR), 'DSL4FSM', str(tmp)]
        p = run(cmd)
        if p.returncode != 0:
            raise RuntimeError(f'coqc failed:\n{p.stdout}\n{p.stderr}')

        simp_list_term = parse_simplified_list(p.stdout)
        simp_asts = decode_list_term_ast(simp_list_term)
        simp_asts = strengthen_simplified_asts(simp_asts)
        simp_formulas = asts_to_ltl_strings(simp_asts, id_to_atom)
        return simp_formulas
    finally:
        try:
            os.remove(tmp)
        except OSError:
            pass


class Handler(BaseHTTPRequestHandler):
    def _send(self, code, payload):
        body = json.dumps(payload).encode('utf-8')
        self.send_response(code)
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('Content-Length', str(len(body)))
        self.send_header('Access-Control-Allow-Origin', '*')
        self.send_header('Access-Control-Allow-Methods', 'POST, OPTIONS')
        self.send_header('Access-Control-Allow-Headers', 'Content-Type')
        self.end_headers()
        self.wfile.write(body)

    def do_OPTIONS(self):
        self._send(200, {'ok': True})

    def do_POST(self):
        if self.path != '/api/coq/simplify':
            self._send(404, {'ok': False, 'error': 'not found'})
            return
        try:
            length = int(self.headers.get('Content-Length', '0'))
            raw = self.rfile.read(length).decode('utf-8')
            data = json.loads(raw or '{}')
            formulas = data.get('formulas', [])
            if not isinstance(formulas, list) or not all(isinstance(x, str) for x in formulas):
                raise ValueError('formulas must be an array of strings')

            simp = coq_simplify_formulas(formulas)
            text = 'true' if not simp else ' &&\n'.join(f'({x})' for x in simp)
            self._send(200, {'ok': True, 'simplified': simp, 'text': text})
        except Exception as e:
            self._send(500, {'ok': False, 'error': str(e)})


def main():
    ensure_kernel_compiled()
    server = HTTPServer((HOST, PORT), Handler)
    print(f'Coq simplify server listening on http://{HOST}:{PORT}')
    server.serve_forever()


if __name__ == '__main__':
    main()
