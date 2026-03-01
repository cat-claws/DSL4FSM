#!/usr/bin/env python3
import json
import os
import re
import subprocess
import tempfile
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / 'tools'
KERNEL = TOOLS / 'ltl_kernel.v'

COQ_ENV = 'rh1'
HOST = '127.0.0.1'
PORT = int(os.environ.get('COQ_SIMPLIFY_PORT', '8081'))


def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True, check=False)


def ensure_kernel_compiled():
    cmd = [
        'conda', 'run', '-n', COQ_ENV,
        'coqc', '-Q', str(TOOLS), 'DSL4FSM', str(KERNEL)
    ]
    p = run(cmd)
    if p.returncode != 0:
        raise RuntimeError(f'Failed to compile ltl_kernel.v:\n{p.stdout}\n{p.stderr}')


def build_list_term(formulas):
    formula_to_id = {}
    id_to_formula = {}
    next_id = 1
    terms = []

    for f in formulas:
        f = f.strip()
        if f == 'G(true)':
            terms.append('LTrue')
        elif f == 'G(false)':
            terms.append('LFalse')
        else:
            if f not in formula_to_id:
                formula_to_id[f] = next_id
                id_to_formula[next_id] = f
                next_id += 1
            terms.append(f"Atom {formula_to_id[f]}")

    return '[' + '; '.join(terms) + ']', id_to_formula


def parse_simplified_list(coqc_output):
    m = re.search(r"=\s*(\[[\s\S]*?\])\s*\n\s*: list ltl", coqc_output)
    if not m:
        raise RuntimeError(f'Unable to parse Coq output:\n{coqc_output}')
    return m.group(1).strip()


def decode_list_term(list_term, id_to_formula):
    if list_term == '[]':
        return []
    if not (list_term.startswith('[') and list_term.endswith(']')):
        raise RuntimeError(f'Unexpected list term: {list_term}')

    inner = list_term[1:-1].strip()
    if not inner:
        return []

    items = [x.strip() for x in inner.split(';')]
    out = []
    for it in items:
        if it == 'LTrue':
            out.append('G(true)')
        elif it == 'LFalse':
            out.append('G(false)')
        else:
            m = re.fullmatch(r'Atom\s+(\d+)', it)
            if not m:
                raise RuntimeError(f'Unsupported simplified item from Coq: {it}')
            idx = int(m.group(1))
            if idx not in id_to_formula:
                raise RuntimeError(f'Unknown atom id from Coq: {idx}')
            out.append(id_to_formula[idx])
    return out


def coq_simplify_formulas(formulas):
    list_term, id_to_formula = build_list_term(formulas)

    with tempfile.NamedTemporaryFile('w', suffix='.v', prefix='coqtmp', delete=False) as tf:
        tmp = Path(tf.name)
        tf.write('From Coq Require Import List.\n')
        tf.write('Import ListNotations.\n')
        tf.write('From DSL4FSM Require Import ltl_kernel.\n\n')
        tf.write(f'Definition input_conj : list ltl := {list_term}.\n')
        tf.write('Eval vm_compute in (simplify_conj input_conj).\n')

    try:
        cmd = [
            'conda', 'run', '-n', COQ_ENV,
            'coqc', '-Q', str(TOOLS), 'DSL4FSM', str(tmp)
        ]
        p = run(cmd)
        if p.returncode != 0:
            raise RuntimeError(f'coqc failed:\n{p.stdout}\n{p.stderr}')

        simp_list_term = parse_simplified_list(p.stdout)
        simp_formulas = decode_list_term(simp_list_term, id_to_formula)
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
            text = 'G(true)' if not simp else ' &&\n'.join(f'({x})' for x in simp)
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
