# Safety DSL for FSM Verification

## 1. Purpose
This project defines a small, implementation-oriented DSL for writing **safety properties** over finite-state transition systems and translating them into a restricted LTL fragment suitable for model checking.

The design target is practical formal verification:
- concise property authoring,
- deterministic DSL-to-LTL mapping,
- direct reduction to reachability/invariant checking.

## 2. System Model
We model the system as a finite labeled transition system:

\[
TS = (S, S_0, \Sigma, \to, L)
\]

- `S`: finite set of states
- `S0 ⊆ S`: initial states
- `Σ`: finite event alphabet
- `→ ⊆ S × Σ × S`: transition relation
- `L: S → 2^AP`: state labeling function

An infinite execution trace is:

\[
\pi = (s_0,\sigma_0)(s_1,\sigma_1)(s_2,\sigma_2)\ldots
\]

with `s0 ∈ S0` and `(si, σi, s(i+1)) ∈ →`.

## 3. DSL Grammar (Strict)
The current DSL supports five property forms:

```bnf
Property ::= Invariant
           | Forbid
           | Require
           | TransitionConstraint
           | Bounded

Invariant ::= "invariant" Formula
Forbid ::= "forbid" Formula
Require ::= "require" Formula "->" Formula
TransitionConstraint ::= "no_transition" State "->" State
Bounded ::= "bounded" Variable "<=" Number
```

Strict syntax rules used by the tool:
- one property per line,
- no `safety` prefix,
- no `keyword:` colon form,
- no trailing semicolon.

## 4. DSL-to-LTL Semantics
Let `⟦·⟧F` map DSL formulas to propositional predicates in LTL state formulas.
Main property translation function:

\[
\llbracket \cdot \rrbracket_P : Property \to LTL
\]

### Invariant
\[
\llbracket invariant\;\phi \rrbracket_P = G\,\llbracket \phi \rrbracket_F
\]

### Forbid
\[
\llbracket forbid\;\phi \rrbracket_P = G\,\neg\llbracket \phi \rrbracket_F
\]

### Require
\[
\llbracket require\;\phi \to \psi \rrbracket_P = G(\llbracket \phi \rrbracket_F \to \llbracket \psi \rrbracket_F)
\]

### TransitionConstraint
\[
\llbracket no\_transition\;S_1 \to S_2 \rrbracket_P = G\big((state=S_1) \to X\neg(state=S_2)\big)
\]

### Bounded
\[
\llbracket bounded\;x \le N \rrbracket_P = G(x \le N)
\]

## 5. Satisfaction
Standard LTL trace semantics:
- `π, i ⊨ p` iff `p ∈ L(si)`
- `π, i ⊨ Xφ` iff `π, i+1 ⊨ φ`
- `π, i ⊨ Gφ` iff `∀j ≥ i, π, j ⊨ φ`

System-level satisfaction:

\[
TS \models P \iff \forall \pi,\; \pi,0 \models \llbracket P \rrbracket_P
\]

## 6. Safety Characterization
All supported properties compile to formulas of the form:
- `G φ`, or
- `G(φ -> X ψ)`

Therefore this DSL is inside the **safety fragment** of LTL.

Consequences:
- violations are detectable by finite prefixes,
- checking can be reduced to bad-state reachability,
- SAT/IC3/k-induction style workflows are applicable.

For each DSL property `P`, there exists a bad-state set `Bad` such that:

\[
TS \models P \iff Reach(TS) \cap Bad = \varnothing
\]

## 7. Expressiveness and Limits
The DSL intentionally excludes liveness operators and full temporal expressiveness.
Not supported directly:
- `F` (eventually),
- `U` (until),
- fairness/recurrence forms (e.g., `GF`),
- branching-time quantifiers.

This is a deliberate trade-off to keep the framework analyzable as finite-state safety verification.

## 8. Representative Property Patterns
Examples expressible in the DSL:

```text
invariant !(grant1 && grant2)
forbid (state == ViolationLost)
require (event == PU) -> (sync == Ahead)
no_transition NeedImmediateForcePush -> ViolationMissedImmediateForcePush
bounded count <= 8
```

## 9. Tooling in This Repository
- `index.html`: unified DSL builder + strict DSL importer + symbol library + symbolic LTL generation + Coq-backed simplification display.
- `tools/coq/ltl_kernel.v`: Coq LTL kernel and proven conjunction simplifier.
- `tools/coq/coq_simplify_server.py`: local HTTP API used by `index.html` to invoke Coq simplification.
- `tools/coq/coq_simplify.sh`: CLI wrapper to simplify a list of LTL terms via Coq.
- `FSM安全性质及写法.pdf`: original source material.
- `FSM安全性质及写法.md`: extracted text version of the source material.

The web tooling stores user-entered strings as typed symbols and generates symbolic DSL/LTL while preserving a symbol-to-string mapping table. Simplification is delegated to the Coq backend (no JavaScript rewrite simplifier in the UI path).

## 10. Suggested Citation Scope (for paper drafting)
A concise formulation for manuscript use:

> We define a domain-specific safety language over finite-state transition systems with compositional semantics into Safety-LTL. The language supports invariants, forbiddance constraints, guarded requirements, explicit transition exclusions, and bounded numeric invariants. Each property is translated into either `G φ` or `G(φ -> X ψ)`, enabling reduction to finite bad-state reachability.

## 11. Human Entry Guide (Reserved DSL + Natural Language Content)
The intended authoring mode is:
- keep DSL keywords fixed (`invariant`, `forbid`, `require`, `no_transition`, `bounded`)
- allow users to type natural-language text inside formula slots

Example:
- `forbid "merge remote history into protected branch"`

Here:
- `forbid` is the reserved DSL keyword
- the quoted text is user intent in natural language
- the tool maps that text to an internal symbol and uses symbols in generated LTL

### 11.1 Input templates
Use these fixed templates:

```text
invariant "<natural-language condition>"
forbid "<natural-language bad condition>"
require "<natural-language precondition>" -> "<natural-language obligation>"
no_transition "<from-state description>" -> "<to-state description>"
bounded "<natural-language variable name>" <= <number>
```

### 11.2 LTL-compatible property set (supported in this DSL)
The following are the compatible property intents to expose clearly in the UI.
They all compile to the supported Safety-LTL fragment (`G φ` or `G(φ -> X ψ)`).

| Human intent | User-entered DSL (natural text) | Recommended strict DSL syntax | LTL shape |
|---|---|---|---|
| Mutual exclusion of grants | `invariant "two different requesters are never granted at the same time"` | `invariant !(grant1 && grant2)` | `G φ` |
| No commit-loss sink reached | `forbid "any state that represents lost commits is reached"` | `forbid (state == ViolationLost)` | `G !φ` |
| Never rewrite published history | `forbid "an operation rewrites commits that are already published"` | `forbid (event == RB_pub)` | `G !φ` |
| No merge in rebase-only policy | `forbid "a merge operation is performed"` | `forbid (event == MG)` | `G !φ` |
| Detached-head implies no push | `require "the repository is in detached-head mode" -> "pushing is not allowed"` | `require (mode == Detached) -> !(event == PU)` | `G(φ -> ψ)` |
| Main branch protected from direct commit | `require "the current branch is main" -> "direct commit is not allowed"` | `require (branch == Main) -> !(event == CO)` | `G(φ -> ψ)` |
| Divergence state forbidden | `forbid "the local and remote histories are diverged"` | `forbid (sync == Diverged)` | `G !φ` |
| Push allowed only when ahead | `require "a push is attempted" -> "the local branch is ahead of remote"` | `require (event == PU) -> (sync == Ahead)` | `G(φ -> ψ)` |
| Rebase failure forbidden under divergence | `forbid "a rebase failure occurs while histories are diverged"` | `forbid ((divergence == Div) && (event == RB_fail))` | `G !φ` |
| Immediate force-push obligation (state encoded) | `no_transition "state where immediate force-push is required" -> "violation state for missing immediate force-push"` | `no_transition NeedImmediateForcePush -> ViolationMissedImmediateForcePush` | `G(s1 -> X !s2)` |
| Force-push requires authorization | `require "a force-push is requested" -> "the actor is authorized"` | `require (event == PUF) -> (auth == Auth)` | `G(φ -> ψ)` |
| Bounded unpublished-commit count | `bounded "number of unpublished commits" <= 8` | `bounded count <= 8` | `G(x <= N)` |
| Force-push allowed only for maintainers | `require "a force-push is requested" -> "the actor has maintainer role"` | `require (event == PUF) -> (role == Maintainer)` | `G(φ -> ψ)` |
| Protected branch blocks normal push | `require "current branch is protected" -> "normal push is not allowed"` | `require (branch == Protected) -> !(event == PU)` | `G(φ -> ψ)` |
| Protected branch blocks force-push | `forbid "force-push is attempted on a protected branch"` | `forbid ((branch == Protected) && (event == PUF))` | `G !φ` |
| Detached mode blocks commit | `require "repository is detached" -> "commit is not allowed"` | `require (mode == Detached) -> !(event == CO)` | `G(φ -> ψ)` |
| Rebase only when needed | `require "a rebase is requested" -> "branch is not already synchronized"` | `require (event == RB) -> (sync != Clean)` | `G(φ -> ψ)` |
| Push only when network is available | `require "a push is attempted" -> "network is online"` | `require (event == PU) -> (network == Online)` | `G(φ -> ψ)` |
| Retry budget bound | `bounded "number of retries" <= 3` | `bounded retry_count <= 3` | `G(x <= N)` |
| Queue depth bound | `bounded "pending queue depth" <= 64` | `bounded queue_depth <= 64` | `G(x <= N)` |

### 11.3 Not included in this DSL subset
Drop these from the user-facing preset list unless they are first encoded into FSM states:
- properties requiring `U` (Until), such as "after rejection, block push until rebase"
- eventuality/liveness forms requiring `F` (Eventually)
- multi-step obligations not reducible to `invariant/forbid/require/no_transition/bounded`

### 11.4 Interpretation model
- User text is treated as a domain phrase, not as strict logic syntax.
- The system stores phrase-to-symbol mappings (for reuse and drag/drop).
- Generated DSL/LTL uses symbols; mapping is shown to users for traceability.
