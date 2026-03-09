# Stepwise AP -> Formula -> Property Builder

## Purpose
This project now uses a stepwise authoring pipeline for pure LTL safety properties:
1. Build and manage reusable APs.
2. Build reusable formulas from APs/formulas.
3. Build properties from formulas.
4. Emit conjunction LTL and conjunction AST JSON.

Conceptually:
- AP is a formula (atomic formula).
- Property is also a formula (temporal formula).

## Authoring Stages

### 1) AP Library
- APs are auto-collected while users build formulas (typed AP text or dragged AP usage).
- AP chips are reusable and draggable.
- AP chips can be dragged between `State APs` and `Transition APs` buckets.
- AP type is global per AP text.

### 2) Formula Builder + Formula Pool
Formula templates are:
- `AP`
- `not Formula`
- `Formula and Formula`
- `Formula or Formula`
- `Formula -> Formula`

Rules:
- AP slots accept AP text (typed) or AP chip (dragged).
- Formula slots accept formula chips, AP chips, formula ids (`F1`), or typed AP text.
- Clicking `Add Formula` stores a reusable formula in Formula Pool.

### 3) Property Builder + Property Pool
Property templates are:
- `always Formula`
- `always Formula -> next Formula`

Rules:
- Property creation is explicit (`Add Property` button).
- Property templates accept formula chips, AP chips, formula ids (`F1`), or typed AP text.
- Added properties are stored in Property Pool and can be removed.

## Grammar Enforced

```bnf
Formula ::= Atom
          | "not" Formula
          | Formula "and" Formula
          | Formula "or" Formula
          | Formula "->" Formula

Property ::= "always" Formula
           | "always" Formula "->" "next" Formula
```

`Atom` comes from AP library entries.

## AP Semantics
Internal AP model:
- `state`: proposition text is emitted as-is.
- `transition`: proposition text is emitted with suffix `is performed`.

Example:
- AP text `force push`
- as state -> `"force push"`
- as transition -> `"force push is performed"`

## Internal Data Model
- `apStore: Map<apId, { id, text, type }>`
- `formulaStore: Map<formulaId, { id, ast }>`
- `propertyStore: Array<{ id, ast }>`

Formula AST nodes:
- `{ type: 'ap_ref', apId }`
- `{ type: 'formula_ref', formulaId }` (internal composition)
- `{ type: 'not', operand }`
- `{ type: 'and', left, right }`
- `{ type: 'or', left, right }`
- `{ type: 'implies', left, right }`

Property AST nodes:
- `{ type: 'globally', operand: FormulaRefOrFormula }`
- `{ type: 'globally', operand: { type: 'implies', left: FormulaRefOrFormula, right: { type: 'next', operand: FormulaRefOrFormula } } }`

Emission AST (resolved output) uses LTL nodes with concrete AP names:
- `globally`, `next`, `not`, `and`, `or`, `implies`, `ap`
- Top-level conjunction:
  - single property: resolved property AST
  - multiple properties: `{ "type": "and", "args": [ ... ] }`

## Deletion Safety
- AP deletion is blocked if referenced by any formula/property.
- Formula deletion is blocked if referenced by any formula/property.
- Property deletion is always allowed.

## File
- Main UI and logic: `index.html`
