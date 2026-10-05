# Corollary 4.10: explicit constant renaming

For a fixed admissible numerical constant A, the paper sets t_d = A d^(−2/5). Its printed chain is

`Var(Z) ≥ c/t_d ≥ c d^(2/5)`.

For A > 1, c > 0 and d > 0, the second comparison is false:

`c/t_d = (c/A) d^(2/5) < c d^(2/5)`.

The explicit correction used in this formalization names the two constants separately:

`Var(Z) ≥ c₁/t_d ≥ c₂ d^(2/5)`, with `c₂ = c₁/A`.

The proof supports a positive numerical c₁ independent of dimension. For each fixed admissible A, c₂ and the dimension threshold may depend on A. The formal corrected proposition retains every such fixed A, not just one selected value.

## Formal separation

- `GaussianTilt.Reference.Literal410` is the literal printed chain
- `GaussianTilt.Reference.Corrected410` is the explicit constant-renaming version
- `GaussianTilt.Reference.Corollary4_10` still denotes `Literal410`
- [`Corollary410SourceAudit.lean`](../GaussianTilt/Corollary410SourceAudit.lean) proves `not_Literal410`
- [`Section4StatementBridges.lean`](../GaussianTilt/Section4StatementBridges.lean) proves `corrected4_10`
- [`NumberedStatements.lean`](../GaussianTilt/Reference/NumberedStatements.lean) keeps the literal and corrected 27-result catalogs distinct

The main lower theorem uses the valid final dimension-scale bound, with constant c₁/A, and is unaffected. The upper theorem and sharp exponent are unchanged.

## Audited source

Pinned [arXiv v1 source](https://arxiv.org/src/2609.08930v1), `main.tex` lines 2419–2447; the main-lower application is at lines 2450–2465. The proof explicitly says “after adjusting the universal constant”.

`main.tex` SHA-256: `47417910f9b553a0836a463cb67bcd5b11fcd78f12b544963c5cac821b8395ff`.

Original download hashes are recorded in [`paper/PROVENANCE.json`](../paper/PROVENANCE.json). Proving the corrected catalog does not prove the literal catalog or imply approval by the paper's authors.
