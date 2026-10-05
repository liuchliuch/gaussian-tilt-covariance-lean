# Independent numbered statement map

The 27 active results of the pinned source are specified independently. This table records specification coverage, not mathematical proof closure. Every target lives in `GaussianTilt.Reference`; no target imports implementation modules. The commented annealing results and nonexistent appendix are excluded.

| No. | Target | Source line | Preserved clauses |
|---|---|---:|---|
| 1.1 | `Theorem1_1` | 282 | Shared universal c/C; upper path, lower bodies and actual Q_n asymptotics |
| 2.1 | `Lemma2_1` | 1201 | All integrable observables; mean/matrix/log derivatives; all-real Renyi times |
| 2.2 | `Theorem2_2` | 1303 | Full isotropic logconcave law; gradient-energy equality |
| 2.3 | `Theorem2_3` | 1329 | Universal tail constant, all t≥1 |
| 2.4 | `Theorem2_4` | 1341 | Every orthogonal projection; actual rank; all p≥2 |
| 2.5 | `Theorem2_5` | 1445 | Proper l.s.c. extended potential; positive finite mass; Loewner and directional bounds |
| 2.6 | `Lemma2_6` | 1503 | Noncentered/nondegenerate law; both PSD-square-root and BM trace forms |
| 3.1 | `Theorem3_1` | 1556 | Universal covariance upper bound |
| 3.2 | `Lemma3_2` | 1596 | Actual log-HS differentiability and EReal upper-right Dini bound |
| 3.3 | `Corollary3_3` | 1659 | Both integrated estimates on every 0≤a<b |
| 3.4 | `Lemma3_4` | 1681 | Exact conjugate-order equality and entropy bound |
| 3.5 | `Lemma3_5` | 1722 | Trace equals projected expectation, plus the numerical bound |
| 3.6 | `Corollary3_6` | 1745 | Sorted eigenvalues and both operator/HS consequences |
| 3.7 | `Lemma3_7` | 1788 | Both stability inequalities throughout the whole closed interval |
| 3.8 | `Lemma3_8` | 1828 | Three universal constants; all endpoint conditions and both outputs |
| 3.9 | `Lemma3_9` | 1887 | Constants before sufficiently large dimension and whole time window |
| 3.10 | `Proposition3_10` | 1954 | Covariance≤uncentered moment≤small-time profile |
| 4.1 | `Theorem4_1` | 2057 | Unconditional isotropic bodies in every sufficiently large n |
| 4.2 | `Lemma4_2` | 2096 | Explicit raw geometry/sign symmetry/centering/positive block covariance |
| 4.3 | `Theorem4_3` | 2140 | Arbitrary IID laws and uniform relative error with literal 1−Phi denominator |
| 4.4 | `Lemma4_4` | 2157 | Uniform s-window; constants may depend only on fixed s0 |
| 4.5 | `Lemma4_5` | 2196 | Actual cube slice tail, every positive d and s≥0 |
| 4.6 | `Lemma4_6` | 2215 | Both moment orders, common constants and threshold |
| 4.7 | `Lemma4_7` | 2269 | Both covariance scales, exact integral ratio and exact scale identity |
| 4.8 | `Corollary4_8` | 2329 | Actual diagonal image and inverse coordinate formulas |
| 4.9 | `Lemma4_9` | 2381 | Every fixed admissible A; threshold after A; literal full-window infimum |
| 4.10 | `Corollary4_10` | 2421 | Literal410 retained; Corrected410 is separate, arbitrary fixed A retained |

## Import and proof separation

- `Reference/PaperStatements.lean`: original independent measure/body/main observables
- `Reference/NumberedDefinitions.lean`: literal uncentered moments, HS norm, entropy and EReal Dini derivative
- `Reference/Section2Statements.lean`, `Section3Statements.lean`: pure targets
- `Reference/Section4Definitions.lean`, `Section4Statements.lean`: independently specified raw construction and lower targets
- `Reference/NumberedStatements.lean`: Theorem 1.1 and the exact 27-result index
- `Section2StatementBridges.lean`, `Section3StatementBridges.lean`, `Section4DefinitionBridges.lean`, `Section4StatementBridges.lean`: separate implementation-side comparison/proof work; these are not imported by any target

The positive-dimensional convention for Section 3 derivative/log statements is explicit. Every asymptotic threshold follows precisely the parameters on which it may depend. Raw covariance scales retain their actual mean corrections, so centering is a proved bridge rather than a definition. The spectral statements use the genuine sorted symmetric spectral API.

## Corollary 4.10

`NumberedTarget` uses the printed `Literal410`. `NumberedTargetWith410Erratum` changes only this target to `Corrected410`. The literal same-constant chain is independently refuted in `Corollary410SourceAudit.lean`; the proposed minimal correction and its unchanged main-lower consequence are documented in `COROLLARY410_ERRATUM.md`. No acceptance or numbered closure follows merely from the corrected proposition being defined.

Machine-readable 27-entry map: `evidence/numbered-statement-map.json`. Independent import closure: `evidence/reference-import-closure.json`.

## Completed proof and verification entrypoints

`GaussianTilt/NumberedProofs.lean` proves each of the 26 literal targets other than 4.10 and every target of the separately corrected catalog, without extra analytic premises. It also refutes the literal complete catalog through `not_Literal410`.

The literal and corrected catalogs remain distinct. Reproduction and Comparator checks are described in [VERIFICATION.md](VERIFICATION.md).
