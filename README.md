# Paper 7: Mixed Prime-Power Fourier Masks and Quantitative Odd Codimension-Two Spectral Gaps

## Files
- `main.tex` — Submission-ready `amsart` LaTeX manuscript (direct sequel to [orthogonal-fourier-masks](https://github.com/AgentSlop-Si/orthogonal-fourier-masks)).
- `references.bib` — Clean BibTeX bibliography.
- `verify_mixed_prime_power.py` — Standalone Python 3 (stdlib only) verifier checking exact weighted character-filtration descent across prime powers (including the connected `(8,4)` mask, its unequal-exponent children, its exact $\mathbb{Q}[\zeta_8]$ inverse-row witness, weighted repeated-label controls, and rectangular/switch negative controls), short-overlap $q$-character erasure at mixed prime-power orders $N=p^a q$ (including shifted-label nonempty cross-$q$ overlaps, $d=q$ boundary failures, and exhaustive short-subset erasure at $N=12,20$), exhaustive enumeration of all $27$ ($N=3$) and $100{,}000$ ($N=5$) ordered two-entry-per-column patterns for the odd codimension-two obstruction, exact cyclotomic verification of the unrestricted stability identities at $N=3,5,7$ with padded supports, and numerical verification of the uniform lower bound $(9-4\sqrt{3})/N$ across Fourier and flat-unitary targets.
- `MixedPrimePowerFourierMasks.lean` — Zero-dependency Lean 4 formal verifier (core `Init` only, verified in Lean 4.36.0 with zero `sorry`, zero custom axioms, and zero `native_decide`) machine-checking the weighted-descent exponent congruences and norm scaling, the complete exact $\mathbb{Z}[\zeta_8]$ Gram/connectivity/descent verification of the connected `(8,4)` mask, the CRT phase factorization and omitted-fiber zero-erasure lemma, exact $\mathbb{Z}[\zeta_{12}]$ verification of a shifted-label $(N,d)=(12,2)$ mask and the $(12,3)$ boundary guard failure, symbolic proofs of the odd-$N$ disjoint-pair triple-collision bound, the rank-2 Welch trace-square bound, the exact per-row stability identity, the exact $\mathbb{Z}[\sqrt{3}]$ constant identities ($2g^2+2g=1$, $9-4\sqrt{3}>2$, norm ratio $>1.01779$, $(9-4\sqrt{3})/3 < 3/4$), and exhaustive kernel verification of all $27$ two-entry-per-column patterns at $N=3$.

## How to Compile PDF
1. Upload `main.tex` and `references.bib` to Overleaf (or compile locally with `latexmk -pdf main.tex`).

## Suggested Submission Metadata
- **arXiv primary / secondary:** `math.CO` (Combinatorics) / `math.NT` (Number Theory), `math.FA` (Functional Analysis)
- **MSC 2020:** Primary `05B20`, `15B10`; Secondary `11R18`, `42A99`, `15A60`
- **Target journals (zero-fee):** *Linear Algebra and its Applications*, *Discrete Mathematics*, *Electronic Journal of Linear Algebra*.

## Verify Computations and Lean Proofs
```bash
python3 verify_mixed_prime_power.py
lean MixedPrimePowerFourierMasks.lean
```
