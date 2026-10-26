# Lean formalization

Lean 4 + Mathlib statement and proof of the main theorem. Toolchain `leanprover/lean4:v4.33.1`,
Mathlib at commit `0df444a360eaa60ab8c11dca51a86af692955474`.

| File | Content |
|---|---|
| `LeanTargetTheorem/MainTheorem.lean` | the Fischer pairing, `Schmid`, `fischerKernel`, the hypotheses `Berezin` (B) and `FarautKoranyi` (FK), and `main_theorem` |
| `LeanTargetTheorem/BoxProof.lean` | finitely many diagrams of each size; `box_formula_of_kernels`, the recurrence form of the Answer |
| `LeanTargetTheorem/Basic.lean` | linearity of $Q_2$; derivatives of $\gamma$ with respect to $\bar\eta$ |
| `LeanTargetTheorem/Defs.lean` | polynomials in $\eta,\bar\eta$, `γ`, `Q₂`, the Hara–Sako recurrence `HaraSako`, Young diagrams (`size`, `content`, `eig`) |

```bash
lake exe cache get
lake build
```
