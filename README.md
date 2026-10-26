# Star products on locally symmetric Kähler manifolds in every dimension

This repository is a study note on the following theorem and answer, with a Lean proof formalization.

### Theorem

> **Problem.** Let $`M`$ be a Kähler manifold of complex dimension $`n`$ with $`\nabla R=0`$, and let $`\star`$ be its standard star product with separation of variables,
>
> ```math
> f\star g=fg+\hbar\,C_1(f,g)+\hbar^2\,C_2(f,g)+\cdots .
> ```
>
> Group the terms by the number $`m`$ of derivatives on $`f`$ and on $`g`$ instead of by the power of $`\hbar`$:
>
> ```math
> f\star g=\sum_{m\ge0}T_{k_1\cdots k_m\bar l_1\cdots\bar l_m}\,(D^{k_1}\cdots D^{k_m}f)\,(\bar D^{l_1}\cdots\bar D^{l_m}g),\qquad D^k=g^{\bar lk}\partial_{\bar l},\quad \bar D^l=g^{\bar lk}\partial_k ,
> ```
>
> where each coefficient $`T_{k_1\cdots k_m\bar l_1\cdots\bar l_m}`$ is a power series in $`\hbar`$. Collect them in polynomials in commuting formal variables $`\eta^1,\dots,\eta^n,\bar\eta^1,\dots,\bar\eta^n`$:
>
> ```math
> P_m=T_{k_1\cdots k_m\bar l_1\cdots\bar l_m}\,\eta^{k_1}\cdots\eta^{k_m}\bar\eta^{l_1}\cdots\bar\eta^{l_m}.
> ```
>
> **Find $`P_m`$ in closed form, for every $`n`$ and every $`m`$.**

> **Answer.** For an irreducible factor of rank $`r`$, multiplicity $`a`$ and curvature scale $`\kappa`$,
>
> ```math
> P_m=\sum_{|\mathbf m|=m}\frac{\hbar^m\,K_{\mathbf m}}{\prod_{(i,j)\in\mathbf m}\bigl(1-\hbar\kappa\,(j-\tfrac{(i-1)a}{2})\bigr)},
> ```
>
> where $`\mathbf m`$ runs over Young diagrams with at most $`r`$ rows (row $`i`$ from $`1`$, column $`j`$ from $`0`$) and $`K_{\mathbf m}`$ is the Fischer kernel of the Schmid component $`\mathcal P_{\mathbf m}`$. For a product of factors, $`\sum_mP_m`$ is the product.

| Dimension | $`P_m`$ | Source |
|---|---|---|
| 1 | $`P_m=\prod_{k=1}^m\frac{2\hbar}{2k+\hbar k(k-1)R}\,\gamma^m`$ | Hara–Sako 2017 |
| 2 | $`P_m=\sum_{i,j=1}^{m+1}(T_m)_{ij}\,(\eta^1)^{m-i+1}(\eta^2)^{i-1}(\bar\eta^1)^{m-j+1}(\bar\eta^2)^{j-1}`$, with $`T_m=\hbar^m\sum_{p_1,\dots,p_m}F^{p_m}_m\cdots F^{p_1}_1\,T_0\,(B^{p_1}_1X_1^{-1})\cdots(B^{p_m}_mX_m^{-1})`$ | Okuda–Sako 2023 |
| all | $`P_m=\sum_{\lvert\mathbf m\rvert=m}\frac{\hbar^m\,K_{\mathbf m}}{\prod_{(i,j)\in\mathbf m}(1-\hbar\kappa(j-\frac{(i-1)a}{2}))}`$ | This repository, from Berezin 1975 and Faraut–Korányi 1990 |

In dimension 2, $`X_k`$ is a pentadiagonal matrix linear in the curvature, and $`F^p_k`$, $`B^p_k`$ are
combinations of the identity and the shift matrix whose coefficients factorize the metric (Appendix A).

## 1. Lean Target Theorem

The Lean statement below is the Answer for one irreducible factor, with Berezin's theorem (B) and
the Faraut–Korányi formula (FK) as hypotheses (see Section 2). It is proved in
[`lean/LeanTargetTheorem/MainTheorem.lean`](lean/LeanTargetTheorem/MainTheorem.lean), with no `sorry`.

```lean
/-- A Schmid decomposition: Fischer-orthogonal projections onto components `𝒫_μ`. -/
structure Schmid (F : Type*) [Field F] (n : ℕ) where
  proj : YoungDiagram → Hol F n →ₗ[F] Hol F n
  proj_idem : ∀ μ p, proj μ (proj μ p) = proj μ p
  proj_orth : ∀ μ μ' p, μ ≠ μ' → proj μ (proj μ' p) = 0
  proj_selfAdjoint : ∀ μ p q, fischer (proj μ p) q = fischer p (proj μ q)
  proj_sum : ∀ (d : ℕ) (p : Hol F n), p.IsHomogeneous d →
    ∑ᶠ (μ : YoungDiagram) (_ : size μ = d), proj μ p = p

/-- The Fischer kernel `K_μ = Σ_{α, β} ⟨(zᵅ)_μ, (zᵝ)_μ⟩_F / (α! β!) · ηᵝ η̄ᵅ`. -/
def fischerKernel (S : Schmid F n) (μ : YoungDiagram) : Poly F n :=
  ∑ α ∈ multiIdx n μ.cells.card, ∑ β ∈ multiIdx n μ.cells.card,
    (fischer (S.proj μ (zpow α)) (S.proj μ (zpow β)) / (mfact α * mfact β)) • etaMono β α

/-- (B) The coefficients of `P m` are weighted Bergman moments. -/
def Berezin (κ : F) (bergman : Hol F n → Hol F n → F) (P : ℕ → Poly F n) : Prop :=
  ∀ m, P m = ∑ α ∈ multiIdx n m, ∑ β ∈ multiIdx n m,
    ((-κ)⁻¹ ^ m * bergman (zpow α) (zpow β) / (mfact α * mfact β)) • etaMono β α

/-- (FK) The weighted Bergman pairing is the Fischer pairing divided by `(ν)_μ`. -/
def FarautKoranyi (S : Schmid F n) (a : ℕ) (ν : F) (bergman : Hol F n → Hol F n → F) : Prop :=
  ∀ (d : ℕ) (p q : Hol F n), p.IsHomogeneous d → q.IsHomogeneous d →
    bergman p q = ∑ᶠ (μ : YoungDiagram) (_ : size μ = d),
      fischer (S.proj μ p) (S.proj μ q) / poch ν a μ

theorem main_theorem [CharZero F] (κ ℏ : F) (a : ℕ) (hκ : κ ≠ 0) (hℏ : ℏ ≠ 0)
    (S : Schmid F n) (bergman : Hol F n → Hol F n → F)
    (P : ℕ → Poly F n) (hB : Berezin κ bergman P)
    (hFK : FarautKoranyi S a (-1 / (ℏ * κ)) bergman) (m : ℕ) :
    P m = ∑ᶠ (μ : YoungDiagram) (_ : size μ = m),
      (ℏ ^ m / ∏ c ∈ μ.cells, (1 - ℏ * κ * content a c)) • fischerKernel S μ
```

| Lean | Mathematics |
|---|---|
| `P : ℕ → Poly F n` | the polynomials $`P_m(\eta,\bar\eta)`$ of the Problem |
| `∑ᶠ (μ) (_ : size μ = m), (ℏ ^ m / ∏ c ∈ μ.cells, (1 - ℏ * κ * content a c)) • fischerKernel S μ` | the Answer $`\sum_{\lvert\mathbf m\rvert=m}\hbar^mK_{\mathbf m}\big/\prod_{(i,j)\in\mathbf m}\bigl(1-\hbar\kappa(j-\tfrac{(i-1)a}2)\bigr)`$ |
| `S : Schmid F n`, `S.proj μ p` | the Schmid decomposition $`\mathcal P=\bigoplus_{\mathbf m}\mathcal P_{\mathbf m}`$, and the component $`p_{\mathbf m}`$ |
| `fischerKernel S μ` | the Fischer kernel $`K_{\mathbf m}`$ of $`\mathcal P_{\mathbf m}`$ |
| `fischer p q` | the Fischer pairing $`\langle p,q\rangle_F=\sum_\alpha p_\alpha q_\alpha\,\alpha!`$ |
| `bergman p q` | the weighted Bergman pairing $`\langle p,q\rangle_\nu=\int_Dp\,\bar q\,d\mu_\nu`$ |
| `hB : Berezin κ bergman P` | (B): $`P_m=\sum_{\lvert\alpha\rvert=\lvert\beta\rvert=m}(-\kappa)^{-m}\langle z^\alpha,z^\beta\rangle_\nu\,\eta^\beta\bar\eta^\alpha/(\alpha!\,\beta!)`$ |
| `hFK : FarautKoranyi S a (-1 / (ℏ * κ)) bergman` | (FK) at $`\nu=-1/(\hbar\kappa)`$: $`\langle p,q\rangle_\nu=\sum_{\lvert\mathbf m\rvert=d}\langle p_{\mathbf m},q_{\mathbf m}\rangle_F/(\nu)_{\mathbf m}`$ for $`p,q`$ of degree $`d`$ |
| `poch ν a μ` | $`(\nu)_{\mathbf m}=\prod_{(i,j)\in\mathbf m}\bigl(\nu+j-\tfrac{(i-1)a}2\bigr)`$ |
| `content a c` | the content $`j-\tfrac{(i-1)a}2`$ of the box $`(i,j)`$ (Lean counts rows from $`0`$) |
| `Poly F n`, `Hol F n` | polynomials in $`\eta,\bar\eta`$, and holomorphic polynomials in $`z`$, over a field $`F`$ of characteristic $`0`$ |

The rank $`r`$ does not appear: the components $`\mathcal P_{\mathbf m}`$ with more than $`r`$ rows are $`0`$.

## 2. Mathematical explanation of the Lean proof (AI generated)

We take two classical theorems as known and derive the main theorem from them by a chain of
equalities. We compute on the noncompact side ($`\kappa=-1`$) and pass to general $`\kappa`$ at the end.

**Known.**

- **(B) Berezin.** On a bounded symmetric domain $`D`$, Berezin's star product with weight $`\nu`$ is
  the standard star product with $`\hbar=1/\nu`$ (Karabegov 1996), and at the origin it is an integral.
- **(FK) Faraut–Korányi.** Polynomials split into Schmid components, $`\mathcal P=\bigoplus_{\mathbf m}\mathcal P_{\mathbf m}`$.
  For $`p\in\mathcal P_{\mathbf m}`$ and $`q\in\mathcal P_{\mathbf n}`$ the weighted Bergman integral is the
  Fischer inner product divided by a product over the boxes of $`\mathbf m`$.

```math
\text{(B)}\quad (f\star g)(0)=\int_D f(0,\bar w)\,g(w,0)\,d\mu_\nu(w)
```

```math
\text{(FK)}\quad \int_D p\,\bar q\,d\mu_\nu=\delta_{\mathbf m\mathbf n}\,\frac{\langle p,q\rangle_F}{(\nu)_{\mathbf m}},\qquad (\nu)_{\mathbf m}=\prod_{(i,l)\in\mathbf m}\bigl(\nu+c_{il}\bigr),\quad c_{il}=l-(i-1)\tfrac a2
```

**Notation.** $`\langle w^\alpha,w^\beta\rangle_F=\alpha!\,\delta_{\alpha\beta}`$ is the Fischer inner product,
$`K_{\mathbf m}(z,\bar w)=\sum_{\alpha,\beta}k^{\mathbf m}_{\alpha\beta}z^\alpha\bar w^\beta`$ is the Fischer reproducing kernel of
$`\mathcal P_{\mathbf m}`$, and $`p_{\mathbf m}`$ is the $`\mathcal P_{\mathbf m}`$-component of $`p`$. At the origin the metric is the
identity, so $`D^k=\partial_{\bar k}`$ and $`\bar D^l=\partial_l`$.

**To show.**

```math
\sum_mP_m(\eta,\bar\eta)=\sum_{\mathbf m}\frac{\hbar^{|\mathbf m|}\,K_{\mathbf m}(\eta,\bar\eta)}{\prod_{(i,l)\in\mathbf m}\bigl(1-\hbar\kappa\,c_{il}\bigr)}\qquad(\kappa=-1).
```

**Step 1 (Taylor expansion in (B)).** Expand $`g(w,0)=\sum_\alpha(\partial^\alpha g)(0)\,w^\alpha/\alpha!`$ and
$`f(0,\bar w)=\sum_\beta(\bar\partial^\beta f)(0)\,\bar w^\beta/\beta!`$. Then

```math
(f\star g)(0)=\sum_{\alpha,\beta}\frac{(\bar\partial^\beta f)(0)\,(\partial^\alpha g)(0)}{\alpha!\,\beta!}\int_D w^\alpha\,\overline{w^\beta}\,d\mu_\nu .
```

**Step 2 (the monomial integrals by (FK)).** Split $`w^\alpha=\sum_{\mathbf m}(w^\alpha)_{\mathbf m}`$. By (FK) only the
diagonal terms survive, and each is divided by $`(\nu)_{\mathbf m}`$:

```math
\int_D w^\alpha\,\overline{w^\beta}\,d\mu_\nu=\sum_{\mathbf m,\mathbf n}\int_D(w^\alpha)_{\mathbf m}\,\overline{(w^\beta)_{\mathbf n}}\,d\mu_\nu=\sum_{\mathbf m}\frac{\langle(w^\alpha)_{\mathbf m},(w^\beta)_{\mathbf m}\rangle_F}{(\nu)_{\mathbf m}} .
```

**Step 3 (component inner products through the kernel).** Take a Fischer-orthonormal basis
$`\varphi_i=\sum_\alpha\varphi_{i\alpha}w^\alpha`$ of $`\mathcal P_{\mathbf m}`$. Then $`k^{\mathbf m}_{\alpha\beta}=\sum_i\varphi_{i\alpha}\overline{\varphi_{i\beta}}`$
and $`\langle w^\alpha,\varphi_i\rangle_F=\alpha!\,\overline{\varphi_{i\alpha}}`$, so

```math
\langle(w^\alpha)_{\mathbf m},(w^\beta)_{\mathbf m}\rangle_F=\sum_i\langle w^\alpha,\varphi_i\rangle_F\,\overline{\langle w^\beta,\varphi_i\rangle_F}=\alpha!\,\beta!\;k^{\mathbf m}_{\beta\alpha} .
```

**Step 4 (combine; the factorials cancel).**

```math
(f\star g)(0)=\sum_{\mathbf m}\frac1{(\nu)_{\mathbf m}}\sum_{\alpha,\beta}k^{\mathbf m}_{\beta\alpha}\,(\bar\partial^\beta f)(0)\,(\partial^\alpha g)(0)=\sum_{\mathbf m}\frac{K_{\mathbf m}(\bar\partial f,\partial g)(0)}{(\nu)_{\mathbf m}},
```

where $`K_{\mathbf m}(\bar\partial f,\partial g)`$ means: in $`K_{\mathbf m}(\eta,\bar\eta)=\sum k^{\mathbf m}_{\beta\alpha}\eta^\beta\bar\eta^\alpha`$ replace
$`\eta^\beta`$ by $`\bar\partial^\beta`$ acting on $`f`$ and $`\bar\eta^\alpha`$ by $`\partial^\alpha`$ acting on $`g`$.

**Step 5 (read off the coefficients).** At the origin $`f\star g=\sum T\,(\bar\partial\cdots f)(\partial\cdots g)`$, so the
generating polynomial is

```math
\sum_mP_m(\eta,\bar\eta)=\sum_{\mathbf m}\frac{K_{\mathbf m}(\eta,\bar\eta)}{(\nu)_{\mathbf m}} .
```

**Step 6 ($`\nu=1/\hbar`$, box by box).** Since $`\nu+c=(1+\hbar c)/\hbar`$ and $`\mathbf m`$ has $`|\mathbf m|`$ boxes,

```math
\frac1{(\nu)_{\mathbf m}}=\prod_{(i,l)\in\mathbf m}\frac{\hbar}{1+\hbar c_{il}}=\frac{\hbar^{|\mathbf m|}}{\prod_{(i,l)\in\mathbf m}(1+\hbar c_{il})} .
```

Substituting into Step 5 gives the formula to show, with $`1+\hbar c=1-\hbar\kappa c`$ at $`\kappa=-1`$. $`\square`$

**Step 7 (general $`\kappa`$).** Scaling the potential by $`\lambda`$ sends $`\hbar\mapsto\hbar/\lambda`$ and $`\kappa\mapsto\kappa/\lambda`$, and
the denominators depend only on $`\hbar\kappa`$; this gives every $`\kappa\lt0`$. For $`\kappa\gt0`$: the $`P_m`$ are determined by the
recurrence $`(m-\hbar Q_2)P_m=\hbar\gamma P_{m-1}`$ with $`Q_2`$ proportional to $`\kappa`$, so they are rational functions of
$`\hbar\kappa`$; they agree with the formula for infinitely many values of $`\kappa\lt0`$, hence identically.

In Lean, `main_theorem` works directly at general $`\kappa`$. It takes (B) in the form of Steps 1 and 5
combined, rescaled as in Step 7: the coefficients of $`P_m`$ are
$`(-\kappa)^{-m}\langle z^\alpha,z^\beta\rangle_\nu/(\alpha!\,\beta!)`$ with $`\nu=-1/(\hbar\kappa)`$ (at $`\kappa=-1`$ this is $`\nu=1/\hbar`$).
It defines $`K_{\mathbf m}`$ by the coefficients of Step 3, and carries out Steps 2, 4 and 6, with (B) and
(FK) as hypotheses. The proof has no `sorry` and uses only the standard axioms.

## 3. Verification

[`lean/`](lean/) contains the statement `main_theorem` and its proof, with no `sorry`; it depends
only on `propext`, `Classical.choice` and `Quot.sound`. To build it:

```bash
cd lean
lake exe cache get
lake build
```

## 4. Repository layout

```
README.md     this file
LICENSE       Apache License 2.0
lean/         Lean 4 + Mathlib: the main theorem (lean/LeanTargetTheorem/MainTheorem.lean)
```

## 5. AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol, and Claude Code using Claude Opus 5.5.

## 6. References

1. K. Hara, A. Sako, *Noncommutative deformations of locally symmetric Kähler manifolds*, J. Geom. Phys. 114 (2017). arXiv:1608.08146
2. T. Okuda, A. Sako, *Explicit formula of deformation quantization with separation of variables for complex two-dimensional locally symmetric Kähler manifold*, Int. J. Geom. Methods Mod. Phys. 20(7) (2023). arXiv:2206.15266
3. T. Okuda, A. Sako, *Deformation quantization with separation of variables of* $`G_{2,4}(\mathbb C)`$, SIGMA 21 (2025) 061. arXiv:2401.00500
4. A. Sako, T. Suzuki, H. Umetsu, *Explicit formulae for noncommutative deformations of* $`\mathbb{CP}^N`$ *and* $`\mathbb{CH}^N`$ (2012). arXiv:1204.4030
5. A. Karabegov, *Deformation quantizations with separation of variables on a Kähler manifold*, Comm. Math. Phys. 180 (1996). arXiv:hep-th/9508013
6. A. Karabegov, *On deformation quantization, on a Kähler manifold, associated to Berezin's quantization*, Funct. Anal. Appl. 30 (1996).
7. A. Karabegov, *An invariant formula for a star product with separation of variables*, J. Geom. Phys. (2012). arXiv:1107.5832
8. F. A. Berezin, *Quantization in complex symmetric spaces*, Math. USSR Izv. 9 (1975).
9. J. Faraut, A. Korányi, *Function spaces and reproducing kernels on bounded symmetric domains*, J. Funct. Anal. 88 (1990).
10. J. Arazy, B. Ørsted, *Asymptotic expansions of Berezin transforms*, Indiana Univ. Math. J. 49 (2000).
11. M. Engliš, *Berezin–Toeplitz quantization on the Schwartz space of bounded symmetric domains*, J. Lie Theory 15 (2005).
12. W. Schmid, *Die Randwerte holomorpher Funktionen auf hermitesch symmetrischen Räumen*, Invent. Math. 9 (1969).
13. N. L. Gammelgaard, *A universal formula for deformation quantization on Kähler manifolds*, Adv. Math. 259 (2014). arXiv:1005.2094
14. P. Schmitt, *Strict quantization of coadjoint orbits*, J. Noncommut. Geom. 15 (2021). arXiv:1907.03185

## Appendix A. Previous work related to the main theorem

| Dimension | $`P_m`$ | Source |
|---|---|---|
| 1 | $`P_m=\prod_{k=1}^m\frac{2\hbar}{2k+\hbar k(k-1)R}\,\gamma^m`$ | Hara–Sako 2017 |
| 2 | $`P_m=\sum_{i,j=1}^{m+1}(T_m)_{ij}\,(\eta^1)^{m-i+1}(\eta^2)^{i-1}(\bar\eta^1)^{m-j+1}(\bar\eta^2)^{j-1}`$, with $`T_m=\hbar^m\sum_{p_1,\dots,p_m}F^{p_m}_m\cdots F^{p_1}_1\,T_0\,(B^{p_1}_1X_1^{-1})\cdots(B^{p_m}_mX_m^{-1})`$ | Okuda–Sako 2023 |
| all | $`P_m=\sum_{\lvert\mathbf m\rvert=m}\frac{\hbar^m\,K_{\mathbf m}}{\prod_{(i,j)\in\mathbf m}(1-\hbar\kappa(j-\frac{(i-1)a}{2}))}`$ | This repository, from Berezin 1975 and Faraut–Korányi 1990 |

### Dimension 1

In dimension 1 the only diagram is the row $`(m)`$, with contents $`0,\dots,m-1`$, and
$`K_{(m)}=\gamma^m/m!`$ with $`\gamma=g_{k\bar l}\,\eta^k\bar\eta^l`$. Substituting into the Answer:

> **Theorem (Answer in dimension 1).**
>
> ```math
> P_m=c_m(\kappa)\,\gamma^m,\qquad c_m(\kappa)=\frac{\hbar^m}{m!\,\prod_{j=0}^{m-1}(1-j\hbar\kappa)} .
> ```

In terms of the curvature $`R`$ used by Hara–Sako, the curvature scale is $`\kappa=-R/2`$. Substituting it,

```math
c_m(\kappa)=\prod_{k=1}^m\frac{\hbar}{k\,\bigl(1+(k-1)\hbar R/2\bigr)}=\prod_{k=1}^m\frac{2\hbar}{2k+\hbar k(k-1)R},
```

so the theorem becomes the following result of Hara–Sako (2017).

> **Hara–Sako (2017).** On a one-dimensional locally symmetric Kähler manifold with curvature $`R`$,
>
> ```math
> P_m=\prod_{k=1}^m\frac{2\hbar}{2k+\hbar k(k-1)R}\;\gamma^m .
> ```

### Dimension 2

A locally symmetric Kähler surface is $`\mathbb{CP}^2`$ or $`\mathbb{CH}^2`$, where the Answer is one row as in
dimension 1, or a product of two curves, where it is the product of two answers of dimension 1.
In a unitary frame:

> **Theorem (Answer in dimension 2).**
>
> ```math
> P_m=c_m(\kappa)\,\gamma^m\quad(\mathbb{CP}^2,\ \mathbb{CH}^2),\qquad P_m=\sum_{p+q=m}c_p(\kappa_1)\,c_q(\kappa_2)\,(\eta^1\bar\eta^1)^p(\eta^2\bar\eta^2)^q\quad(\text{two curves}).
> ```

Okuda–Sako collect the coefficients of $`P_m`$ in an $`(m+1)\times(m+1)`$ matrix $`T_m`$:

```math
P_m=\sum_{i,j=1}^{m+1}T^m_{ij}\,(\eta^1)^{m-i+1}(\eta^2)^{i-1}(\bar\eta^1)^{m-j+1}(\bar\eta^2)^{j-1}.
```

Put $`p=m-i+1`$ and $`q=i-1`$. The theorem says that $`T_m`$ is diagonal, with

```math
T^m_{ii}=\tbinom mq\,c_m(\kappa)\quad(\mathbb{CP}^2,\ \mathbb{CH}^2),\qquad T^m_{ii}=c_p(\kappa_1)\,c_q(\kappa_2)\quad(\text{two curves}).
```

In both cases the only nonzero curvature components $`R_{\bar k}{}^{\bar i\bar j}{}_{\bar l}`$ are those with
$`\{i,j\}=\{k,l\}`$. As in dimension 1, the curvature scales are $`\kappa_1=-R_{\bar1}{}^{\bar1\bar1}{}_{\bar1}/2`$ and
$`\kappa_2=-R_{\bar2}{}^{\bar2\bar2}{}_{\bar2}/2`$; moreover $`R_{\bar2}{}^{\bar2\bar1}{}_{\bar1}=0`$ for two curves, and $`R_{\bar2}{}^{\bar2\bar1}{}_{\bar1}=-\kappa`$ for $`\mathbb{CP}^2`$
and $`\mathbb{CH}^2`$ (where $`\kappa_1=\kappa_2=\kappa`$). Substituting into the matrix $`X_m`$ of Okuda–Sako below, it is diagonal:

```math
\begin{aligned}
X^m_{ii}&=p\bigl(1-(p-1)\hbar\kappa_1\bigr)+q\bigl(1-(q-1)\hbar\kappa_2\bigr)&&(\text{two curves}),\\
X^m_{ii}&=m\bigl(1-(m-1)\hbar\kappa\bigr)&&(\mathbb{CP}^2,\ \mathbb{CH}^2).
\end{aligned}
```

Since $`\hbar\,c_{p-1}(\kappa)=p\bigl(1-(p-1)\hbar\kappa\bigr)\,c_p(\kappa)`$, for two curves

```math
\hbar\bigl(T^{m-1}_{ii}+T^{m-1}_{i-1,i-1}\bigr)=\hbar\bigl(c_{p-1}(\kappa_1)\,c_q(\kappa_2)+c_p(\kappa_1)\,c_{q-1}(\kappa_2)\bigr)=X^m_{ii}\,T^m_{ii},
```

and for $`\mathbb{CP}^2`$, $`\mathbb{CH}^2`$ the same holds by $`\binom{m-1}{q}+\binom{m-1}{q-1}=\binom mq`$. So the theorem satisfies
$`T_mX_m=\hbar A'_m`$. Since $`X_m=m\,I+O(\hbar)`$ is invertible, this equation determines $`T_m`$ from $`T_{m-1}`$,
and the theorem is the following result of Okuda–Sako (2023).

> **Okuda–Sako (2023).** For every two-dimensional locally symmetric Kähler manifold, in a unitary frame,
>
> ```math
> T_mX_m=\hbar A'_m,\qquad (A'_m)_{ij}=T^{m-1}_{ij}+T^{m-1}_{i-1,j-1},
> ```
>
> where $`X_m`$ is pentadiagonal with diagonal entries
>
> ```math
> X^m_{ii}=m+\hbar\Bigl[\tbinom p2R_{\bar1}{}^{\bar1\bar1}{}_{\bar1}+\tbinom q2R_{\bar2}{}^{\bar2\bar2}{}_{\bar2}+2pq\,R_{\bar2}{}^{\bar2\bar1}{}_{\bar1}\Bigr],
> ```
>
> and off-diagonal entries linear in the $`R_{\bar k}{}^{\bar i\bar j}{}_{\bar l}`$ with $`\{i,j\}\neq\{k,l\}`$. Iterating,
>
> ```math
> T_m=\hbar^m\sum_{p_1,\dots,p_m=1}^4F^{p_m}_m\cdots F^{p_1}_1\,T_0\,(B^{p_1}_1X_1^{-1})\cdots(B^{p_m}_mX_m^{-1}),
> ```
>
> where $`F^p_k=\Theta^p_1\,\mathrm{Id}+\Theta^p_2\,S`$ and $`B^p_k=\Theta^p_{\bar1}\,\mathrm{Id}+\Theta^p_{\bar2}\,S^{T}`$, with $`S`$ the shift matrix (ones just below the diagonal) and $`g_{\bar\mu\nu}=\sum_p\Theta^p_{\bar\mu}\Theta^p_\nu`$.
