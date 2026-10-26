import LeanTargetTheorem.BoxProof

/-!
# Main theorem: Problem and Answer

*Problem.* For a Kähler manifold with `∇R = 0`, find in closed form the coefficients `P m` of the
standard star product with separation of variables.

*Answer.* On an irreducible Hermitian symmetric space of multiplicity `a` and curvature scale
`κ`,

  `P m = Σ_{|μ| = m} ℏ^m K_μ / ∏_{c ∈ μ} (1 − ℏ κ c)`,

where `K_μ` is the Fischer kernel of the Schmid component `𝒫_μ`.

The main theorem proves the Answer assuming two classical theorems, stated below as `Berezin` (B)
and `FarautKoranyi` (FK), at the weight `ν = −1/(ℏ κ)`. The derivation is in `README.md`, Section 2.
-/

noncomputable section

open MvPolynomial

namespace LeanTargetTheorem

variable {F : Type*} [Field F] {n : ℕ}

/-! ## Holomorphic polynomials and the Fischer pairing -/

/-- Holomorphic polynomials in `z¹, …, zⁿ`. -/
abbrev Hol (F : Type*) [Field F] (n : ℕ) : Type _ := MvPolynomial (Fin n) F

/-- The multi-indices `α` of degree `m`. -/
def multiIdx (n m : ℕ) : Finset (Fin n →₀ ℕ) := Finset.univ.finsuppAntidiag m

/-- `α! = ∏ αᵢ!`. -/
def mfact (α : Fin n →₀ ℕ) : F := α.prod fun _ k => (k.factorial : F)

/-- The monomial `zᵅ`. -/
abbrev zpow (α : Fin n →₀ ℕ) : Hol F n := monomial α 1

/-- The monomial `ηᵝ η̄ᵅ`. -/
def etaMono (β α : Fin n →₀ ℕ) : Poly F n :=
  monomial (Finsupp.mapDomain Sum.inl β + Finsupp.mapDomain Sum.inr α) 1

/-- The Fischer pairing `⟨p, q⟩_F = Σ_α p_α q_α α!`. -/
def fischer (p q : Hol F n) : F := ∑ α ∈ p.support, p.coeff α * q.coeff α * mfact α

/-! ## The Schmid decomposition and its Fischer kernels -/

/-- A Schmid decomposition: Fischer-orthogonal projections `proj μ` onto components `𝒫_μ` of
degree `|μ|`, labelled by Young diagrams, that add up to the identity in each degree. -/
structure Schmid (F : Type*) [Field F] (n : ℕ) where
  /-- The projection onto the component `𝒫_μ`. -/
  proj : YoungDiagram → Hol F n →ₗ[F] Hol F n
  proj_idem : ∀ μ p, proj μ (proj μ p) = proj μ p
  proj_orth : ∀ μ μ' p, μ ≠ μ' → proj μ (proj μ' p) = 0
  proj_selfAdjoint : ∀ μ p q, fischer (proj μ p) q = fischer p (proj μ q)
  proj_sum : ∀ (d : ℕ) (p : Hol F n), p.IsHomogeneous d →
    ∑ᶠ (μ : YoungDiagram) (_ : size μ = d), proj μ p = p

/-- The Fischer reproducing kernel of `𝒫_μ`:
`K_μ(η, η̄) = Σ_{α, β} ⟨(zᵅ)_μ, (zᵝ)_μ⟩_F / (α! β!) · ηᵝ η̄ᵅ`. -/
def fischerKernel (S : Schmid F n) (μ : YoungDiagram) : Poly F n :=
  ∑ α ∈ multiIdx n μ.cells.card, ∑ β ∈ multiIdx n μ.cells.card,
    (fischer (S.proj μ (zpow α)) (S.proj μ (zpow β)) / (mfact α * mfact β)) • etaMono β α

/-- The generalized Pochhammer symbol `(ν)_μ = ∏_{c ∈ μ} (ν + c)`. -/
def poch (ν : F) (a : ℕ) (μ : YoungDiagram) : F := ∏ c ∈ μ.cells, (ν + content a c)

/-! ## The two classical theorems, as hypotheses -/

/-- **(B) Berezin.** The coefficients of the standard star product at the origin are the moments
of the weighted Bergman pairing `bergman p q = ∫ p q̄ dμ_ν`:
`P m = Σ_{|α| = |β| = m} (−κ)^{−m} ⟨zᵅ, zᵝ⟩_ν / (α! β!) · ηᵝ η̄ᵅ`. -/
def Berezin (κ : F) (bergman : Hol F n → Hol F n → F) (P : ℕ → Poly F n) : Prop :=
  ∀ m, P m = ∑ α ∈ multiIdx n m, ∑ β ∈ multiIdx n m,
    ((-κ)⁻¹ ^ m * bergman (zpow α) (zpow β) / (mfact α * mfact β)) • etaMono β α

/-- **(FK) Faraut–Korányi.** On homogeneous polynomials of degree `d`, the weighted Bergman pairing
is the sum over the Schmid components of the Fischer pairing divided by `(ν)_μ`. -/
def FarautKoranyi (S : Schmid F n) (a : ℕ) (ν : F) (bergman : Hol F n → Hol F n → F) : Prop :=
  ∀ (d : ℕ) (p q : Hol F n), p.IsHomogeneous d → q.IsHomogeneous d →
    bergman p q = ∑ᶠ (μ : YoungDiagram) (_ : size μ = d),
      fischer (S.proj μ p) (S.proj μ q) / poch ν a μ

/-! ## The main theorem -/

/-- **Main theorem.** Let `P m` be the coefficients of the standard star product. Assuming
Berezin's theorem (B) and the Faraut–Korányi formula (FK) at the weight `ν = −1/(ℏ κ)`,
`P m = Σ_{|μ| = m} ℏ^m K_μ / ∏_{c ∈ μ} (1 − ℏ κ c)`, with `K_μ` the Fischer kernels. -/
theorem main_theorem [CharZero F] (κ ℏ : F) (a : ℕ) (hκ : κ ≠ 0) (hℏ : ℏ ≠ 0)
    (S : Schmid F n) (bergman : Hol F n → Hol F n → F)
    (P : ℕ → Poly F n) (hB : Berezin κ bergman P)
    (hFK : FarautKoranyi S a (-1 / (ℏ * κ)) bergman) (m : ℕ) :
    P m = ∑ᶠ (μ : YoungDiagram) (_ : size μ = m),
      (ℏ ^ m / ∏ c ∈ μ.cells, (1 - ℏ * κ * content a c)) • fischerKernel S μ := by
  -- monomials of degree `m` are homogeneous
  have hdeg : ∀ α ∈ multiIdx n m, (zpow α : Hol F n).IsHomogeneous m := by
    intro α hα
    apply isHomogeneous_monomial
    rw [Finsupp.degree_eq_sum]
    exact (Finset.mem_finsuppAntidiag.mp hα).1
  -- one box at a time: `(−κ)^{−m} / (ν)_μ = ℏ^m / ∏ (1 − ℏ κ c)` at `ν = −1/(ℏ κ)`
  have hscal : ∀ μ : YoungDiagram, μ.cells.card = m →
      (-κ)⁻¹ ^ m / poch (-1 / (ℏ * κ)) a μ = ℏ ^ m / ∏ c ∈ μ.cells, (1 - ℏ * κ * content a c) := by
    intro μ hμ
    have hpoch : poch (-1 / (ℏ * κ)) a μ =
        (-1 / (ℏ * κ)) ^ m * ∏ c ∈ μ.cells, (1 - ℏ * κ * content a c) := by
      rw [poch, ← hμ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun c _ => ?_
      field_simp
      ring
    have hq : (-κ)⁻¹ / (-1 / (ℏ * κ)) = ℏ := by
      field_simp
    rw [hpoch, ← div_div, ← div_pow, hq]
  -- Step 1–2: (B), then (FK) for each pair of monomials
  rw [finsum_card_eq, hB m]
  have hL : ∀ α ∈ multiIdx n m, ∀ β ∈ multiIdx n m,
      ((-κ)⁻¹ ^ m * bergman (zpow α) (zpow β) / (mfact α * mfact β)) • (etaMono β α : Poly F n) =
      ∑ μ ∈ ydSet m, (ℏ ^ m / ∏ c ∈ μ.cells, (1 - ℏ * κ * content a c)) •
        ((fischer (S.proj μ (zpow α)) (S.proj μ (zpow β)) / (mfact α * mfact β)) •
          (etaMono β α : Poly F n)) := by
    intro α hα β hβ
    rw [hFK m _ _ (hdeg α hα) (hdeg β hβ), finsum_card_eq, Finset.mul_sum, Finset.sum_div,
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [smul_smul, ← hscal μ (mem_ydSet.mp hμ)]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun α hα => Finset.sum_congr rfl fun β hβ => hL α hα β hβ]
  -- Step 3–4: collect the terms of each Young diagram into its Fischer kernel
  have hR : ∀ μ ∈ ydSet m, (ℏ ^ m / ∏ c ∈ μ.cells, (1 - ℏ * κ * content a c)) •
      fischerKernel S μ =
      ∑ α ∈ multiIdx n m, ∑ β ∈ multiIdx n m,
        (ℏ ^ m / ∏ c ∈ μ.cells, (1 - ℏ * κ * content a c)) •
          ((fischer (S.proj μ (zpow α)) (S.proj μ (zpow β)) / (mfact α * mfact β)) •
            (etaMono β α : Poly F n)) := by
    intro μ hμ
    rw [fischerKernel, mem_ydSet.mp hμ, Finset.smul_sum]
    simp only [Finset.smul_sum]
  rw [Finset.sum_congr rfl hR]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]

end LeanTargetTheorem
