import LeanTargetTheorem.Basic

/-!
# The box formula solves the Hara–Sako recurrence

`box_formula_of_kernels`: kernels with (K1)–(K4) make the box formula solve the Hara–Sako
recurrence. The proof:

* `ydSet m`: the finitely many Young diagrams with `m` boxes; the finite sums in the statement
  are sums over `ydSet m`.
* Pieri coefficients `γ K_μ = Σ_ν β μ ν K_ν`, and comparison of coefficients by independence.
* The sum rule `Σ_μ β μ ν = m + 1` and the content rule
  `Σ_μ β μ ν κ (λ ν − λ μ) = 2 κ λ ν`, the latter from the commutator `[Q₂, γ]`.
* Adding a box: `B ν = B μ (1 − ℏ κ (λ ν − λ μ)/2)`.
-/

noncomputable section

open MvPolynomial

namespace LeanTargetTheorem

variable {F : Type*} [Field F] {n : ℕ}

/-! ## Finitely many diagrams of each size -/

theorem cell_lt_card (μ : YoungDiagram) {c : ℕ × ℕ} (hc : c ∈ μ.cells) :
    c.1 < μ.cells.card ∧ c.2 < μ.cells.card := by
  have hcμ : (c.1, c.2) ∈ μ := (YoungDiagram.mem_cells _).mp hc
  constructor
  · have hsub : (Finset.range (c.1 + 1)).image (fun k => (k, c.2)) ⊆ μ.cells := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      exact (YoungDiagram.mem_cells _).mpr (μ.up_left_mem (by omega) le_rfl hcμ)
    have h := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range] at h
    omega
  · have hsub : (Finset.range (c.2 + 1)).image (fun k => (c.1, k)) ⊆ μ.cells := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      exact (YoungDiagram.mem_cells _).mpr (μ.up_left_mem le_rfl (by omega) hcμ)
    have h := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range] at h
    omega

theorem finite_card (m : ℕ) : {μ : YoungDiagram | μ.cells.card = m}.Finite := by
  have hinj : Set.InjOn (fun μ : YoungDiagram => μ.cells) {μ | μ.cells.card = m} :=
    fun μ _ ν _ h => YoungDiagram.ext h
  refine Set.Finite.of_finite_image ?_ hinj
  refine ((Finset.range m ×ˢ Finset.range m).powerset.finite_toSet).subset ?_
  rintro _ ⟨μ, hμ, rfl⟩
  rw [Finset.mem_coe, Finset.mem_powerset]
  intro c hc
  have h := cell_lt_card μ hc
  replace hμ : μ.cells.card = m := hμ
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
  omega

/-- The Young diagrams with `m` boxes. -/
def ydSet (m : ℕ) : Finset YoungDiagram := (finite_card m).toFinset

theorem mem_ydSet {m : ℕ} {μ : YoungDiagram} : μ ∈ ydSet m ↔ μ.cells.card = m := by
  simp [ydSet]

theorem finsum_card_eq {M : Type*} [AddCommMonoid M] (f : YoungDiagram → M) (m : ℕ) :
    ∑ᶠ (μ : YoungDiagram) (_ : μ.cells.card = m), f μ = ∑ μ ∈ ydSet m, f μ :=
  finsum_mem_eq_finite_toFinset_sum f (finite_card m)

/-! ## Comparing coefficients -/

theorem coeff_eq_zero {K : YoungDiagram → Poly F n} {M : ℕ}
    (hind : LinearIndependent F fun μ : {μ : YoungDiagram // μ.cells.card = M ∧ K μ ≠ 0} => K μ)
    (c : YoungDiagram → F) (h : ∑ ν ∈ ydSet M, c ν • K ν = 0) :
    ∀ ν ∈ ydSet M, K ν ≠ 0 → c ν = 0 := by
  classical
  intro ν hν hK
  have h' : ∑ i ∈ (ydSet M).subtype (fun μ => μ.cells.card = M ∧ K μ ≠ 0),
      (fun i : {μ : YoungDiagram // μ.cells.card = M ∧ K μ ≠ 0} => c i.1) i • K i.1 = 0 := by
    rw [Finset.sum_subtype_eq_sum_filter (f := fun μ => c μ • K μ), Finset.sum_filter_of_ne]
    · exact h
    · intro x hx hne
      refine ⟨mem_ydSet.mp hx, fun h0 => hne ?_⟩
      rw [h0, smul_zero]
  exact (linearIndependent_iff'.mp hind) _ _ h' ⟨ν, mem_ydSet.mp hν, hK⟩
    (Finset.mem_subtype.mpr hν)

/-! ## `Q₂` on scalar multiples and on powers of `γ` -/

theorem Q2_smul (R : Curv F n) (c : F) (P : Poly F n) : Q2 R (c • P) = c • Q2 R P := by
  rw [smul_eq_C_mul, smul_eq_C_mul, Q2_C_mul]

theorem Q2_sum_smul {ι : Type*} (R : Curv F n) (s : Finset ι) (c : ι → F) (f : ι → Poly F n) :
    Q2 R (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • Q2 R (f i) := by
  rw [Q2_sum]
  exact Finset.sum_congr rfl fun i _ => Q2_smul R (c i) (f i)

theorem Q2_one (R : Curv F n) : Q2 R (1 : Poly F n) = 0 := by
  simp [Q2]

theorem Q2_gamma (R : Curv F n) : Q2 R (gamma : Poly F n) = 0 := by
  simp [Q2, pderiv_inr_gamma, pderiv_inr_eta]

/-- `S R = Σ R^{āb̄}_{l̄q̄} η̄ˡ η̄^q ηᵃ ηᵇ`. -/
def Sform (R : Curv F n) : Poly F n :=
  ∑ a, ∑ b, ∑ l, ∑ q, C (R a b l q) * etaBar l * etaBar q * eta a * eta b

/-- The scalar `(k + 2)(k + 1)/2`. -/
def qc (k : ℕ) : F := ((k : F) + 2) * ((k : F) + 1) / 2

theorem Q2_gamma_pow_add_two (R : Curv F n) (k : ℕ) :
    Q2 R (gamma ^ (k + 2)) = C (qc k) * gamma ^ k * Sform R := by
  have h2 : ∀ a b : Fin n, pderiv (Sum.inr a) (pderiv (Sum.inr b) (gamma ^ (k + 2) : Poly F n)) =
      C (((k : F) + 1 + 1) * ((k : F) + 1)) * gamma ^ k * eta a * eta b := fun a b => by
    rw [pderiv_inr_gamma_pow, mul_assoc, pderiv_C_mul, Derivation.leibniz, pderiv_inr_eta,
      pderiv_inr_gamma_pow]
    simp only [smul_eq_mul, map_mul, mul_zero]
    push_cast
    ring
  simp only [Q2, h2, Sform, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun q _ => ?_
  rw [show C (R a b l q / 2) = C (R a b l q) * C (2⁻¹ : F) by rw [← map_mul, div_eq_mul_inv],
    show C (qc k : F) = C (((k : F) + 1 + 1) * ((k : F) + 1)) * C (2⁻¹ : F) by
      rw [← map_mul]; congr 1; simp only [qc]; ring]
  ring

/-- The commutator identity `(m − 1) Q₂ γ^{m+1} = (m + 1) γ Q₂ γ^m`. -/
theorem Q2_comm_gamma_pow (R : Curv F n) (m : ℕ) :
    ((m : F) - 1) • Q2 R (gamma ^ (m + 1)) = ((m : F) + 1) • (gamma * Q2 R (gamma ^ m)) := by
  match m with
  | 0 => simp [Q2_gamma, Q2_one]
  | 1 => simp [Q2_gamma]
  | k + 2 =>
    rw [show k + 2 + 1 = k + 1 + 2 by omega, Q2_gamma_pow_add_two, Q2_gamma_pow_add_two,
      smul_eq_C_mul, smul_eq_C_mul]
    have key : (((k + 2 : ℕ) : F) - 1) * qc (k + 1) = (((k + 2 : ℕ) : F) + 1) * qc k := by
      simp only [qc]; push_cast; ring
    have kC := congrArg (C : F → Poly F n) key
    simp only [map_mul] at kC
    linear_combination (gamma ^ (k + 1) * Sform R) * kC

/-! ## Adding one box -/

theorem exists_new_cell {μ ν : YoungDiagram} (h : μ ≤ ν)
    (hc : ν.cells.card = μ.cells.card + 1) : ∃ x, x ∉ μ.cells ∧ ν.cells = insert x μ.cells := by
  have hsub : μ.cells ⊆ ν.cells := YoungDiagram.cells_subset_iff.mpr h
  have hcard : (ν.cells \ μ.cells).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  have hxs : x ∈ ν.cells \ μ.cells := by rw [hx]; exact Finset.mem_singleton_self x
  refine ⟨x, (Finset.mem_sdiff.mp hxs).2, ?_⟩
  rw [← Finset.union_sdiff_of_subset hsub, hx, Finset.insert_eq, Finset.union_comm]

theorem box_step [CharZero F] (ℏ κ : F) (a : ℕ) {μ ν : YoungDiagram} (h : μ ≤ ν)
    (hc : ν.cells.card = μ.cells.card + 1) :
    boxProd ℏ κ a ν = boxProd ℏ κ a μ * (1 - ℏ * κ * ((eig a ν - eig a μ) / 2)) := by
  obtain ⟨x, hx, hν⟩ := exists_new_cell h hc
  simp only [boxProd, eig, hν, Finset.prod_insert hx, Finset.sum_insert hx]
  ring

theorem boxProd_ne_zero [CharZero F] {ℏ κ : F} (hgen : Generic ℏ κ) (a : ℕ) (μ : YoungDiagram) :
    boxProd ℏ κ a μ ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun c _ => ?_
  have e : (content a c : F) = (((c.2 : ℚ) - (c.1 : ℚ) * a / 2 : ℚ) : F) := by
    simp only [content]
    push_cast
    ring
  rw [e]
  exact hgen _

/-! ## Pieri coefficients -/

theorem pieri_coeff {K : YoungDiagram → Poly F n}
    (hK_pieri : ∀ μ, gamma * K μ ∈
      Submodule.span F (K '' {ν | μ ≤ ν ∧ ν.cells.card = μ.cells.card + 1})) :
    ∃ β : YoungDiagram → YoungDiagram → F, ∀ μ,
      gamma * K μ = (∑ ν ∈ ydSet (μ.cells.card + 1), β μ ν • K ν) ∧ ∀ ν, β μ ν ≠ 0 → μ ≤ ν := by
  have h := fun μ => (Finsupp.mem_span_image_iff_linearCombination F).mp (hK_pieri μ)
  choose l hl hlx using h
  refine ⟨fun μ ν => l μ ν, fun μ => ⟨?_, fun ν hν => ?_⟩⟩
  · rw [← hlx μ, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Finset.sum_subset
    · intro ν hν
      exact mem_ydSet.mpr ((Finsupp.mem_supported F (l μ)).mp (hl μ) hν).2
    · intro ν _ hν
      rw [Finsupp.notMem_support_iff.mp hν, zero_smul]
  · exact ((Finsupp.mem_supported F (l μ)).mp (hl μ) (Finsupp.mem_support_iff.mpr hν)).1

/-! ## The sum rule and the content rule -/

theorem gamma_pow_factorial [CharZero F] (m : ℕ) :
    gamma * ((m.factorial : F)⁻¹ • gamma ^ m) =
      ((m : F) + 1) • (((m + 1).factorial : F)⁻¹ • (gamma : Poly F n) ^ (m + 1)) := by
  have h : ((m : F) + 1) * ((m + 1).factorial : F)⁻¹ = (m.factorial : F)⁻¹ := by
    have hf : (m.factorial : F) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hm : (m : F) + 1 ≠ 0 := Nat.cast_add_one_ne_zero m
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  rw [smul_smul, h, smul_eq_C_mul, smul_eq_C_mul, pow_succ]
  ring


section rules

variable [CharZero F] {K : YoungDiagram → Poly F n}
  (hK_sum : ∀ m : ℕ,
    ∑ᶠ (μ : YoungDiagram) (_ : μ.cells.card = m), K μ = (m.factorial : F)⁻¹ • gamma ^ m)
  (β : YoungDiagram → YoungDiagram → F)
  (hβ : ∀ μ, gamma * K μ = ∑ ν ∈ ydSet (μ.cells.card + 1), β μ ν • K ν)
  (hK_indep : ∀ m : ℕ,
    LinearIndependent F fun μ : {μ : YoungDiagram // μ.cells.card = m ∧ K μ ≠ 0} => K μ)
omit [CharZero F] in
include hK_sum hβ in
theorem gamma_mul_sum (m : ℕ) :
    ∑ ν ∈ ydSet (m + 1), (∑ μ ∈ ydSet m, β μ ν) • K ν =
      gamma * ((m.factorial : F)⁻¹ • gamma ^ m) := by
  have hβm : ∀ μ ∈ ydSet m, gamma * K μ = ∑ ν ∈ ydSet (m + 1), β μ ν • K ν := fun μ hμ => by
    rw [hβ μ, mem_ydSet.mp hμ]
  have hsum := hK_sum m
  rw [finsum_card_eq] at hsum
  rw [← hsum, Finset.mul_sum, Finset.sum_congr rfl hβm, Finset.sum_comm]
  simp only [Finset.sum_smul]

include hK_sum hβ hK_indep

/-- The sum rule `Σ_μ β μ ν = m + 1`. -/
theorem sum_rule (m : ℕ) :
    ∀ ν ∈ ydSet (m + 1), K ν ≠ 0 → ∑ μ ∈ ydSet m, β μ ν = (m : F) + 1 := by
  have hsum1 := hK_sum (m + 1)
  rw [finsum_card_eq] at hsum1
  have hzero : ∑ ν ∈ ydSet (m + 1), (∑ μ ∈ ydSet m, β μ ν - ((m : F) + 1)) • K ν = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [gamma_mul_sum hK_sum β hβ, ← Finset.smul_sum, hsum1, gamma_pow_factorial, sub_self]
  intro ν hν hK
  exact sub_eq_zero.mp (coeff_eq_zero (hK_indep (m + 1)) _ hzero ν hν hK)

/-- The content rule `Σ_μ β μ ν κ (λ ν − λ μ) = 2 κ λ ν`. -/
theorem content_rule (R : Curv F n) (κ : F) (a : ℕ)
    (hK_eig : ∀ μ, Q2 R (K μ) = (κ * eig a μ) • K μ) (m : ℕ) :
    ∀ ν ∈ ydSet (m + 1), K ν ≠ 0 →
      ∑ μ ∈ ydSet m, β μ ν * (κ * (eig a ν - eig a μ)) = 2 * (κ * eig a ν) := by
  have hβm : ∀ μ ∈ ydSet m, gamma * K μ = ∑ ν ∈ ydSet (m + 1), β μ ν • K ν := fun μ hμ => by
    rw [hβ μ, mem_ydSet.mp hμ]
  have hsum := hK_sum m
  have hsum1 := hK_sum (m + 1)
  rw [finsum_card_eq] at hsum hsum1
  -- each commutator `[Q₂, γ] K_μ` in the basis `K_ν`
  have hterm : ∀ μ ∈ ydSet m, Q2 R (gamma * K μ) - gamma * Q2 R (K μ) =
      ∑ ν ∈ ydSet (m + 1), (β μ ν * (κ * (eig a ν - eig a μ))) • K ν := fun μ hμ => by
    rw [hK_eig, mul_smul_comm, hβm μ hμ, Q2_sum_smul, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hK_eig, smul_smul, smul_smul, ← sub_smul]
    congr 1
    ring
  -- summed over `μ`, the commutator is `(m!)⁻¹ (Q₂ γ^{m+1} − γ Q₂ γ^m)`
  have hD : ∑ μ ∈ ydSet m, (Q2 R (gamma * K μ) - gamma * Q2 R (K μ)) =
      (m.factorial : F)⁻¹ • (Q2 R (gamma ^ (m + 1)) - gamma * Q2 R (gamma ^ m)) := by
    rw [Finset.sum_sub_distrib, ← Q2_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Q2_sum, hsum,
      mul_smul_comm, Q2_smul, Q2_smul, mul_smul_comm, ← smul_sub, pow_succ', mul_comm gamma]
  -- `Σ_ν 2 κ λ ν K_ν = 2 Q₂ (γ^{m+1}/(m+1)!)`
  have hE : ∑ ν ∈ ydSet (m + 1), (2 * (κ * eig a ν)) • K ν =
      (2 * ((m + 1).factorial : F)⁻¹) • Q2 R (gamma ^ (m + 1)) := by
    have : ∑ ν ∈ ydSet (m + 1), (2 * (κ * eig a ν)) • K ν =
        (2 : F) • Q2 R (∑ ν ∈ ydSet (m + 1), K ν) := by
      rw [Q2_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [hK_eig, smul_smul]
    rw [this, hsum1, Q2_smul, smul_smul]
  -- the commutator identity closes the gap
  have hcomm := Q2_comm_gamma_pow R m
  have hfac : (m.factorial : F)⁻¹ = ((m : F) + 1) * ((m + 1).factorial : F)⁻¹ := by
    have hf : (m.factorial : F) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hm : (m : F) + 1 ≠ 0 := Nat.cast_add_one_ne_zero m
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  have hzero : ∑ ν ∈ ydSet (m + 1),
      (∑ μ ∈ ydSet m, β μ ν * (κ * (eig a ν - eig a μ)) - 2 * (κ * eig a ν)) • K ν = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul]
    rw [Finset.sum_comm, ← Finset.sum_congr rfl hterm, hD, hE, hfac]
    simp only [smul_eq_C_mul, map_mul, map_sub, map_add, map_natCast, map_one, map_ofNat] at hcomm ⊢
    linear_combination (C (((m + 1).factorial : F)⁻¹)) * hcomm
  intro ν hν hK
  exact sub_eq_zero.mp (coeff_eq_zero (hK_indep (m + 1)) _ hzero ν hν hK)

end rules

/-! ## The box formula solves the recurrence -/

theorem box_starRec [CharZero F] (R : Curv F n) (κ ℏ : F) (a : ℕ) (hgen : Generic ℏ κ)
    (K : YoungDiagram → Poly F n)
    (hK_sum : ∀ m : ℕ,
      ∑ᶠ (μ : YoungDiagram) (_ : μ.cells.card = m), K μ = (m.factorial : F)⁻¹ • gamma ^ m)
    (hK_eig : ∀ μ, Q2 R (K μ) = (κ * eig a μ) • K μ)
    (hK_pieri : ∀ μ, gamma * K μ ∈
      Submodule.span F (K '' {ν | μ ≤ ν ∧ ν.cells.card = μ.cells.card + 1}))
    (hK_indep : ∀ m : ℕ,
      LinearIndependent F fun μ : {μ : YoungDiagram // μ.cells.card = m ∧ K μ ≠ 0} => K μ) :
    StarRec R ℏ (boxSeries ℏ κ a K) := by
  obtain ⟨β, hβ⟩ := pieri_coeff hK_pieri
  have hβeq : ∀ μ, gamma * K μ = ∑ ν ∈ ydSet (μ.cells.card + 1), β μ ν • K ν :=
    fun μ => (hβ μ).1
  have hB := boxProd_ne_zero hgen a
  refine ⟨?_, fun m => ?_⟩
  · have h0 := hK_sum 0
    rw [finsum_card_eq] at h0
    simp only [boxSeries, finsum_card_eq]
    rw [show ∑ μ ∈ ydSet 0, (ℏ ^ 0 / boxProd ℏ κ a μ) • K μ = ∑ μ ∈ ydSet 0, K μ from
      Finset.sum_congr rfl fun μ hμ => by
        have hc : μ.cells = ∅ := Finset.card_eq_zero.mp (mem_ydSet.mp hμ)
        simp [boxProd, hc], h0]
    simp
  · simp only [boxSeries, finsum_card_eq]
    -- the left side in the basis `K_ν`
    have hL : ((m : F) + 1) • ∑ ν ∈ ydSet (m + 1), (ℏ ^ (m + 1) / boxProd ℏ κ a ν) • K ν -
        ℏ • Q2 R (∑ ν ∈ ydSet (m + 1), (ℏ ^ (m + 1) / boxProd ℏ κ a ν) • K ν) =
        ∑ ν ∈ ydSet (m + 1),
          (ℏ ^ (m + 1) / boxProd ℏ κ a ν * (((m : F) + 1) - ℏ * (κ * eig a ν))) • K ν := by
      rw [Q2_sum_smul, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [hK_eig, smul_smul, smul_smul, smul_smul, ← sub_smul]
      congr 1
      ring
    -- the right side in the basis `K_ν`
    have hR : ℏ • (gamma * ∑ μ ∈ ydSet m, (ℏ ^ m / boxProd ℏ κ a μ) • K μ) =
        ∑ ν ∈ ydSet (m + 1), (∑ μ ∈ ydSet m, ℏ ^ (m + 1) / boxProd ℏ κ a μ * β μ ν) • K ν := by
      rw [Finset.mul_sum, Finset.smul_sum]
      have h : ∀ μ ∈ ydSet m, ℏ • (gamma * (ℏ ^ m / boxProd ℏ κ a μ) • K μ) =
          ∑ ν ∈ ydSet (m + 1), (ℏ ^ (m + 1) / boxProd ℏ κ a μ * β μ ν) • K ν := fun μ hμ => by
        rw [mul_smul_comm, hβeq μ, mem_ydSet.mp hμ, Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [smul_smul, smul_smul]
        congr 1
        rw [pow_succ]
        ring
      rw [Finset.sum_congr rfl h, Finset.sum_comm]
      simp only [Finset.sum_smul]
    rw [hL, hR]
    refine Finset.sum_congr rfl fun ν hν => ?_
    by_cases hK : K ν = 0
    · rw [hK, smul_zero, smul_zero]
    · congr 1
      have hs := sum_rule hK_sum β hβeq hK_indep m ν hν hK
      have hc := content_rule hK_sum β hβeq hK_indep R κ a hK_eig m ν hν hK
      have hν' : ν.cells.card = m + 1 := mem_ydSet.mp hν
      -- one box at a time: `1/B μ = (1 − ℏκ (λν − λμ)/2) / B ν`
      have hterm : ∀ μ ∈ ydSet m, ℏ ^ (m + 1) / boxProd ℏ κ a μ * β μ ν =
          ℏ ^ (m + 1) / boxProd ℏ κ a ν * (β μ ν * (1 - ℏ * κ * ((eig a ν - eig a μ) / 2))) := by
        intro μ hμ
        by_cases h0 : β μ ν = 0
        · rw [h0]
          ring
        · have hstep := box_step ℏ κ a ((hβ μ).2 ν h0) (by rw [hν', mem_ydSet.mp hμ])
          have h1 := hB μ
          have h2 : 1 - ℏ * κ * ((eig a ν - eig a μ) / 2) ≠ 0 := by
            intro hz
            apply hB ν
            rw [hstep, hz, mul_zero]
          have h3 : (2 : F) - ℏ * κ * (eig a ν - eig a μ) ≠ 0 := by
            intro hz
            apply h2
            linear_combination hz / 2
          rw [hstep]
          field_simp
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      have hsplit : ∑ μ ∈ ydSet m, β μ ν * (1 - ℏ * κ * ((eig a ν - eig a μ) / 2)) =
          ∑ μ ∈ ydSet m, β μ ν - ℏ / 2 * ∑ μ ∈ ydSet m, β μ ν * (κ * (eig a ν - eig a μ)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun μ _ => by ring
      rw [hsplit, hs, hc]
      ring

/-! ## The algebraic form, with the kernel properties as a structure -/

open scoped Nat in
/-- Kernels `K_μ`, indexed by Young diagrams `μ`, with the properties (K1)–(K4). -/
structure Kernels (R : Curv F n) (κ : F) (a : ℕ) where
  /-- The kernel `K_μ`. -/
  K : YoungDiagram → Poly F n
  /-- (K1) `Σ_{|μ| = m} K_μ = γ^m / m!`. -/
  K1 : ∀ m : ℕ, ∑ᶠ (μ : YoungDiagram) (_ : size μ = m), K μ = (m ! : F)⁻¹ • γ ^ m
  /-- (K2) `Q₂ K_μ = κ λ(μ) K_μ`. -/
  K2 : ∀ μ, Q₂ R (K μ) = (κ * eig a μ) • K μ
  /-- (K3) `γ K_μ` is a linear combination of the `K_ν` with `ν = μ + □`. -/
  K3 : ∀ μ, γ * K μ ∈ Submodule.span F (K '' {ν | AddsOneBox μ ν})
  /-- (K4) The nonzero `K_μ` with `|μ| = m` are linearly independent. -/
  K4 : ∀ m : ℕ, LinearIndependent F fun μ : {μ : YoungDiagram // size μ = m ∧ K μ ≠ 0} => K μ

/-- Kernels with (K1)–(K4) make the box formula solve the Hara–Sako recurrence, for every
curvature tensor and generic `ℏ`; no analysis is used. -/
theorem box_formula_of_kernels [CharZero F] (R : Curv F n) (κ ℏ : F) (a : ℕ)
    (hℏ : Generic ℏ κ) (K : Kernels R κ a) :
    HaraSako R ℏ fun m =>
      ∑ᶠ (μ : YoungDiagram) (_ : size μ = m),
        (ℏ ^ m / ∏ c ∈ μ.cells, (1 - ℏ * κ * content a c)) • K.K μ := by
  obtain ⟨h0, hrec⟩ := box_starRec R κ ℏ a hℏ K.K K.K1 K.K2 K.K3 K.K4
  refine ⟨h0, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.cast_add_one]
  exact hrec k

end LeanTargetTheorem
