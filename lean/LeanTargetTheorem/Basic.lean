import LeanTargetTheorem.Defs

/-!
# Basic lemmas

Linearity of `Q₂` and the derivatives of `γ` with respect to `η̄`.
-/

noncomputable section

open MvPolynomial

namespace LeanTargetTheorem

variable {F : Type*} [Field F] {n : ℕ}

/-! ## Linearity of `Q₂` -/

theorem Q2_add (R : Curv F n) (P Q : Poly F n) : Q2 R (P + Q) = Q2 R P + Q2 R Q := by
  simp only [Q2, map_add, mul_add, Finset.sum_add_distrib]

theorem Q2_sum {ι : Type*} (R : Curv F n) (s : Finset ι) (f : ι → Poly F n) :
    Q2 R (∑ i ∈ s, f i) = ∑ i ∈ s, Q2 R (f i) :=
  map_sum (AddMonoidHom.mk' (Q2 R) (Q2_add R)) f s

/-! ## Derivatives of `γ` -/

/-- `∂_{η̄ᵃ} ηᵇ = 0`. -/
theorem pderiv_inr_eta (a b : Fin n) : pderiv (Sum.inr a) (eta b : Poly F n) = 0 := by
  simp [eta, pderiv_X]

/-- `∂_{η̄ᵃ} γ = ηᵃ`. -/
theorem pderiv_inr_gamma (a : Fin n) : pderiv (Sum.inr a) (gamma : Poly F n) = eta a := by
  simp [gamma, Derivation.leibniz, pderiv_inr_eta, etaBar, pderiv_X, Pi.single_apply]

/-- `∂_{η̄ᵃ} γ^{k+1} = (k + 1) γ^k ηᵃ`. -/
theorem pderiv_inr_gamma_pow (a : Fin n) (k : ℕ) :
    pderiv (Sum.inr a) (gamma ^ (k + 1) : Poly F n) = C ((k : F) + 1) * gamma ^ k * eta a := by
  rw [Derivation.leibniz_pow, pderiv_inr_gamma]
  simp only [add_tsub_cancel_right, smul_eq_mul, nsmul_eq_mul, map_add, map_natCast, map_one]
  push_cast
  ring

end LeanTargetTheorem
