import Mathlib

/-!
# Definitions shared by the target theorems

The standard star product with separation of variables on a Kähler manifold with `∇R = 0` is
encoded by polynomials `P m` in `η¹, …, ηⁿ, η̄¹, …, η̄ⁿ`: `P m` collects the coefficients of the
terms with `m` holomorphic and `m` antiholomorphic derivatives. They are determined by

  `(m − ℏ Q₂) P m = ℏ γ P (m − 1)`,  `P 0 = 1`,

with `γ = Σ ηᵏ η̄ᵏ` and `Q₂ = ½ Σ R^{āb̄}_{l̄q̄} η̄ˡ η̄^q ∂_{η̄ᵃ} ∂_{η̄ᵇ}`, written in a unitary frame
at a point (`g_{k l̄} = δ_{kl}`).

The deformation parameter `ℏ` is an element of a field `F` of characteristic zero, assumed
`Generic`: `1 − ℏ κ q ≠ 0` for every rational `q`, as for a formal parameter.
-/

noncomputable section

open MvPolynomial

namespace LeanTargetTheorem

/-- Polynomials in `η¹, …, ηⁿ` (variables `Sum.inl i`) and `η̄¹, …, η̄ⁿ` (variables `Sum.inr i`). -/
abbrev Poly (F : Type*) [Field F] (n : ℕ) : Type _ := MvPolynomial (Fin n ⊕ Fin n) F

/-- A curvature tensor `R a b l q = R^{āb̄}_{l̄q̄}` in a unitary frame. -/
abbrev Curv (F : Type*) (n : ℕ) : Type _ := Fin n → Fin n → Fin n → Fin n → F

variable {F : Type*} [Field F] {n : ℕ}

/-- The variable `ηⁱ`. -/
def eta (i : Fin n) : Poly F n := X (Sum.inl i)

/-- The variable `η̄ⁱ`. -/
def etaBar (i : Fin n) : Poly F n := X (Sum.inr i)

/-- `γ = g_{k l̄} ηᵏ η̄ˡ = Σ ηᵏ η̄ᵏ`. -/
def gamma : Poly F n := ∑ k, eta k * etaBar k

/-- `Q₂ P = ½ Σ R^{āb̄}_{l̄q̄} η̄ˡ η̄^q ∂_{η̄ᵃ} ∂_{η̄ᵇ} P`. -/
def Q2 (R : Curv F n) (P : Poly F n) : Poly F n :=
  ∑ a, ∑ b, ∑ l, ∑ q, C (R a b l q / 2) * etaBar l * etaBar q *
    pderiv (Sum.inr a) (pderiv (Sum.inr b) P)

/-- The Hara–Sako recurrence in Karabegov's form: `P 0 = 1` and
`(m − ℏ Q₂) P m = ℏ γ P (m − 1)` for `m ≥ 1`. -/
def StarRec (R : Curv F n) (ℏ : F) (P : ℕ → Poly F n) : Prop :=
  P 0 = 1 ∧ ∀ m : ℕ, ((m : F) + 1) • P (m + 1) - ℏ • Q2 R (P (m + 1)) = ℏ • (gamma * P m)

/-- `ℏ` is generic for the curvature scale `κ`: `1 − ℏ κ q ≠ 0` for every rational `q`.
This holds when `ℏ` is a formal parameter, and it makes every denominator below nonzero. -/
def Generic (ℏ κ : F) : Prop := ∀ q : ℚ, 1 - ℏ * κ * q ≠ 0

/-- The recurrence determines `P` as soon as every `m − ℏ Q₂` (`m ≥ 1`) is injective,
which is the case for a formal parameter `ℏ`. -/
theorem StarRec.unique {R : Curv F n} {ℏ : F} {P P' : ℕ → Poly F n}
    (hinj : ∀ m : ℕ, Function.Injective fun p : Poly F n => ((m : F) + 1) • p - ℏ • Q2 R p)
    (hP : StarRec R ℏ P) (hP' : StarRec R ℏ P') : P = P' := by
  funext m
  induction m with
  | zero => rw [hP.1, hP'.1]
  | succ m ih => exact hinj m (by simp only [hP.2 m, hP'.2 m, ih])

/-- `Q₂` commutes with multiplication by constants. -/
theorem Q2_C_mul (R : Curv F n) (c : F) (P : Poly F n) : Q2 R (C c * P) = C c * Q2 R P := by
  simp only [Q2, pderiv_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun q _ => by ring

/-! ## Young diagrams -/

/-- The content `j − i·a/2` of the box in row `i` and column `j` (both counted from `0`). -/
def content (a : ℕ) (c : ℕ × ℕ) : F := (c.2 : F) - (c.1 : F) * a / 2

/-- The box factor `∏_{boxes} (1 − ℏ κ · content)`. -/
def boxProd (ℏ κ : F) (a : ℕ) (μ : YoungDiagram) : F :=
  ∏ c ∈ μ.cells, (1 - ℏ * κ * content a c)

/-- `λ_a(μ) = 2 Σ_{boxes} content = Σ_i m_i (m_i − 1 − (i − 1) a)`. -/
def eig (a : ℕ) (μ : YoungDiagram) : F := 2 * ∑ c ∈ μ.cells, content a c

/-- The box formula `P m = Σ_{|μ| = m} ℏ^m K_μ / ∏_{boxes of μ} (1 − ℏ κ · content)`. -/
def boxSeries (ℏ κ : F) (a : ℕ) (K : YoungDiagram → Poly F n) (m : ℕ) : Poly F n :=
  ∑ᶠ (μ : YoungDiagram) (_ : μ.cells.card = m), (ℏ ^ m / boxProd ℏ κ a μ) • K μ

/-! ## Names used in the statement of the main theorem -/

/-- `γ = Σ ηᵏ η̄ᵏ`. -/
abbrev γ : Poly F n := gamma

/-- `Q₂ = ½ Σ R^{āb̄}_{l̄q̄} η̄ˡ η̄^q ∂_{η̄ᵃ} ∂_{η̄ᵇ}`. -/
abbrev Q₂ (R : Curv F n) (P : Poly F n) : Poly F n := Q2 R P

/-- The number of boxes `|μ|` of a Young diagram. -/
abbrev size (μ : YoungDiagram) : ℕ := μ.cells.card

/-- `ν = μ + □`: the diagram `ν` is `μ` with one box added. -/
abbrev AddsOneBox (μ ν : YoungDiagram) : Prop := μ ≤ ν ∧ size ν = size μ + 1

/-- The Hara–Sako recurrence: `P 0 = 1` and `(m − ℏ Q₂) P m = ℏ γ P (m − 1)` for `m ≥ 1`. -/
def HaraSako (R : Curv F n) (ℏ : F) (P : ℕ → Poly F n) : Prop :=
  P 0 = 1 ∧ ∀ m : ℕ, 1 ≤ m → (m : F) • P m - ℏ • Q₂ R (P m) = ℏ • (γ * P (m - 1))

end LeanTargetTheorem
