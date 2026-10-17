/-
Supplementary material for "Non-acceleration of the heavy-ball method in 1D".
Paper-faithful formalization of Sections 2, 3, 4, and Appendix B

Version information available in the manifest.
-/

/-
Supplementary material for "Non-acceleration of the heavy-ball method in 1D".
Part 1 of 4: the preliminaries of Section 2, used by Sections 3 and 4.
-/

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Section 2: the function class, interpolation, and cycles

* `F μ L E` is `F_{μ,L}(E)` for a real inner product space `E`. Section 3 identifies `ℝ² ≅ ℂ`, so
  `F μ L ℂ` is `F_{μ,L}(ℝ²)`, with the real inner product `⟪w, z⟫ = Re(z w̄)`; `F μ L ℝ` is
  `F_{μ,L}(ℝ)`.
* `hb` gives the iterates of (HB). `Ωcv L` is `Ω_cv(Q_{μ,L})`, defined by its closed form (1), as
  the paper uses it. `Cycles` is Definition 2.1. `ΩKcycle` and `Ωcycle` are `Ω^{(d)}_{K-cycle}`
  and `Ω^{(d)}_{Cycle}`.
* `theorem_2_2` is Theorem 2.2 (Taylor et al., 2017) for finite index sets, both directions. It is
  proved here, not assumed. Sufficiency uses the Moreau envelope of a polyhedral function.
* `theorem_2_2_1d` is its one-dimensional form: consecutive sorted points suffice.
* `cycles_of_grad` and `grad_of_cycles` are equation (5).

Nothing is assumed in this file.
-/

noncomputable section

open Real Filter Topology Set Asymptotics
open scoped RealInnerProductSpace

namespace HeavyBall

/-! ## The function class and the necessity part of Theorem 2.2 -/

/-- `F_{μ,L}(E)`: differentiable functions on a real inner product space `E` that are `μ`-strongly
convex and `L`-smooth, in the first-order form of Section 2. For `E = ℝ` and `E = ℂ ≅ ℝ²` this is
`F_{μ,L}(ℝ)` and `F_{μ,L}(ℝ²)`. -/
def F (μ L : ℝ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    Set (E → ℝ) :=
  {f | Differentiable ℝ f ∧ ∀ x y : E,
    f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y ∧
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2}

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- `⟪v - μ a, b - a⟫ + μ/2 ‖b‖² - μ/2 ‖a‖² = ⟪v, b - a⟫ + μ/2 ‖b - a‖²`. -/
lemma shift_identity (μ : ℝ) (v a b : E) :
    ⟪v - μ • a, b - a⟫ + μ / 2 * ‖b‖ ^ 2 - μ / 2 * ‖a‖ ^ 2 =
      ⟪v, b - a⟫ + μ / 2 * ‖b - a‖ ^ 2 := by
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_self_eq_norm_sq,
    norm_sub_sq_real, real_inner_comm a b]
  ring

/-- A two-sided quadratic bound on the first-order remainder gives the gradient. -/
lemma hasGradientAt_of_sq_bound {e : E → ℝ} {v z : E} (C : ℝ)
    (h : ∀ y, |e y - e z - ⟪v, y - z⟫| ≤ C * ‖y - z‖ ^ 2) : HasGradientAt e v z := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  refine IsBigO.trans_isLittleO (g := fun w : E => ‖w‖ ^ 2) ?_ (isLittleO_norm_pow_id one_lt_two)
  refine IsBigO.of_bound C (Eventually.of_forall fun w => ?_)
  have := h (z + w)
  rw [add_sub_cancel_left] at this
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖w‖)] using this

/-- A function with a two-sided quadratic sandwich around `G` is in `F_{μ,L}` with gradient `G`. -/
lemma mem_F_of_sandwich {μ L : ℝ} (hμ : 0 ≤ μ) (hμL : μ ≤ L) {f : E → ℝ} {G : E → E}
    (h : ∀ z y, f z + ⟪G z, y - z⟫ + μ / 2 * ‖y - z‖ ^ 2 ≤ f y ∧
      f y ≤ f z + ⟪G z, y - z⟫ + L / 2 * ‖y - z‖ ^ 2) :
    f ∈ F μ L E ∧ ∀ z, gradient f z = G z := by
  have hg : ∀ z, HasGradientAt f (G z) z := fun z =>
    hasGradientAt_of_sq_bound (L / 2) fun y => by
      obtain ⟨h1, h2⟩ := h z y
      have a1 : 0 ≤ μ / 2 * ‖y - z‖ ^ 2 := by positivity
      have a2 : 0 ≤ L / 2 * ‖y - z‖ ^ 2 := by
        have : 0 ≤ L := hμ.trans hμL
        positivity
      rw [abs_le]
      constructor <;> linarith
  have hgr : ∀ z, gradient f z = G z := fun z => (hg z).gradient
  refine ⟨⟨fun z => (hg z).differentiableAt, fun x y => ?_⟩, hgr⟩
  rw [hgr]
  exact h x y

/-- `x ↦ μ/2 ‖x‖²` belongs to `F_{μ,L}` when `0 ≤ μ ≤ L`. -/
lemma quad_mem_F {μ L : ℝ} (hμ : 0 ≤ μ) (hμL : μ ≤ L) :
    (fun x : E => μ / 2 * ‖x‖ ^ 2) ∈ F μ L E := by
  refine (mem_F_of_sandwich (G := fun x => μ • x) hμ hμL fun z y => ?_).1
  have e := shift_identity μ (μ • z) z y
  rw [sub_self, inner_zero_left] at e
  have : 0 ≤ (L - μ) / 2 * ‖y - z‖ ^ 2 := by
    have : 0 ≤ L - μ := sub_nonneg.2 hμL
    positivity
  constructor <;> nlinarith

/-- **Necessity in Theorem 2.2**, in normalized form: for `f ∈ F_{μ,L}`, with
`h = f - μ/2 ‖·‖²` and `G = ∇f - μ id`, we have
`h y + ⟪G y, x - y⟫ + ‖G x - G y‖² / (2 (L - μ)) ≤ h x`. -/
theorem F.interp {μ L : ℝ} (hμL : μ < L) {f : E → ℝ} (hf : f ∈ F μ L E) (x y : E) :
    (f y - μ / 2 * ‖y‖ ^ 2) + ⟪gradient f y - μ • y, x - y⟫ +
        1 / (2 * (L - μ)) * ‖(gradient f x - μ • x) - (gradient f y - μ • y)‖ ^ 2 ≤
      f x - μ / 2 * ‖x‖ ^ 2 := by
  have hℓ : 0 < L - μ := sub_pos.2 hμL
  obtain ⟨Gx, hGx⟩ : ∃ G, G = gradient f x - μ • x := ⟨_, rfl⟩
  obtain ⟨Gy, hGy⟩ : ∃ G, G = gradient f y - μ • y := ⟨_, rfl⟩
  rw [← hGx, ← hGy]
  obtain ⟨D, hD⟩ : ∃ D, D = Gx - Gy := ⟨_, rfl⟩
  rw [← hD]
  obtain ⟨z, hz⟩ : ∃ z, z = x - (L - μ)⁻¹ • D := ⟨_, rfl⟩
  have h1 := (hf.2 y z).1
  have h2 := (hf.2 x z).2
  have e1 := shift_identity μ (gradient f y) y z
  have e2 := shift_identity μ (gradient f x) x z
  rw [← hGy] at e1
  rw [← hGx] at e2
  have hzx : z - x = -((L - μ)⁻¹ • D) := by rw [hz]; abel
  have hzy : z - y = (x - y) - (L - μ)⁻¹ • D := by rw [hz]; abel
  have k1 : ⟪Gy, z - y⟫ = ⟪Gy, x - y⟫ - (L - μ)⁻¹ * ⟪Gy, D⟫ := by
    rw [hzy, inner_sub_right, real_inner_smul_right]
  have k2 : ⟪Gx, z - x⟫ = -((L - μ)⁻¹ * ⟪Gx, D⟫) := by
    rw [hzx, inner_neg_right, real_inner_smul_right]
  have k3 : ‖z - x‖ ^ 2 = ((L - μ)⁻¹) ^ 2 * ‖D‖ ^ 2 := by
    rw [hzx, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have k4 : ⟪Gx, D⟫ - ⟪Gy, D⟫ = ‖D‖ ^ 2 := by
    rw [← inner_sub_left, ← hD, real_inner_self_eq_norm_sq]
  have A1 : (f y - μ / 2 * ‖y‖ ^ 2) + ⟪Gy, z - y⟫ ≤ f z - μ / 2 * ‖z‖ ^ 2 := by linarith
  have A2 : f z - μ / 2 * ‖z‖ ^ 2 ≤
      (f x - μ / 2 * ‖x‖ ^ 2) + ⟪Gx, z - x⟫ + (L - μ) / 2 * ‖z - x‖ ^ 2 := by linarith
  rw [k1] at A1
  rw [k2, k3] at A2
  have k5 : (L - μ) / 2 * ((L - μ)⁻¹ ^ 2 * ‖D‖ ^ 2) = (L - μ)⁻¹ / 2 * ‖D‖ ^ 2 := by
    field_simp
  have k6 : 1 / (2 * (L - μ)) * ‖D‖ ^ 2 = (L - μ)⁻¹ / 2 * ‖D‖ ^ 2 := by
    rw [one_div, mul_inv]; ring
  have k7 : (L - μ)⁻¹ * ⟪Gx, D⟫ = (L - μ)⁻¹ * ⟪Gy, D⟫ + (L - μ)⁻¹ * ‖D‖ ^ 2 := by
    rw [← mul_add, ← k4]; ring
  rw [k6]
  linarith [k5, k7]

omit [CompleteSpace E] in
/-- The interpolation inequality of Theorem 2.2 is equivalent to its normalized form. -/
lemma taylor_iff {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L) (xi xj gi gj : E) (fi fj : ℝ) :
    1 / (2 * (1 - μ / L)) * (1 / L * ‖gi - gj‖ ^ 2 + μ * ‖xi - xj‖ ^ 2 -
        2 * μ / L * ⟪gi - gj, xi - xj⟫) ≤ fi - fj - ⟪gj, xi - xj⟫ ↔
      (fj - μ / 2 * ‖xj‖ ^ 2) + ⟪gj - μ • xj, xi - xj⟫ +
        1 / (2 * (L - μ)) * ‖(gi - μ • xi) - (gj - μ • xj)‖ ^ 2 ≤ fi - μ / 2 * ‖xi‖ ^ 2 := by
  have hL : 0 < L := hμ.trans hμL
  have hℓ : 0 < L - μ := sub_pos.2 hμL
  have hT : 1 / (2 * (1 - μ / L)) * (1 / L * ‖gi - gj‖ ^ 2 + μ * ‖xi - xj‖ ^ 2 -
        2 * μ / L * ⟪gi - gj, xi - xj⟫) =
      1 / (2 * (L - μ)) * ‖(gi - μ • xi) - (gj - μ • xj)‖ ^ 2 + μ / 2 * ‖xi - xj‖ ^ 2 := by
    have e : (gi - μ • xi) - (gj - μ • xj) = (gi - gj) - μ • (xi - xj) := by
      rw [smul_sub]; abel
    rw [e, norm_sub_sq_real (gi - gj) (μ • (xi - xj)), real_inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]
    have h1 : (1 : ℝ) - μ / L = (L - μ) / L := by field_simp
    rw [h1]
    field_simp
    ring
  have hS := shift_identity μ gj xj xi
  rw [hT]
  constructor <;> intro h <;> linarith

end General

/-! ## Sufficiency in Theorem 2.2: a Moreau-envelope construction -/

section Sufficiency

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- Finite smooth convex interpolation with constant `1`: if
`fb j + ⟪gb j, x i - x j⟫ + ‖gb i - gb j‖²/2 ≤ fb i` for all `i, j`, there are `e` and `G` with
`0 ≤ e y - e z - ⟪G z, y - z⟫ ≤ ‖y - z‖²/2`, `e (x i) = fb i` and `G (x i) = gb i`. The function
`e` is the Moreau envelope of the polyhedral function `y ↦ max_j (c j + ⟪gb j, y - w j⟫)`. -/
theorem interp01 {ι : Type*} [Fintype ι] [Nonempty ι] (x gb : ι → E) (fb : ι → ℝ)
    (h : ∀ i j, fb j + ⟪gb j, x i - x j⟫ + 1 / 2 * ‖gb i - gb j‖ ^ 2 ≤ fb i) :
    ∃ e : E → ℝ, ∃ G : E → E,
      (∀ z y, e z + ⟪G z, y - z⟫ ≤ e y ∧ e y ≤ e z + ⟪G z, y - z⟫ + 1 / 2 * ‖y - z‖ ^ 2) ∧
      ∀ i, e (x i) = fb i ∧ G (x i) = gb i := by
  classical
  set w : ι → E := fun i => x i - gb i with hw
  set c : ι → ℝ := fun i => fb i - 1 / 2 * ‖gb i‖ ^ 2 with hc
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  set φ : E → ℝ := fun y => Finset.univ.sup' hne fun j => c j + ⟪gb j, y - w j⟫ with hφ
  have φ_ge : ∀ j y, c j + ⟪gb j, y - w j⟫ ≤ φ y := fun j y =>
    Finset.le_sup' (fun j => c j + ⟪gb j, y - w j⟫) (Finset.mem_univ j)
  have φ_w : ∀ i, φ (w i) = c i := by
    intro i
    apply le_antisymm
    · apply Finset.sup'_le
      intro j _
      have hij := h i j
      have e1 : w i - w j = (x i - x j) - (gb i - gb j) := by simp only [hw]; abel
      have e2 : ⟪gb j, gb i - gb j⟫ = ⟪gb i, gb j⟫ - ‖gb j‖ ^ 2 := by
        rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
      rw [norm_sub_sq_real] at hij
      show c j + ⟪gb j, w i - w j⟫ ≤ c i
      rw [e1, inner_sub_right, e2]
      simp only [hc]
      linarith
    · have := φ_ge i (w i)
      simpa using this
  have φ_conv : ∀ a b : E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      φ (a + t • (b - a)) ≤ (1 - t) * φ a + t * φ b := by
    intro a b t ht0 ht1
    apply Finset.sup'_le
    intro j _
    have h1 := mul_le_mul_of_nonneg_left (φ_ge j a) (sub_nonneg.2 ht1)
    have h2 := mul_le_mul_of_nonneg_left (φ_ge j b) ht0
    have e : a + t • (b - a) - w j = (1 - t) • (a - w j) + t • (b - w j) := by module
    have : c j + ⟪gb j, a + t • (b - a) - w j⟫ =
        (1 - t) * (c j + ⟪gb j, a - w j⟫) + t * (c j + ⟪gb j, b - w j⟫) := by
      rw [e, inner_add_right, real_inner_smul_right, real_inner_smul_right]; ring
    rw [this]
    linarith
  have φ_cont : Continuous φ := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    exact ContinuousAt.finset_sup'_apply hne fun j _ => by fun_prop
  -- existence of the proximal point
  have prox : ∀ z : E, ∃ P : E, ∀ y, φ P + ⟪z - P, y - P⟫ ≤ φ y := by
    intro z
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_sup' hne fun j => c j + ⟪gb j, z - w j⟫
    have hφz : ∀ y, φ z + ⟪gb j₀, y - z⟫ ≤ φ y := by
      intro y
      have h1 := φ_ge j₀ y
      have e : ⟪gb j₀, y - w j₀⟫ = ⟪gb j₀, z - w j₀⟫ + ⟪gb j₀, y - z⟫ := by
        rw [← inner_add_right]; congr 1; abel
      have hz : φ z = c j₀ + ⟪gb j₀, z - w j₀⟫ := hj₀
      linarith
    set R := 2 * ‖gb j₀‖ with hR
    have hcpt : IsCompact (Metric.closedBall z R) := isCompact_closedBall z R
    have hzmem : z ∈ Metric.closedBall z R := Metric.mem_closedBall_self (by positivity)
    obtain ⟨P, -, hPmin⟩ := hcpt.exists_isMinOn ⟨z, hzmem⟩
      (f := fun y => φ y + 1 / 2 * ‖z - y‖ ^ 2)
      (φ_cont.add (continuous_const.mul
        ((continuous_const.sub continuous_id).norm.pow 2))).continuousOn
    rw [isMinOn_iff] at hPmin
    have hglob : ∀ y, φ P + 1 / 2 * ‖z - P‖ ^ 2 ≤ φ y + 1 / 2 * ‖z - y‖ ^ 2 := by
      intro y
      by_cases hy : y ∈ Metric.closedBall z R
      · exact hPmin y hy
      · have h1 : φ P + 1 / 2 * ‖z - P‖ ^ 2 ≤ φ z + 1 / 2 * ‖z - z‖ ^ 2 := hPmin z hzmem
        rw [sub_self, norm_zero] at h1
        have hy' : R < ‖y - z‖ := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hy
        have h2 := hφz y
        have h3 : -(‖gb j₀‖ * ‖y - z‖) ≤ ⟪gb j₀, y - z⟫ := by
          have := abs_real_inner_le_norm (gb j₀) (y - z)
          linarith [neg_abs_le ⟪gb j₀, y - z⟫]
        have h4 : ‖z - y‖ = ‖y - z‖ := norm_sub_rev z y
        have h5 : 0 ≤ ‖y - z‖ * (‖y - z‖ - 2 * ‖gb j₀‖) :=
          mul_nonneg (norm_nonneg _) (by linarith)
        rw [h4]
        nlinarith
    refine ⟨P, fun y => ?_⟩
    by_contra hcon
    push Not at hcon
    set d := φ P + ⟪z - P, y - P⟫ - φ y with hd
    have hd0 : 0 < d := by linarith
    set N := ‖y - P‖ ^ 2 with hN
    have hN0 : 0 ≤ N := by positivity
    set t := min 1 (d / (N + 1)) with ht
    have ht0 : 0 < t := lt_min one_pos (div_pos hd0 (by positivity))
    have ht1 : t ≤ 1 := min_le_left _ _
    have htN : t * N < d := by
      have h1 : t ≤ d / (N + 1) := min_le_right _ _
      have h2 : t * (N + 1) ≤ d := by rwa [le_div_iff₀ (by positivity)] at h1
      nlinarith
    have hmin := hglob (P + t • (y - P))
    have hconv := φ_conv P y t ht0.le ht1
    have hexp : ‖z - (P + t • (y - P))‖ ^ 2 = ‖z - P‖ ^ 2 - 2 * t * ⟪z - P, y - P⟫ + t ^ 2 * N := by
      rw [show z - (P + t • (y - P)) = (z - P) - t • (y - P) by abel, norm_sub_sq_real,
        real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [hexp] at hmin
    have key : 0 < t * ((φ P + ⟪z - P, y - P⟫ - φ y) - 1 / 2 * (t * N)) :=
      mul_pos ht0 (by linarith)
    nlinarith
  -- uniqueness of the proximal point
  have prox_unique : ∀ z P P', (∀ y, φ P + ⟪z - P, y - P⟫ ≤ φ y) →
      (∀ y, φ P' + ⟪z - P', y - P'⟫ ≤ φ y) → P = P' := by
    intro z P P' h1 h2
    have a1 := h1 P'
    have a2 := h2 P
    have e : ⟪z - P, P' - P⟫ + ⟪z - P', P - P'⟫ = ‖P' - P‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      have : P - P' = -(P' - P) := by abel
      rw [this, inner_neg_right, ← sub_eq_add_neg, ← inner_sub_left]
      congr 1
      abel
    have hle : ‖P' - P‖ ^ 2 ≤ 0 := by linarith
    have : ‖P' - P‖ = 0 := by
      have := sq_nonneg ‖P' - P‖
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hle this)
    exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm
  choose P hP using prox
  refine ⟨fun z => φ (P z) + 1 / 2 * ‖z - P z‖ ^ 2, fun z => z - P z, fun z y => ⟨?_, ?_⟩,
    fun i => ?_⟩
  · -- lower bound
    have h1 := hP z (P y)
    have e1 : P y - P z = (y - z) + ((z - P z) - (y - P y)) := by abel
    rw [e1, inner_add_right] at h1
    have e2 : ⟪z - P z, (z - P z) - (y - P y)⟫ = ‖z - P z‖ ^ 2 - ⟪z - P z, y - P y⟫ := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
    have e3 := norm_sub_sq_real (y - P y) (z - P z)
    have e4 : ⟪y - P y, z - P z⟫ = ⟪z - P z, y - P y⟫ := real_inner_comm _ _
    have e5 := sq_nonneg ‖(y - P y) - (z - P z)‖
    show φ (P z) + 1 / 2 * ‖z - P z‖ ^ 2 + ⟪z - P z, y - z⟫ ≤ φ (P y) + 1 / 2 * ‖y - P y‖ ^ 2
    linarith
  · -- upper bound
    have h2 := hP y (P z)
    have n1 := norm_add_sq_real (y - P y) (P y - P z)
    have n2 := norm_add_sq_real (y - z) (z - P z)
    rw [show y - P y + (P y - P z) = y - P z by abel] at n1
    rw [show y - z + (z - P z) = y - P z by abel] at n2
    have e7 : ⟪y - P y, P z - P y⟫ = -⟪y - P y, P y - P z⟫ := by
      rw [← inner_neg_right, neg_sub]
    have e8 : ⟪y - z, z - P z⟫ = ⟪z - P z, y - z⟫ := real_inner_comm _ _
    have e9 := sq_nonneg ‖P y - P z‖
    show φ (P y) + 1 / 2 * ‖y - P y‖ ^ 2 ≤
      φ (P z) + 1 / 2 * ‖z - P z‖ ^ 2 + ⟪z - P z, y - z⟫ + 1 / 2 * ‖y - z‖ ^ 2
    linarith
  · -- the data points
    have hwi : ∀ y, φ (w i) + ⟪x i - w i, y - w i⟫ ≤ φ y := by
      intro y
      have := φ_ge i y
      rw [φ_w i, show x i - w i = gb i by simp only [hw]; abel]
      exact this
    have hPi : P (x i) = w i := prox_unique (x i) _ _ (hP (x i)) hwi
    refine ⟨?_, ?_⟩
    · show φ (P (x i)) + 1 / 2 * ‖x i - P (x i)‖ ^ 2 = fb i
      rw [hPi, φ_w i, show x i - w i = gb i by simp only [hw]; abel]
      simp only [hc]
      ring
    · show x i - P (x i) = gb i
      rw [hPi]
      simp only [hw]
      abel

/-- **Sufficiency in Theorem 2.2**, in normalized form, for a finite index set: data satisfying the
normalized interpolation inequalities are interpolated by some `f ∈ F_{μ,L}(E)`. -/
theorem interp_sufficient {ι : Type*} [Fintype ι] {μ L : ℝ} (hμ : 0 ≤ μ) (hμL : μ < L)
    (x g : ι → E) (fv : ι → ℝ)
    (h : ∀ i j, (fv j - μ / 2 * ‖x j‖ ^ 2) + ⟪g j - μ • x j, x i - x j⟫ +
        1 / (2 * (L - μ)) * ‖(g i - μ • x i) - (g j - μ • x j)‖ ^ 2 ≤ fv i - μ / 2 * ‖x i‖ ^ 2) :
    ∃ f ∈ F μ L E, ∀ i, f (x i) = fv i ∧ gradient f (x i) = g i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨_, quad_mem_F hμ hμL.le, fun i => (IsEmpty.false i).elim⟩
  have hℓ : 0 < L - μ := sub_pos.2 hμL
  obtain ⟨e, G, he, hdata⟩ := interp01 x (fun i => (L - μ)⁻¹ • (g i - μ • x i))
    (fun i => (L - μ)⁻¹ * (fv i - μ / 2 * ‖x i‖ ^ 2)) (by
      intro i j
      have hij := mul_le_mul_of_nonneg_left (h i j) (inv_nonneg.2 hℓ.le)
      rw [← smul_sub, real_inner_smul_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hℓ)]
      have : (L - μ)⁻¹ * (1 / (2 * (L - μ)) * ‖(g i - μ • x i) - (g j - μ • x j)‖ ^ 2) =
          1 / 2 * ((L - μ)⁻¹ * ‖(g i - μ • x i) - (g j - μ • x j)‖) ^ 2 := by
        field_simp
      nlinarith)
  obtain ⟨hF, hgrad⟩ := mem_F_of_sandwich (μ := μ) (L := L)
    (f := fun z => μ / 2 * ‖z‖ ^ 2 + (L - μ) * e z)
    (G := fun z => μ • z + (L - μ) • G z) hμ hμL.le (fun z y => by
      obtain ⟨h1, h2⟩ := he z y
      have s := shift_identity μ (μ • z) z y
      rw [sub_self, inner_zero_left] at s
      have i1 : ⟪μ • z + (L - μ) • G z, y - z⟫ = ⟪μ • z, y - z⟫ + (L - μ) * ⟪G z, y - z⟫ := by
        rw [inner_add_left, real_inner_smul_left (G z)]
      rw [i1]
      have m1 := mul_le_mul_of_nonneg_left h1 hℓ.le
      have m2 := mul_le_mul_of_nonneg_left h2 hℓ.le
      constructor <;> nlinarith)
  refine ⟨_, hF, fun i => ⟨?_, ?_⟩⟩
  · simp only [(hdata i).1]
    field_simp
    ring
  · rw [hgrad, (hdata i).2, smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]
    abel

/-- **Theorem 2.2** (Taylor et al., 2017, Thm. 4), for a finite index set: there is
`f ∈ F_{μ,L}(E)` with `∇f(xᵢ) = gᵢ` iff there are function values `fᵢ` satisfying the interpolation
inequalities. -/
theorem theorem_2_2 {ι : Type*} [Fintype ι] {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L) (x g : ι → E) :
    (∃ f ∈ F μ L E, ∀ i, gradient f (x i) = g i) ↔
      ∃ fv : ι → ℝ, ∀ i j, 1 / (2 * (1 - μ / L)) * (1 / L * ‖g i - g j‖ ^ 2 +
        μ * ‖x i - x j‖ ^ 2 - 2 * μ / L * ⟪g i - g j, x i - x j⟫) ≤
          fv i - fv j - ⟪g j, x i - x j⟫ := by
  constructor
  · rintro ⟨f, hf, hg⟩
    refine ⟨fun i => f (x i), fun i j => (taylor_iff hμ hμL _ _ _ _ _ _).2 ?_⟩
    have := F.interp hμL hf (x i) (x j)
    rwa [hg i, hg j] at this
  · rintro ⟨fv, hfv⟩
    obtain ⟨f, hf, hfx⟩ := interp_sufficient hμ.le hμL x g fv fun i j =>
      (taylor_iff hμ hμL _ _ _ _ _ _).1 (hfv i j)
    exact ⟨f, hf, fun i => (hfx i).2⟩

end Sufficiency

/-! ## The one-dimensional case of Theorem 2.2 -/

section OneDim

lemma real_inner_eq_mul (a b : ℝ) : ⟪a, b⟫ = a * b := by
  simp [mul_comm]

lemma norm_sq_real (a : ℝ) : ‖a‖ ^ 2 = a ^ 2 := by
  rw [Real.norm_eq_abs, sq_abs]

/-- Tangent lines lie below a function with monotone derivative. -/
lemma tangent_le_of_monotone {φ φ' : ℝ → ℝ} (hd : ∀ x, HasDerivAt φ (φ' x) x)
    (hm : Monotone φ') (a b : ℝ) : φ a + φ' a * (b - a) ≤ φ b := by
  have hc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨c, hc', hcd⟩ := exists_hasDerivAt_eq_slope φ φ' hab hc.continuousOn
      (fun x _ => hd x)
    have h1 : φ' a ≤ φ' c := hm hc'.1.le
    have h2 : φ b - φ a = φ' c * (b - a) := by
      rw [hcd]; field_simp [sub_ne_zero.2 hab.ne']
    linarith [mul_nonneg (sub_nonneg.2 h1) (sub_pos.2 hab).le]
  · simp
  · obtain ⟨c, hc', hcd⟩ := exists_hasDerivAt_eq_slope φ φ' hab hc.continuousOn
      (fun x _ => hd x)
    have h1 : φ' c ≤ φ' a := hm hc'.2.le
    have h2 : φ a - φ b = φ' c * (a - b) := by
      rw [hcd]; field_simp [sub_ne_zero.2 hab.ne']
    linarith [mul_nonneg (sub_nonneg.2 h1) (sub_pos.2 hab).le]

/-- **Sufficiency in Theorem 2.2 for `d = 1`**: if all slopes between distinct points lie in
`[μ, L]`, the data are interpolated by some `f ∈ F_{μ,L}(ℝ)`. The derivative of `f` is the
piecewise linear function `x ↦ μ x + max_i min(hᵢ, hᵢ + (L - μ)(x - yᵢ))`. -/
theorem interp_1d {ι : Type*} [Fintype ι] {μ L : ℝ} (hμ : 0 ≤ μ) (hμL : μ < L) (y g : ι → ℝ)
    (hy : Function.Injective y)
    (hs : ∀ i j, y i < y j → μ * (y j - y i) ≤ g j - g i ∧ g j - g i ≤ L * (y j - y i)) :
    ∃ f ∈ F μ L ℝ, ∀ i, gradient f (y i) = g i := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨_, quad_mem_F hμ hμL.le, fun i => (IsEmpty.false i).elim⟩
  have hℓ : 0 < L - μ := sub_pos.2 hμL
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  set H : ℝ → ℝ := fun x => Finset.univ.sup' hne fun i =>
    min (g i - μ * y i) (g i - μ * y i + (L - μ) * (x - y i)) with hH
  have H_mono : Monotone H := by
    intro a b hab
    apply Finset.sup'_le
    intro i _
    refine le_trans ?_ (Finset.le_sup' (fun i => min (g i - μ * y i)
      (g i - μ * y i + (L - μ) * (b - y i))) (Finset.mem_univ i))
    exact min_le_min le_rfl (by nlinarith)
  have H_lip : ∀ a b, a ≤ b → H b ≤ H a + (L - μ) * (b - a) := by
    intro a b hab
    apply Finset.sup'_le
    intro i _
    have hle := Finset.le_sup' (fun i => min (g i - μ * y i)
      (g i - μ * y i + (L - μ) * (a - y i))) (Finset.mem_univ i)
    have key : min (g i - μ * y i) (g i - μ * y i + (L - μ) * (b - y i)) ≤
        min (g i - μ * y i) (g i - μ * y i + (L - μ) * (a - y i)) + (L - μ) * (b - a) := by
      rcases le_total (g i - μ * y i) (g i - μ * y i + (L - μ) * (a - y i)) with h1 | h1
      · rw [min_eq_left h1]
        have := min_le_left (g i - μ * y i) (g i - μ * y i + (L - μ) * (b - y i))
        nlinarith
      · rw [min_eq_right h1]
        have := min_le_right (g i - μ * y i) (g i - μ * y i + (L - μ) * (b - y i))
        nlinarith
    exact key.trans (by linarith)
  have H_at : ∀ j, H (y j) = g j - μ * y j := by
    intro j
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      rcases lt_trichotomy (y i) (y j) with hij | hij | hij
      · have := (hs i j hij).1
        exact (min_le_left _ _).trans (by linarith)
      · rw [hy hij]; exact min_le_left _ _
      · have := (hs j i hij).2
        exact (min_le_right _ _).trans (by nlinarith)
    · have := Finset.le_sup' (fun i => min (g i - μ * y i)
        (g i - μ * y i + (L - μ) * (y j - y i))) (Finset.mem_univ j)
      simpa using this
  have H_cont : Continuous H := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    exact ContinuousAt.finset_sup'_apply hne fun i _ => by fun_prop
  set gg : ℝ → ℝ := fun x => μ * x + H x with hgg
  have gg_cont : Continuous gg := by fun_prop
  set f : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, gg s with hf
  have hfd : ∀ x, HasDerivAt f (gg x) x := fun x =>
    (gg_cont.integral_hasStrictDerivAt 0 x).hasDerivAt
  have low : ∀ a b, f a + gg a * (b - a) + μ / 2 * (b - a) ^ 2 ≤ f b := by
    intro a b
    have hd : ∀ x, HasDerivAt (fun x => f x - μ / 2 * x ^ 2) (H x) x := fun x =>
      ((hfd x).sub ((hasDerivAt_pow 2 x).const_mul (μ / 2))).congr_deriv (by
        simp only [hgg]; push_cast; ring)
    have := tangent_le_of_monotone hd H_mono a b
    simp only [hgg] at this ⊢
    linarith
  have up : ∀ a b, f b ≤ f a + gg a * (b - a) + L / 2 * (b - a) ^ 2 := by
    intro a b
    have hd : ∀ x, HasDerivAt (fun x => L / 2 * x ^ 2 - f x) ((L - μ) * x - H x) x := fun x =>
      (((hasDerivAt_pow 2 x).const_mul (L / 2)).sub (hfd x)).congr_deriv (by
        simp only [hgg]; push_cast; ring)
    have hm : Monotone fun x => (L - μ) * x - H x := by
      intro u v huv
      have := H_lip u v huv
      simp only
      linarith
    have := tangent_le_of_monotone hd hm a b
    simp only [hgg] at this ⊢
    linarith
  obtain ⟨hF, hgrad⟩ := mem_F_of_sandwich (E := ℝ) (f := f) (G := gg) hμ hμL.le fun z w => by
    rw [real_inner_eq_mul, norm_sq_real]
    exact ⟨low z w, up z w⟩
  refine ⟨f, hF, fun i => ?_⟩
  rw [hgrad]
  simp only [hgg, H_at]
  ring

/-- **Necessity in Theorem 2.2 for `d = 1`**: slopes of `∇f` lie in `[μ, L]`. -/
theorem F.slope_1d {μ L : ℝ} {f : ℝ → ℝ} (hf : f ∈ F μ L ℝ) {a b : ℝ} (hab : a < b) :
    μ * (b - a) ≤ gradient f b - gradient f a ∧ gradient f b - gradient f a ≤ L * (b - a) := by
  obtain ⟨h1, h2⟩ := hf.2 a b
  obtain ⟨h3, h4⟩ := hf.2 b a
  rw [real_inner_eq_mul, norm_sq_real] at h1 h2 h3 h4
  have hba : 0 < b - a := sub_pos.2 hab
  constructor
  · have : μ * (b - a) * (b - a) ≤ (gradient f b - gradient f a) * (b - a) := by nlinarith
    exact le_of_mul_le_mul_right this hba
  · have : (gradient f b - gradient f a) * (b - a) ≤ L * (b - a) * (b - a) := by nlinarith
    exact le_of_mul_le_mul_right this hba

/-- Slope bounds between consecutive sorted points give slope bounds between all points. -/
lemma slopes_of_consecutive {ι : Type*} [Fintype ι] (y g : ι → ℝ) (c₁ c₂ : ℝ)
    (h : ∀ i j, y i < y j → (∀ k, ¬(y i < y k ∧ y k < y j)) →
      c₁ * (y j - y i) ≤ g j - g i ∧ g j - g i ≤ c₂ * (y j - y i)) :
    ∀ i j, y i < y j → c₁ * (y j - y i) ≤ g j - g i ∧ g j - g i ≤ c₂ * (y j - y i) := by
  classical
  suffices H : ∀ n, ∀ i j, (Finset.univ.filter fun k => y i < y k ∧ y k < y j).card = n →
      y i < y j → c₁ * (y j - y i) ≤ g j - g i ∧ g j - g i ≤ c₂ * (y j - y i) from
    fun i j => H _ i j rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i j hn hij
    by_cases hk : ∃ k, y i < y k ∧ y k < y j
    · obtain ⟨k, hik, hkj⟩ := hk
      have sub1 : (Finset.univ.filter fun l => y i < y l ∧ y l < y k) ⊂
          (Finset.univ.filter fun l => y i < y l ∧ y l < y j) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨k, by simp [hik, hkj], by simp⟩
        · intro l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun ⟨a, b⟩ => ⟨a, b.trans hkj⟩
      have sub2 : (Finset.univ.filter fun l => y k < y l ∧ y l < y j) ⊂
          (Finset.univ.filter fun l => y i < y l ∧ y l < y j) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨k, by simp [hik, hkj], by simp⟩
        · intro l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun ⟨a, b⟩ => ⟨hik.trans a, b⟩
      obtain ⟨a1, a2⟩ := ih _ (hn ▸ Finset.card_lt_card sub1) i k rfl hik
      obtain ⟨b1, b2⟩ := ih _ (hn ▸ Finset.card_lt_card sub2) k j rfl hkj
      constructor <;> linarith
    · push Not at hk
      exact h i j hij fun k ⟨a, b⟩ => absurd b (not_lt.2 (hk k a))

/-- **Theorem 2.2 for `d = 1`**: it is enough to consider consecutive sorted points and require
their slopes to lie in `[μ, L]`. -/
theorem theorem_2_2_1d {ι : Type*} [Fintype ι] {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L)
    (y g : ι → ℝ) (hy : Function.Injective y) :
    (∃ f ∈ F μ L ℝ, ∀ i, gradient f (y i) = g i) ↔
      ∀ i j, y i < y j → (∀ k, ¬(y i < y k ∧ y k < y j)) →
        μ ≤ (g j - g i) / (y j - y i) ∧ (g j - g i) / (y j - y i) ≤ L := by
  constructor
  · rintro ⟨f, hf, hg⟩ i j hij _
    have := F.slope_1d hf hij
    rw [hg i, hg j] at this
    have hpos : 0 < y j - y i := sub_pos.2 hij
    constructor
    · rw [le_div_iff₀ hpos]; linarith [this.1]
    · rw [div_le_iff₀ hpos]; linarith [this.2]
  · intro h
    refine interp_1d hμ.le hμL y g hy (slopes_of_consecutive y g μ L fun i j hij hc => ?_)
    have hpos : 0 < y j - y i := sub_pos.2 hij
    obtain ⟨h1, h2⟩ := h i j hij hc
    rw [le_div_iff₀ hpos] at h1
    rw [div_le_iff₀ hpos] at h2
    exact ⟨by linarith, by linarith⟩

end OneDim

/-! ## Heavy-ball iterates and cycles -/

section Cycles

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The iterates of (HB) with parameters `(γ, β)` on `f`, started from `(x₀, x₁)`. -/
def hb (γ β : ℝ) (f : E → ℝ) (x₀ x₁ : E) : ℕ → E
  | 0 => x₀
  | 1 => x₁
  | t + 2 => hb γ β f x₀ x₁ (t + 1) - γ • gradient f (hb γ β f x₀ x₁ (t + 1)) +
      β • (hb γ β f x₀ x₁ (t + 1) - hb γ β f x₀ x₁ t)

lemma hb_add_two (γ β : ℝ) (f : E → ℝ) (x₀ x₁ : E) (t : ℕ) :
    hb γ β f x₀ x₁ (t + 2) = hb γ β f x₀ x₁ (t + 1) - γ • gradient f (hb γ β f x₀ x₁ (t + 1)) +
      β • (hb γ β f x₀ x₁ (t + 1) - hb γ β f x₀ x₁ t) := rfl

/-- `Ω_cv(Q_{μ,L})`, the parameters `(γ, β)` for which (HB) converges on all of `Q_{μ,L}`, in the
closed form (1) (Polyak, 1964). It does not depend on `μ`. -/
def Ωcv (L : ℝ) : Set (ℝ × ℝ) := {p | |p.2| < 1 ∧ 0 < p.1 ∧ p.1 < 2 * (1 + p.2) / L}

/-- **Definition 2.1** (cycle). `(HB)_{γ,β}` run on `f` cycles over the points
`z 0, …, z (K - 1)`: `(γ, β) ∈ Ω_cv(Q_{μ,L})`, the points are not all equal, the iterates from some
`(x₀, x₁)` satisfy `x_t = z (t mod K)`, and `K` is the minimal period of the iterates. -/
def Cycles (L γ β : ℝ) (f : E → ℝ) (K : ℕ) (z : ℕ → E) : Prop :=
  (γ, β) ∈ Ωcv L ∧ (∃ i < K, ∃ j < K, z i ≠ z j) ∧
    ∃ x₀ x₁ : E, (∀ t, hb γ β f x₀ x₁ t = z (t % K)) ∧
      ∀ K', 0 < K' → (∀ t, hb γ β f x₀ x₁ (t + K') = hb γ β f x₀ x₁ t) → K ≤ K'

/-- `Ω^{(d)}_{K-cycle}`, with `ℝ^d` replaced by the real inner product space `E`. -/
def ΩKcycle (μ L : ℝ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : ℕ) : Set (ℝ × ℝ) :=
  {p | ∃ f ∈ F μ L E, ∃ z : ℕ → E, Cycles L p.1 p.2 f K z}

/-- `Ω^{(d)}_{Cycle} = ⋃_{K ≥ 3} Ω^{(d)}_{K-cycle}`, with `ℝ^d` replaced by `E`. -/
def Ωcycle (μ L : ℝ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    Set (ℝ × ℝ) :=
  ⋃ K ≥ 3, ΩKcycle μ L E K

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma periodic_mod {K : ℕ} {z : ℕ → E} (hper : ∀ t, z (t + K) = z t) (t : ℕ) : z (t % K) = z t := by
  have h : ∀ q r, z (r + K * q) = z r := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, ← add_assoc, hper, ih]
  conv_rhs => rw [← Nat.mod_add_div t K]
  rw [h]

/-- Equation (5): (HB) follows a `K`-periodic sequence `z` of distinct points iff `∇f` takes the
values `((1 + β) z_t - z_{t+1} - β z_{t-1}) / γ` along it. This is the "if" direction. -/
lemma cycles_of_grad {L γ β : ℝ} {f : E → ℝ} {K : ℕ} (hK : 2 ≤ K) {z : ℕ → E}
    (hp : (γ, β) ∈ Ωcv L) (hper : ∀ t, z (t + K) = z t)
    (hinj : ∀ i < K, ∀ j < K, z i = z j → i = j)
    (hg : ∀ t, gradient f (z (t + 1)) = γ⁻¹ • ((1 + β) • z (t + 1) - z (t + 2) - β • z t)) :
    Cycles L γ β f K z := by
  have hγ : γ ≠ 0 := hp.2.1.ne'
  have hz : ∀ t, hb γ β f (z 0) (z 1) t = z t ∧ hb γ β f (z 0) (z 1) (t + 1) = z (t + 1) := by
    intro t
    induction t with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [show n + 1 + 1 = n + 2 from rfl, hb_add_two, ih.1, ih.2, hg n, smul_smul,
        mul_inv_cancel₀ hγ, one_smul]
      module
  refine ⟨hp, ⟨0, by omega, 1, by omega, fun h => by
    have := hinj 0 (by omega) 1 (by omega) h
    omega⟩, z 0, z 1, fun t => by rw [periodic_mod hper, (hz t).1], fun K' hK' hper' => ?_⟩
  by_contra hlt
  push Not at hlt
  have h0 := hper' 0
  rw [zero_add, (hz K').1, (hz 0).1] at h0
  have := hinj K' hlt 0 (by omega) h0
  omega

/-- The "only if" direction of (5). -/
lemma grad_of_cycles {L γ β : ℝ} {f : E → ℝ} {K : ℕ} {z : ℕ → E}
    (hper : ∀ t, z (t + K) = z t) (h : Cycles L γ β f K z) (t : ℕ) :
    γ • gradient f (z (t + 1)) = (1 + β) • z (t + 1) - z (t + 2) - β • z t := by
  obtain ⟨-, -, x₀, x₁, hx, -⟩ := h
  have hz : ∀ t, hb γ β f x₀ x₁ t = z t := fun t => by rw [hx, periodic_mod hper]
  have := hb_add_two γ β f x₀ x₁ t
  rw [hz, hz, hz] at this
  rw [this]
  module

end Cycles

end HeavyBall

/-! Each line prints `[propext, Classical.choice, Quot.sound]`: no `sorry`, no further axioms. -/

#print axioms HeavyBall.theorem_2_2
#print axioms HeavyBall.theorem_2_2_1d
/-!
Supplementary material for "Non-acceleration of the heavy-ball method in 1D".
Part 2 of 4, Section 3: augmented regions and binding constraints

Points of `ℝ²` are complex numbers, as in Section 3.

* `M`, `Mhat`, `pm` and `qm` are the operators (2) and the numbers (3). `ϕ` is the residual (7).
  `ΩRoU μ L K m` is `Ω°_{K,m}`, `Ωaug` is `Ω_{aug-°}` and `ΩRoUcycle` is `Ω_{°-cycle}`.
* `mixed_condition`: equations (4)--(8).  The proof uses Parseval only as the formal statement that the cross-terms in (6) cancel after summing over `j`; this is exactly the orthogonality step used in the paper.
* Lemma 3.1. Equation (9) is `lemma_3_1`. The binding constraint is `lemma_3_1_binding` and
  `binding_unique`. The case `m > (K - 1)/2` is `lemma_3_1_reflect` and
  `lemma_3_1_binding_reflect`. `q_m > 0` and (i) ⟺ (ii) are `lemma_3_1_ii`. Strict inequalities
  and the interior are `lemma_3_1_strict` and `lemma_3_1_interior`.
* `theorem_2_3`: Theorem 2.3 (Goujaud et al., 2025b, Thm. 3.5), recovered as Lemma 3.1 with
  `m = 1`.
* `example_3_2`: Example 3.2.  The exclusion of ordered cycles is routed through `theorem_2_3` and the displayed minimum `ex_hGTD_min`, exactly as in the manuscript.

Nothing is assumed in this file.  Comments marked `PAPER STEP` identify the corresponding displayed step in Section 3.
-/

noncomputable section

open Real Filter Topology Set Asymptotics
open scoped RealInnerProductSpace ComplexConjugate

namespace HeavyBall

/-! ## Definitions -/

/-- `θ_K = 2π/K`. -/
def θ (K : ℕ) : ℝ := 2 * π / K

/-- `ω_K = e^{2πi/K}`. -/
def ω (K : ℕ) : ℂ := Complex.exp (2 * π * Complex.I / K)

/-- The unnormalized (HB) operator `M̂_m` of (2). -/
def Mhat (γ β : ℝ) (K m : ℕ) : ℂ := ((1 + β) - ω K ^ m - β * (ω K ^ m)⁻¹) / γ

/-- The normalized (HB) operator `M_m` of (2). -/
def M (μ L γ β : ℝ) (K m : ℕ) : ℂ :=
  ((1 + β - μ * γ) - ω K ^ m - β * (ω K ^ m)⁻¹) / ((L - μ) * γ)

/-- `p_m` of (3). -/
def pm (μ L γ β : ℝ) (K m : ℕ) : ℝ :=
  ((1 + β - μ * γ) - (1 + β) * Real.cos (m * θ K)) / ((L - μ) * γ)

/-- `q_m` of (3). -/
def qm (μ L γ β : ℝ) (K m : ℕ) : ℝ := (1 - β) * Real.sin (m * θ K) / ((L - μ) * γ)

/-- `A_m = p_m (1 - p_m) - q_m²`. -/
def Am (μ L γ β : ℝ) (K m : ℕ) : ℝ :=
  pm μ L γ β K m * (1 - pm μ L γ β K m) - qm μ L γ β K m ^ 2

/-- The residual `ϕ_{K,m}(Δ)` of (7). -/
def ϕ (μ L γ β : ℝ) (K m Δ : ℕ) : ℝ :=
  (conj (1 - M μ L γ β K m) * M μ L γ β K m * (ω K ^ (m * Δ) - 1)).re

/-- `U_K = {m ∈ {1, …, K - 1} : gcd(m, K) = 1}`. -/
def U (K : ℕ) : Set ℕ := {m | 1 ≤ m ∧ m < K ∧ Nat.Coprime m K}

/-- `Ω°_{K,m}`: the parameters in `Ω_cv(Q_{μ,L})` with which (HB) cycles over the `m`-jump `K`-th
roots of unity `1, ω^m, ω^{2m}, …` on `F_{μ,L}(ℝ²)`, where `ℝ² ≅ ℂ`. -/
def ΩRoU (μ L : ℝ) (K m : ℕ) : Set (ℝ × ℝ) :=
  {p | ∃ f ∈ F μ L ℂ, Cycles L p.1 p.2 f K fun t => ω K ^ (m * t)}

/-- `Ω_{aug-°} = ⋃_{K ≥ 3} ⋃_{m ∈ U_K} Ω°_{K,m}`. -/
def Ωaug (μ L : ℝ) : Set (ℝ × ℝ) := ⋃ K ≥ 3, ⋃ m ∈ U K, ΩRoU μ L K m

/-- `Ω_{°-cycle} = ⋃_{K ≥ 3} Ω_{K-°-cycle}`, where `Ω_{K-°-cycle} = Ω°_{K,1}`. -/
def ΩRoUcycle (μ L : ℝ) : Set (ℝ × ℝ) := ⋃ K ≥ 3, ΩRoU μ L K 1

/-! ## Roots of unity -/

lemma ω_pow (K n : ℕ) : ω K ^ n = Complex.exp (↑((n : ℝ) * θ K) * Complex.I) := by
  rw [ω, ← Complex.exp_nat_mul]
  congr 1
  simp only [θ]
  push_cast
  ring

lemma ω_pow_eq (K n : ℕ) :
    ω K ^ n = ↑(Real.cos (n * θ K)) + ↑(Real.sin (n * θ K)) * Complex.I := by
  rw [ω_pow, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma ω_pow_inv_eq (K n : ℕ) :
    (ω K ^ n)⁻¹ = ↑(Real.cos (n * θ K)) - ↑(Real.sin (n * θ K)) * Complex.I := by
  rw [ω_pow, ← Complex.exp_neg, ← neg_mul, ← Complex.ofReal_neg, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

lemma norm_ω_pow (K n : ℕ) : ‖ω K ^ n‖ = 1 := by
  rw [ω_pow, Complex.norm_exp_ofReal_mul_I]

lemma ω_pow_ne_zero (K n : ℕ) : ω K ^ n ≠ 0 := by
  intro h
  have := norm_ω_pow K n
  rw [h, norm_zero] at this
  exact zero_ne_one this

lemma ω_pow_self {K : ℕ} (hK : K ≠ 0) : ω K ^ K = 1 := by
  rw [ω, ← Complex.exp_nat_mul]
  have : (K : ℂ) * (2 * π * Complex.I / K) = 2 * π * Complex.I := by
    field_simp
  rw [this, Complex.exp_two_pi_mul_I]

lemma ω_pow_mul_self {K : ℕ} (hK : K ≠ 0) (a : ℕ) : ω K ^ (a * K) = 1 := by
  rw [mul_comm, pow_mul, ω_pow_self hK, one_pow]

lemma ω_primitive {K : ℕ} (hK : K ≠ 0) : IsPrimitiveRoot (ω K) K :=
  Complex.isPrimitiveRoot_exp K hK

/-- The points `ω^{m a}`, `a < K`, are distinct when `gcd(m, K) = 1`. -/
lemma ω_pow_inj {K m : ℕ} (hK : K ≠ 0) (hm : Nat.Coprime m K) {a b : ℕ} (ha : a < K)
    (hb : b < K) (h : ω K ^ (m * a) = ω K ^ (m * b)) : a = b := by
  have hp := (ω_primitive hK).pow_of_coprime m hm
  rw [pow_mul, pow_mul] at h
  exact hp.pow_inj ha hb h

/-! ## The operators `M`, `M̂` and the residual -/

lemma M_eq (μ L γ β : ℝ) (K m : ℕ) :
    M μ L γ β K m = ↑(pm μ L γ β K m) - ↑(qm μ L γ β K m) * Complex.I := by
  rw [M, ω_pow_inv_eq, ω_pow_eq, pm, qm]
  have hd : ((L : ℂ) - μ) * γ = ↑((L - μ) * γ) := by push_cast; ring
  rw [hd]
  apply Complex.ext <;>
    simp only [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im] <;>
    ring

lemma Mhat_eq {μ L γ β : ℝ} (hγ : γ ≠ 0) (hμL : μ ≠ L) (K m : ℕ) :
    Mhat γ β K m = ↑μ + ↑(L - μ) * M μ L γ β K m := by
  have h1 : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have h2 : (L : ℂ) - μ ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hμL.symm
  rw [Mhat, M]
  push_cast
  field_simp
  ring

lemma re_conj_mul (p q x y : ℝ) :
    (conj (1 - (↑p - ↑q * Complex.I)) * (↑p - ↑q * Complex.I) * (↑x + ↑y * Complex.I - 1)).re
      = (p * (1 - p) - q ^ 2) * (x - 1) + q * y := by
  simp [Complex.mul_re, Complex.mul_im]; ring

/-- The residual in real form: `ϕ(Δ) = A (cos(mΔθ) - 1) + q sin(mΔθ)`. -/
lemma ϕ_eq (μ L γ β : ℝ) (K m Δ : ℕ) :
    ϕ μ L γ β K m Δ = Am μ L γ β K m * (Real.cos ((m * Δ : ℕ) * θ K) - 1) +
      qm μ L γ β K m * Real.sin ((m * Δ : ℕ) * θ K) := by
  rw [ϕ, M_eq, ω_pow_eq, re_conj_mul, Am]

lemma residual_half (A q x : ℝ) :
    A * (Real.cos (2 * x) - 1) + q * Real.sin (2 * x) =
      -2 * (Real.sin x * (A * Real.sin x - q * Real.cos x)) := by
  rw [Real.cos_two_mul, Real.sin_two_mul]
  linear_combination (2 * A) * Real.sin_sq_add_cos_sq x

lemma prod_shift (A q x : ℝ) (k : ℕ) :
    Real.sin (x + k * π) * (A * Real.sin (x + k * π) - q * Real.cos (x + k * π)) =
      Real.sin x * (A * Real.sin x - q * Real.cos x) := by
  rw [Real.sin_add_nat_mul_pi, Real.cos_add_nat_mul_pi]
  have : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  linear_combination (Real.sin x * (A * Real.sin x - q * Real.cos x)) * this

/-- The residual in half-angle form, reduced modulo `K`: with `j = mΔ mod K` and `x = jπ/K`,
`ϕ(Δ) = -2 sin x (A sin x - q cos x)`. -/
lemma ϕ_half (μ L γ β : ℝ) {K : ℕ} (hK : K ≠ 0) (m Δ : ℕ) :
    ϕ μ L γ β K m Δ = -2 * (Real.sin ((m * Δ % K : ℕ) * π / K) *
      (Am μ L γ β K m * Real.sin ((m * Δ % K : ℕ) * π / K) -
        qm μ L γ β K m * Real.cos ((m * Δ % K : ℕ) * π / K))) := by
  rw [ϕ_eq]
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK
  have h1 : ((m * Δ : ℕ) : ℝ) * θ K = 2 * (((m * Δ : ℕ) : ℝ) * π / K) := by
    unfold θ; ring
  rw [h1, residual_half]
  have h2 : ((m * Δ : ℕ) : ℝ) * π / K =
      ((m * Δ % K : ℕ) : ℝ) * π / K + ((m * Δ / K : ℕ) : ℝ) * π := by
    have : ((m * Δ : ℕ) : ℝ) = ((m * Δ % K : ℕ) : ℝ) + K * ((m * Δ / K : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_add_div (m * Δ) K).symm
    rw [this]
    field_simp
  rw [h2, prod_shift]

lemma ϕ_zero (μ L γ β : ℝ) (K m : ℕ) : ϕ μ L γ β K m 0 = 0 := by
  simp [ϕ]

/-- `ϕ_{K,K-m} = ϕ_{K,m}`: reflecting the cycle about the real axis. -/
lemma ϕ_reflect (μ L γ β : ℝ) {K m : ℕ} (hK : K ≠ 0) (hmK : m ≤ K) (Δ : ℕ) :
    ϕ μ L γ β K (K - m) Δ = ϕ μ L γ β K m Δ := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK
  have e1 : ((K - m : ℕ) : ℝ) * θ K = ((1 : ℕ) : ℝ) * (2 * π) - (m : ℝ) * θ K := by
    rw [Nat.cast_sub hmK]; unfold θ; field_simp; ring
  have e2 : (((K - m) * Δ : ℕ) : ℝ) * θ K = (Δ : ℝ) * (2 * π) - ((m * Δ : ℕ) : ℝ) * θ K := by
    rw [Nat.cast_mul, Nat.cast_sub hmK, Nat.cast_mul]; unfold θ; field_simp
  rw [ϕ_eq, ϕ_eq, Am, Am, pm, pm, qm, qm, e1, e2]
  simp only [Real.cos_nat_mul_two_pi_sub, Real.sin_nat_mul_two_pi_sub]
  ring

/-! ## Sign lemmas -/

lemma key_mono {A q a x : ℝ} (hq : 0 < q) (ha0 : 0 < a) (ha : a < π / 2) (hx1 : a ≤ x)
    (hx2 : x < π) (h : q * Real.cos a ≤ A * Real.sin a) : q * Real.cos x ≤ A * Real.sin x := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith)
  have hca : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, ha⟩
  have hA : 0 < A := by
    by_contra hA
    push Not at hA
    nlinarith [mul_pos hq hca]
  have hsx : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hx2.le
  have hsub : 0 ≤ Real.sin (x - a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [Real.sin_sub] at hsub
  rcases le_or_gt (Real.cos x) 0 with hcx | hcx
  · nlinarith [mul_nonneg hA.le hsx, mul_nonneg hq.le (neg_nonneg.2 hcx)]
  · have h1 : q * Real.cos a * Real.cos x ≤ A * Real.sin a * Real.cos x :=
      mul_le_mul_of_nonneg_right h hcx.le
    have h2 : A * (Real.cos x * Real.sin a) ≤ A * (Real.sin x * Real.cos a) :=
      mul_le_mul_of_nonneg_left (by linarith) hA.le
    have : q * Real.cos x * Real.cos a ≤ A * Real.sin x * Real.cos a := by nlinarith
    exact le_of_mul_le_mul_right this hca

lemma key_mono_strict {A q a x : ℝ} (hq : 0 < q) (ha0 : 0 < a) (ha : a < π / 2) (hx1 : a ≤ x)
    (hx2 : x < π) (h : q * Real.cos a < A * Real.sin a) : q * Real.cos x < A * Real.sin x := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith)
  have hca : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, ha⟩
  have hA : 0 < A := by
    by_contra hA
    push Not at hA
    nlinarith [mul_pos hq hca]
  have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi (by linarith) hx2
  have hsub : 0 ≤ Real.sin (x - a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [Real.sin_sub] at hsub
  rcases le_or_gt (Real.cos x) 0 with hcx | hcx
  · nlinarith [mul_pos hA hsx, mul_nonneg hq.le (neg_nonneg.2 hcx)]
  · have h1 : q * Real.cos a * Real.cos x < A * Real.sin a * Real.cos x :=
      mul_lt_mul_of_pos_right h hcx
    have h2 : A * (Real.cos x * Real.sin a) ≤ A * (Real.sin x * Real.cos a) :=
      mul_le_mul_of_nonneg_left (by linarith) hA.le
    have : q * Real.cos x * Real.cos a < A * Real.sin x * Real.cos a := by nlinarith
    exact lt_of_mul_lt_mul_right this hca.le

/-! ## The interpolation inequality for a single Fourier mode -/

/-- The interpolation inequality between `a` and `a ζ` for the pure mode, in normalized form,
equals the residual: `⟪M aζ, a - aζ⟫ + ‖M a - M aζ‖²/2 = Re[(1 - M)* M (ζ - 1)]`. -/
lemma pair_identity (Mc a ζ : ℂ) (ha : ‖a‖ = 1) (hζ : ‖ζ‖ = 1) :
    ⟪Mc * (a * ζ), a - a * ζ⟫ + 1 / 2 * ‖Mc * a - Mc * (a * ζ)‖ ^ 2 =
      (conj (1 - Mc) * Mc * (ζ - 1)).re := by
  have ha' : a.re * a.re + a.im * a.im = 1 := by
    have := Complex.sq_norm a
    rw [ha, Complex.normSq_apply] at this
    linarith
  have hζ' : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by
    have := Complex.sq_norm ζ
    rw [hζ, Complex.normSq_apply] at this
    linarith
  rw [Complex.inner, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, Complex.one_re, Complex.one_im]
  linear_combination
    (ζ.re^2*Mc.re^2/2 - ζ.re^2*Mc.re + ζ.re^2*Mc.im^2/2 - ζ.re*Mc.re^2 + ζ.re*Mc.re -
      ζ.re*Mc.im^2 + Mc.re^2*ζ.im^2/2 + Mc.re^2/2 - Mc.re*ζ.im^2 + Mc.im^2*ζ.im^2/2 +
      Mc.im^2/2 - Mc.im*ζ.im) * ha' + (Mc.re^2/2 - Mc.re + Mc.im^2/2) * hζ'

/-- The same identity with the factor `ℓ = L - μ` of the normalization. -/
lemma pair_identity_scaled (Mc a ζ : ℂ) {ℓ : ℝ} (hℓ : 0 < ℓ) (ha : ‖a‖ = 1) (hζ : ‖ζ‖ = 1) :
    ⟪(ℓ : ℂ) * Mc * (a * ζ), a - a * ζ⟫ +
        1 / (2 * ℓ) * ‖(ℓ : ℂ) * Mc * a - (ℓ : ℂ) * Mc * (a * ζ)‖ ^ 2 =
      ℓ * (conj (1 - Mc) * Mc * (ζ - 1)).re := by
  rw [← pair_identity Mc a ζ ha hζ]
  have e1 : ⟪(ℓ : ℂ) * Mc * (a * ζ), a - a * ζ⟫ = ℓ * ⟪Mc * (a * ζ), a - a * ζ⟫ := by
    rw [mul_assoc, ← Complex.real_smul, real_inner_smul_left]
  have e2 : ‖(ℓ : ℂ) * Mc * a - (ℓ : ℂ) * Mc * (a * ζ)‖ = ℓ * ‖Mc * a - Mc * (a * ζ)‖ := by
    rw [mul_assoc, mul_assoc, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hℓ]
  rw [e1, e2]
  have hℓ0 : ℓ ≠ 0 := hℓ.ne'
  field_simp
  try ring

/-! ## The Fourier reduction and the necessary mixed condition (8) -/

lemma ω_pow_conj (K n : ℕ) : conj (ω K ^ n) = (ω K ^ n)⁻¹ :=
  (Complex.inv_eq_conj (norm_ω_pow K n)).symm

lemma ω_pow_mod {K : ℕ} (hK : K ≠ 0) (n : ℕ) : ω K ^ n = ω K ^ (n % K) := by
  conv_lhs => rw [← Nat.mod_add_div n K, pow_add, pow_mul, ω_pow_self hK, one_pow, mul_one]

lemma ω_pow_ne_one {K j : ℕ} (hK : K ≠ 0) (h0 : 0 < j) (h1 : j < 2 * K) (hK' : j ≠ K) :
    ω K ^ j ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := ((ω_primitive hK).pow_eq_one_iff_dvd j).1 h
  rcases c with _ | _ | c
  · simp at hc; omega
  · simp at hc; omega
  · have : 2 * K ≤ K * (c + 1 + 1) := by nlinarith
    omega

/-- Orthogonality of the characters `t ↦ ω^{mt}` on `{0, …, K - 1}`. -/
lemma orthogonality {K : ℕ} (hK : K ≠ 0) {m m' : ℕ} (hm : m < K) (hm' : m' < K) :
    ∑ t ∈ Finset.range K, ω K ^ (m * t) * conj (ω K ^ (m' * t)) =
      if m = m' then (K : ℂ) else 0 := by
  have hζ : ∀ t, ω K ^ (m * t) * conj (ω K ^ (m' * t)) = (ω K ^ (m + K - m')) ^ t := by
    intro t
    rw [ω_pow_conj, ← pow_mul]
    have h1 : ω K ^ (m' * t) * ω K ^ ((K - m') * t) = 1 := by
      rw [← pow_add, ← add_mul, show m' + (K - m') = K by omega, mul_comm, ω_pow_mul_self hK]
    rw [show (m + K - m') * t = m * t + (K - m') * t by
      rw [show m + K - m' = m + (K - m') by omega, add_mul], pow_add,
      inv_eq_of_mul_eq_one_right h1]
  simp_rw [hζ]
  split_ifs with h
  · subst h
    rw [show m + K - m = K by omega, ω_pow_self hK]
    simp
  · rw [geom_sum_eq (ω_pow_ne_one hK (by omega) (by omega) (by omega)), ← pow_mul, mul_comm,
      pow_mul, ω_pow_self hK, one_pow, sub_self, zero_div]

/-- A Parseval-type identity for the real inner product on `ℂ`. -/
lemma parseval {K : ℕ} (hK : K ≠ 0) (a b : ℕ → ℂ) :
    ∑ t ∈ Finset.range K, ⟪∑ m ∈ Finset.range K, a m * ω K ^ (m * t),
        ∑ m ∈ Finset.range K, b m * ω K ^ (m * t)⟫ =
      K * (∑ m ∈ Finset.range K, b m * conj (a m)).re := by
  simp_rw [Complex.inner, map_sum, map_mul, Finset.sum_mul_sum]
  rw [← Complex.re_sum]
  have : ∑ t ∈ Finset.range K, ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K,
      b i * ω K ^ (i * t) * (conj (a j) * conj (ω K ^ (j * t))) =
      ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K, b i * conj (a j) *
        ∑ t ∈ Finset.range K, ω K ^ (i * t) * conj (ω K ^ (j * t)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [this]
  have h2 : ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K, b i * conj (a j) *
      ∑ t ∈ Finset.range K, ω K ^ (i * t) * conj (ω K ^ (j * t)) =
      ∑ i ∈ Finset.range K, b i * conj (a i) * K := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Finset.sum_congr rfl fun j hj => by
      rw [orthogonality hK hi (Finset.mem_range.1 hj)]]
    simp [Finset.sum_ite_eq, hi]
  rw [h2, ← Finset.sum_mul, mul_comm]
  simp

lemma parseval_norm {K : ℕ} (hK : K ≠ 0) (d : ℕ → ℂ) :
    ∑ t ∈ Finset.range K, ‖∑ m ∈ Finset.range K, d m * ω K ^ (m * t)‖ ^ 2 =
      K * ∑ m ∈ Finset.range K, ‖d m‖ ^ 2 := by
  simp_rw [← real_inner_self_eq_norm_sq]
  rw [parseval hK d d]
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, real_inner_self_eq_norm_sq]
  norm_cast

/-- The discrete Fourier coefficients `c_m = (1/K) ∑_t z_t ω^{-mt}` of a cycle, (4). -/
def dft (K : ℕ) (z : ℕ → ℂ) (m : ℕ) : ℂ :=
  (K : ℂ)⁻¹ * ∑ s ∈ Finset.range K, z s * conj (ω K ^ (m * s))

/-- Fourier inversion (4): `z_t = ∑_m c_m ω^{mt}` for a `K`-periodic `z`. -/
lemma dft_inv {K : ℕ} (hK : K ≠ 0) {z : ℕ → ℂ} (hper : ∀ t, z (t + K) = z t) (t : ℕ) :
    z t = ∑ m ∈ Finset.range K, dft K z m * ω K ^ (m * t) := by
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  have ht : t % K < K := Nat.mod_lt _ (Nat.pos_of_ne_zero hK)
  have hω : ∀ m, ω K ^ (m * t) = ω K ^ (m * (t % K)) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div t K]
    rw [mul_add, pow_add, show m * (K * (t / K)) = m * (t / K) * K by ring,
      ω_pow_mul_self hK, mul_one]
  have e : ∑ m ∈ Finset.range K, dft K z m * ω K ^ (m * t) =
      (K : ℂ)⁻¹ * ∑ s ∈ Finset.range K, z s *
        ∑ m ∈ Finset.range K, ω K ^ ((t % K) * m) * conj (ω K ^ (s * m)) := by
    unfold dft
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun m _ => ?_
    rw [hω m]
    ring_nf
  rw [e, Finset.sum_congr rfl fun s hs => by rw [orthogonality hK ht (Finset.mem_range.1 hs)]]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_range, ht, ite_true]
  rw [periodic_mod hper]
  field_simp

/-- `∑_{t < K} (F (t + Δ) - F t) = 0` for `K`-periodic `F`. -/
lemma sum_shift_periodic {K : ℕ} {F : ℕ → ℝ} (hper : ∀ t, F (t + K) = F t) (Δ : ℕ) :
    ∑ t ∈ Finset.range K, F (t + Δ) = ∑ t ∈ Finset.range K, F t := by
  induction Δ with
  | zero => simp
  | succ n ih =>
    rw [← ih]
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; simp
    · have h1 := Finset.sum_range_succ (fun t => F (t + n)) K
      have h2 := Finset.sum_range_succ' (fun t => F (t + n)) K
      have h3 : F (K + n) = F (0 + n) := by rw [zero_add, add_comm, hper]
      have h4 : ∑ t ∈ Finset.range K, F (t + (n + 1)) = ∑ t ∈ Finset.range K, F (t + 1 + n) :=
        Finset.sum_congr rfl fun t _ => by rw [show t + (n + 1) = t + 1 + n by ring]
      rw [h4]
      linarith

/-- **The necessary mixed condition (8).** Every cycle of length `K ≥ 3` in `ℂ ≅ ℝ²` on some
`f ∈ F_{μ,L}(ℂ)` satisfies `∑_m s_m ϕ_{K,m}(Δ) ≤ 0` for `Δ = 1, …, K - 1`, where
`s_m = |c_m|² / ∑_{m'} |c_{m'}|²` and `c_m` are the Fourier coefficients (4) of the cycle. -/
theorem mixed_condition {μ L : ℝ} (hμL : μ < L) {K : ℕ} (hK : 3 ≤ K) {γ β : ℝ}
    {f : ℂ → ℝ} (hf : f ∈ F μ L ℂ) {z : ℕ → ℂ} (hc : Cycles L γ β f K z) :
    ∃ s : ℕ → ℝ, (∀ m, s m = ‖dft K (fun t => z (t % K)) m‖ ^ 2 /
        ∑ m' ∈ Finset.range K, ‖dft K (fun t => z (t % K)) m'‖ ^ 2) ∧
      (∀ m, 0 ≤ s m) ∧ ∑ m ∈ Finset.range K, s m = 1 ∧
      ∀ Δ, 1 ≤ Δ → Δ < K → ∑ m ∈ Finset.range K, s m * ϕ μ L γ β K m Δ ≤ 0 := by
  have hK0 : K ≠ 0 := by omega
  have hKr : (0 : ℝ) < K := by positivity
  have hℓ : 0 < L - μ := sub_pos.2 hμL
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ → ℂ, Z = fun t => z (t % K) := ⟨_, rfl⟩
  rw [← hZ]
  have hZper : ∀ t, Z (t + K) = Z t := fun t => by rw [hZ]; simp only [Nat.add_mod_right]
  obtain ⟨hp, ⟨i₀, hi₀, j₀, hj₀, hij₀⟩, x₀, x₁, hx, hmin⟩ := hc
  have hγ : γ ≠ 0 := hp.2.1.ne'
  have hZi : ∀ i < K, Z i = z i := fun i hi => by
    rw [hZ]; exact congrArg z (Nat.mod_eq_of_lt hi)
  have hcZ : Cycles L γ β f K Z :=
    ⟨hp, ⟨i₀, hi₀, j₀, hj₀, by rw [hZi i₀ hi₀, hZi j₀ hj₀]; exact hij₀⟩,
      x₀, x₁, fun t => by rw [hx t, hZ]; simp only [Nat.mod_mod], hmin⟩
  have hinv := dft_inv hK0 hZper
  -- the gradient along the cycle, mode by mode
  have key : ∀ t, gradient f (Z (t + 1)) =
      ∑ m ∈ Finset.range K, dft K Z m * Mhat γ β K m * ω K ^ (m * (t + 1)) := by
    intro t
    have h := grad_of_cycles hZper hcZ t
    have hγ' : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
    rw [Complex.real_smul] at h
    apply mul_left_cancel₀ hγ'
    rw [h, hinv t, hinv (t + 1), hinv (t + 2)]
    simp only [Complex.real_smul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hne : ω K ^ m ≠ 0 := ω_pow_ne_zero K m
    rw [Mhat, show m * (t + 2) = m * t + m * 2 by ring, show m * (t + 1) = m * t + m by ring,
      pow_add, pow_add, show m * 2 = m + m by ring, pow_add]
    field_simp
    push_cast
    ring
  have hG : ∀ t, gradient f (Z t) - μ • Z t =
      ∑ m ∈ Finset.range K, ((L - μ : ℝ) : ℂ) * dft K Z m * M μ L γ β K m * ω K ^ (m * t) := by
    intro t
    have ht : gradient f (Z t) =
        ∑ m ∈ Finset.range K, dft K Z m * Mhat γ β K m * ω K ^ (m * t) := by
      have := key (t + K - 1)
      rw [show t + K - 1 + 1 = t + K by omega, hZper] at this
      rw [this]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_add, pow_add, ω_pow_mul_self hK0, mul_one]
    rw [ht, hinv t, Complex.real_smul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Mhat_eq hγ hμL.ne]
    ring
  -- sum the interpolation inequalities over `t`
  have hsum : ∀ Δ, (L - μ) * K * ∑ m ∈ Finset.range K, ‖dft K Z m‖ ^ 2 * ϕ μ L γ β K m Δ ≤ 0 := by
    intro Δ
    have step : ∀ t, ⟪gradient f (Z (t + Δ)) - μ • Z (t + Δ), Z t - Z (t + Δ)⟫ +
        1 / (2 * (L - μ)) * ‖(gradient f (Z t) - μ • Z t) -
          (gradient f (Z (t + Δ)) - μ • Z (t + Δ))‖ ^ 2 ≤
        (f (Z t) - μ / 2 * ‖Z t‖ ^ 2) - (f (Z (t + Δ)) - μ / 2 * ‖Z (t + Δ)‖ ^ 2) := by
      intro t
      have := F.interp hμL hf (Z t) (Z (t + Δ))
      linarith
    have hS := Finset.sum_le_sum fun t (_ : t ∈ Finset.range K) => step t
    have hshift := sum_shift_periodic (F := fun t => f (Z t) - μ / 2 * ‖Z t‖ ^ 2)
      (fun t => by
        show f (Z (t + K)) - μ / 2 * ‖Z (t + K)‖ ^ 2 = f (Z t) - μ / 2 * ‖Z t‖ ^ 2
        rw [hZper]) Δ
    rw [Finset.sum_sub_distrib, hshift, sub_self, Finset.sum_add_distrib] at hS
    -- evaluate both sums with Parseval
    have e1 : ∀ t, Z t - Z (t + Δ) = ∑ m ∈ Finset.range K,
        (dft K Z m * (1 - ω K ^ (m * Δ))) * ω K ^ (m * t) := by
      intro t
      rw [hinv t, hinv (t + Δ), ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_add, pow_add]
      ring
    have e2 : ∀ t, gradient f (Z (t + Δ)) - μ • Z (t + Δ) = ∑ m ∈ Finset.range K,
        (((L - μ : ℝ) : ℂ) * dft K Z m * M μ L γ β K m * ω K ^ (m * Δ)) * ω K ^ (m * t) := by
      intro t
      rw [hG]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_add, pow_add]
      ring
    have e3 : ∀ t, (gradient f (Z t) - μ • Z t) - (gradient f (Z (t + Δ)) - μ • Z (t + Δ)) =
        ∑ m ∈ Finset.range K,
          (((L - μ : ℝ) : ℂ) * dft K Z m * M μ L γ β K m * (1 - ω K ^ (m * Δ))) *
            ω K ^ (m * t) := by
      intro t
      rw [hG, hG, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_add, pow_add]
      ring
    simp_rw [e3, e2, e1] at hS
    rw [parseval hK0, ← Finset.mul_sum, parseval_norm hK0] at hS
    -- identify each mode with the residual
    have hmode : ∀ m, ((dft K Z m * (1 - ω K ^ (m * Δ))) *
        conj (((L - μ : ℝ) : ℂ) * dft K Z m * M μ L γ β K m * ω K ^ (m * Δ))).re +
        1 / (2 * (L - μ)) *
          ‖((L - μ : ℝ) : ℂ) * dft K Z m * M μ L γ β K m * (1 - ω K ^ (m * Δ))‖ ^ 2 =
        (L - μ) * (‖dft K Z m‖ ^ 2 * ϕ μ L γ β K m Δ) := by
      intro m
      have pid := pair_identity (M μ L γ β K m) 1 (ω K ^ (m * Δ)) (by simp) (norm_ω_pow K _)
      rw [Complex.inner] at pid
      simp only [one_mul, mul_one] at pid
      have e4 : ((dft K Z m * (1 - ω K ^ (m * Δ))) *
          conj (((L - μ : ℝ) : ℂ) * dft K Z m * M μ L γ β K m * ω K ^ (m * Δ))).re =
          (L - μ) * ‖dft K Z m‖ ^ 2 *
            ((1 - ω K ^ (m * Δ)) * conj (M μ L γ β K m * ω K ^ (m * Δ))).re := by
        rw [show (dft K Z m * (1 - ω K ^ (m * Δ))) *
            conj (((L - μ : ℝ) : ℂ) * dft K Z m * M μ L γ β K m * ω K ^ (m * Δ)) =
            ((L - μ : ℝ) : ℂ) * (dft K Z m * conj (dft K Z m)) *
              ((1 - ω K ^ (m * Δ)) * conj (M μ L γ β K m * ω K ^ (m * Δ))) by
          simp only [map_mul, Complex.conj_ofReal]; ring]
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul,
          Complex.re_ofReal_mul]
      have e5 : ‖((L - μ : ℝ) : ℂ) * dft K Z m * M μ L γ β K m * (1 - ω K ^ (m * Δ))‖ ^ 2 =
          (L - μ) ^ 2 * ‖dft K Z m‖ ^ 2 *
            ‖M μ L γ β K m - M μ L γ β K m * ω K ^ (m * Δ)‖ ^ 2 := by
        rw [show ((L - μ : ℝ) : ℂ) * dft K Z m * M μ L γ β K m * (1 - ω K ^ (m * Δ)) =
            ((L - μ : ℝ) : ℂ) * dft K Z m *
              (M μ L γ β K m - M μ L γ β K m * ω K ^ (m * Δ)) by ring,
          norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ]
        ring
      have hϕ : ϕ μ L γ β K m Δ =
          (conj (1 - M μ L γ β K m) * M μ L γ β K m * (ω K ^ (m * Δ) - 1)).re := rfl
      rw [e4, e5, hϕ, ← pid]
      have hℓ0 : L - μ ≠ 0 := hℓ.ne'
      field_simp
    rw [Complex.re_sum] at hS
    have hcomb : ∑ m ∈ Finset.range K, (((dft K Z m * (1 - ω K ^ (m * Δ))) *
        conj (((L - μ : ℝ) : ℂ) * dft K Z m * M μ L γ β K m * ω K ^ (m * Δ))).re +
        1 / (2 * (L - μ)) *
          ‖((L - μ : ℝ) : ℂ) * dft K Z m * M μ L γ β K m * (1 - ω K ^ (m * Δ))‖ ^ 2) =
        (L - μ) * ∑ m ∈ Finset.range K, ‖dft K Z m‖ ^ 2 * ϕ μ L γ β K m Δ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => hmode m
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hcomb
    have hK := congrArg (fun x => (K : ℝ) * x) hcomb
    nlinarith
  -- normalize
  have hS0 : 0 < ∑ m ∈ Finset.range K, ‖dft K Z m‖ ^ 2 := by
    by_contra h
    push Not at h
    have hzero : ∀ m ∈ Finset.range K, ‖dft K Z m‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun m _ => sq_nonneg _).1
        (le_antisymm h (Finset.sum_nonneg fun m _ => sq_nonneg _))
    have hZ0 : ∀ t, Z t = 0 := by
      intro t
      rw [hinv t]
      refine Finset.sum_eq_zero fun m hm => ?_
      have := hzero m hm
      rw [sq_eq_zero_iff, norm_eq_zero] at this
      rw [this, zero_mul]
    apply hij₀
    rw [← hZi i₀ hi₀, ← hZi j₀ hj₀, hZ0, hZ0]
  refine ⟨fun m => ‖dft K Z m‖ ^ 2 / ∑ m' ∈ Finset.range K, ‖dft K Z m'‖ ^ 2, fun m => rfl,
    fun m => by positivity, ?_, fun Δ _ _ => ?_⟩
  · rw [← Finset.sum_div, div_self hS0.ne']
  · have := hsum Δ
    have hpos : 0 < (L - μ) * K := mul_pos hℓ hKr
    have h2 : ∑ m ∈ Finset.range K, ‖dft K Z m‖ ^ 2 * ϕ μ L γ β K m Δ ≤ 0 := by
      by_contra h
      push Not at h
      nlinarith [mul_pos hpos h]
    calc ∑ m ∈ Finset.range K,
          ‖dft K Z m‖ ^ 2 / (∑ m' ∈ Finset.range K, ‖dft K Z m'‖ ^ 2) * ϕ μ L γ β K m Δ
        = (∑ m ∈ Finset.range K, ‖dft K Z m‖ ^ 2 * ϕ μ L γ β K m Δ) /
            ∑ m' ∈ Finset.range K, ‖dft K Z m'‖ ^ 2 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun m _ => ?_
          ring
      _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg h2 hS0.le

/-! ## Lemma 3.1 -/

/-- On the roots of unity, the gradient condition (5) reads `∇f(z) = M̂ z`. -/
lemma rou_grad_iff {γ β : ℝ} {K m : ℕ} (hK : K ≠ 0) (f : ℂ → ℝ) :
    (∀ t, gradient f (ω K ^ (m * (t + 1))) =
        γ⁻¹ • ((1 + β) • ω K ^ (m * (t + 1)) - ω K ^ (m * (t + 2)) - β • ω K ^ (m * t))) ↔
      ∀ s, gradient f (ω K ^ (m * s)) = Mhat γ β K m * ω K ^ (m * s) := by
  have key : ∀ s, γ⁻¹ • ((1 + β) • ω K ^ (m * (s + 1)) - ω K ^ (m * (s + 2)) -
      β • ω K ^ (m * s)) = Mhat γ β K m * ω K ^ (m * (s + 1)) := by
    intro s
    have hne : ω K ^ m ≠ 0 := ω_pow_ne_zero K m
    have h1 : ω K ^ (m * (s + 2)) = ω K ^ (m * (s + 1)) * ω K ^ m := by
      rw [← pow_add]; ring_nf
    have h2 : ω K ^ (m * s) = ω K ^ (m * (s + 1)) * (ω K ^ m)⁻¹ := by
      rw [show m * (s + 1) = m * s + m by ring, pow_add, mul_assoc, mul_inv_cancel₀ hne,
        mul_one]
    rw [h1, h2, Mhat]
    simp only [Complex.real_smul]
    push_cast
    ring
  constructor
  · intro h s
    have hs := h (s + K - 1)
    have e1 : s + K - 1 + 1 = s + K := by omega
    have e3 : ω K ^ (m * (s + K)) = ω K ^ (m * s) := by
      rw [mul_add, pow_add, ω_pow_mul_self hK, mul_one]
    rw [key, e1, e3] at hs
    exact hs
  · intro h t
    rw [key, h]

/-- **Lemma 3.1, equation (9).** For `K ≥ 3` and `m ∈ U_K`, `(HB)` cycles over the `m`-jump `K`-th
roots of unity iff `(γ, β) ∈ Ω_cv(Q_{μ,L})` and all residuals are non-positive. -/
theorem lemma_3_1 {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L) {K m : ℕ} (hK : 3 ≤ K) (hm : m ∈ U K) :
    ΩRoU μ L K m = {x | x ∈ Ωcv L ∧ ∀ Δ, 1 ≤ Δ → Δ < K → ϕ μ L x.1 x.2 K m Δ ≤ 0} := by
  obtain ⟨-, -, hcop⟩ := hm
  have hK0 : K ≠ 0 := by omega
  have hℓ : 0 < L - μ := sub_pos.2 hμL
  have hper : ∀ t, ω K ^ (m * (t + K)) = ω K ^ (m * t) := fun t => by
    rw [mul_add, pow_add, ω_pow_mul_self hK0, mul_one]
  have hG : ∀ {γ β : ℝ}, γ ≠ 0 → ∀ w : ℂ,
      Mhat γ β K m * w - μ • w = ((L - μ : ℝ) : ℂ) * M μ L γ β K m * w := by
    intro γ β hγ w
    rw [Mhat_eq hγ hμL.ne, Complex.real_smul]
    ring
  ext ⟨γ, β⟩
  simp only [ΩRoU, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨f, hf, hc⟩
    have hp := hc.1
    have hγ : γ ≠ 0 := hp.2.1.ne'
    refine ⟨hp, fun Δ hΔ1 hΔK => ?_⟩
    have hg : ∀ s, gradient f (ω K ^ (m * s)) = Mhat γ β K m * ω K ^ (m * s) := by
      refine (rou_grad_iff hK0 f).1 fun t => ?_
      have h := grad_of_cycles (z := fun t => ω K ^ (m * t)) hper hc t
      rw [← h, smul_smul, inv_mul_cancel₀ hγ, one_smul]
    have step : ∀ k, (f (ω K ^ (m * ((k + 1) * Δ))) - μ / 2) + (L - μ) * ϕ μ L γ β K m Δ ≤
        f (ω K ^ (m * (k * Δ))) - μ / 2 := by
      intro k
      have h := F.interp hμL hf (ω K ^ (m * (k * Δ))) (ω K ^ (m * ((k + 1) * Δ)))
      rw [norm_ω_pow, norm_ω_pow, hg, hg, hG hγ, hG hγ] at h
      have hzz : ω K ^ (m * ((k + 1) * Δ)) = ω K ^ (m * (k * Δ)) * ω K ^ (m * Δ) := by
        rw [← pow_add]; congr 1; ring
      have pid := pair_identity_scaled (M μ L γ β K m) (ω K ^ (m * (k * Δ))) (ω K ^ (m * Δ)) hℓ
        (norm_ω_pow K _) (norm_ω_pow K _)
      rw [← hzz] at pid
      have e : ϕ μ L γ β K m Δ =
          (conj (1 - M μ L γ β K m) * M μ L γ β K m * (ω K ^ (m * Δ) - 1)).re := rfl
      rw [e]
      linarith
    have hsum := Finset.sum_le_sum (s := Finset.range K) fun k _ => (by linarith [step k] :
      (L - μ) * ϕ μ L γ β K m Δ ≤
        (f (ω K ^ (m * (k * Δ))) - μ / 2) - (f (ω K ^ (m * ((k + 1) * Δ))) - μ / 2))
    rw [Finset.sum_range_sub' (fun k => f (ω K ^ (m * (k * Δ))) - μ / 2), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul] at hsum
    have hzK : ω K ^ (m * (K * Δ)) = ω K ^ (m * (0 * Δ)) := by
      rw [zero_mul, mul_zero, pow_zero, ← mul_assoc, mul_comm m K, mul_assoc, pow_mul,
        ω_pow_self hK0, one_pow]
    rw [hzK, sub_self] at hsum
    have hKpos : (0 : ℝ) < K := by positivity
    by_contra hpos
    push Not at hpos
    nlinarith [mul_pos hKpos (mul_pos hℓ hpos)]
  · rintro ⟨hp, hϕ⟩
    have hγ : γ ≠ 0 := hp.2.1.ne'
    obtain ⟨f, hf, hfx⟩ := interp_sufficient (E := ℂ) (ι := Fin K) hμ.le hμL
      (fun i => ω K ^ (m * (i : ℕ))) (fun i => Mhat γ β K m * ω K ^ (m * (i : ℕ)))
      (fun _ => μ / 2) (by
        intro i j
        rw [norm_ω_pow, norm_ω_pow, hG hγ, hG hγ]
        -- write `ω^{mj} = ω^{mi} ω^{mΔ'}` with `Δ' < K`, and `Δ' = 0` only if `i = j`
        obtain ⟨Δ', hΔ'K, hzj⟩ : ∃ Δ', Δ' < K ∧
            ω K ^ (m * (j : ℕ)) = ω K ^ (m * (i : ℕ)) * ω K ^ (m * Δ') := by
          rcases le_or_gt (i : ℕ) j with hij | hij
          · refine ⟨j - i, by omega, ?_⟩
            rw [← pow_add, ← mul_add, show (i : ℕ) + (j - i) = j by omega]
          · refine ⟨j + K - i, by omega, ?_⟩
            rw [← pow_add, ← mul_add, show (i : ℕ) + (j + K - i) = j + K by omega, mul_add,
              pow_add, ω_pow_mul_self hK0, mul_one]
        have pid := pair_identity_scaled (M μ L γ β K m) (ω K ^ (m * (i : ℕ))) (ω K ^ (m * Δ'))
          hℓ (norm_ω_pow K _) (norm_ω_pow K _)
        rw [← hzj] at pid
        have hϕ' : (conj (1 - M μ L γ β K m) * M μ L γ β K m * (ω K ^ (m * Δ') - 1)).re ≤ 0 := by
          rcases Nat.eq_zero_or_pos Δ' with h0 | h0
          · rw [h0, mul_zero, pow_zero, sub_self, mul_zero, Complex.zero_re]
          · exact hϕ Δ' h0 hΔ'K
        nlinarith [mul_nonpos_iff.2 (Or.inl ⟨hℓ.le, hϕ'⟩)])
    have hg : ∀ s, gradient f (ω K ^ (m * s)) = Mhat γ β K m * ω K ^ (m * s) := by
      intro s
      have h := (hfx ⟨s % K, Nat.mod_lt _ (by omega)⟩).2
      simp only at h
      have e : ω K ^ (m * (s % K)) = ω K ^ (m * s) :=
        periodic_mod (z := fun t => ω K ^ (m * t)) hper s
      rwa [e] at h
    exact ⟨f, hf, cycles_of_grad (by omega) hp hper
      (fun a ha b hb h => ω_pow_inj hK0 hcop ha hb h) ((rou_grad_iff hK0 f).2 hg)⟩

lemma qm_pos {μ L γ β : ℝ} (hμL : μ < L) {K m : ℕ} (hm1 : 1 ≤ m) (h2m : 2 * m < K)
    (hp : (γ, β) ∈ Ωcv L) : 0 < qm μ L γ β K m := by
  obtain ⟨hβ, hγ, -⟩ := hp
  have hβ' : 0 < 1 - β := by linarith [(abs_lt.1 hβ).2]
  have hK : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hs : 0 < Real.sin (m * θ K) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < m := by exact_mod_cast hm1
      unfold θ
      positivity
    · have h2 : (2 * m : ℝ) < K := by exact_mod_cast h2m
      unfold θ
      rw [mul_div_assoc', div_lt_iff₀ hK]
      nlinarith [Real.pi_pos]
  unfold qm
  have : 0 < (L - μ) * γ := mul_pos (sub_pos.2 hμL) hγ
  positivity

lemma pi_div_bounds {K : ℕ} (hK : 3 ≤ K) : 0 < π / K ∧ π / K < π / 2 := by
  have hKr : (3 : ℝ) ≤ K := by exact_mod_cast hK
  exact ⟨by positivity, div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)⟩

/-- The residual system reduces to the single inequality `q cos(π/K) ≤ A sin(π/K)`. -/
lemma residual_system_iff {μ L γ β : ℝ} (hμL : μ < L) {K m : ℕ} (hK : 3 ≤ K) (hm : m ∈ U K)
    (h2m : 2 * m < K) (hp : (γ, β) ∈ Ωcv L) :
    (∀ Δ, 1 ≤ Δ → Δ < K → ϕ μ L γ β K m Δ ≤ 0) ↔
      qm μ L γ β K m * Real.cos (π / K) ≤ Am μ L γ β K m * Real.sin (π / K) := by
  obtain ⟨hm1, -, hcop⟩ := hm
  have hK0 : K ≠ 0 := by omega
  have hKr : (0 : ℝ) < K := by positivity
  have hq := qm_pos hμL hm1 h2m hp
  obtain ⟨ha0, ha⟩ := pi_div_bounds hK
  have hsa : 0 < Real.sin (π / K) := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  constructor
  · intro h
    obtain ⟨Δm, hΔmK, hΔm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega : 1 < K)
    have hΔm1 : 1 ≤ Δm := by
      rcases Nat.eq_zero_or_pos Δm with h0 | h0
      · simp [h0] at hΔm
      · exact h0
    have := h Δm hΔm1 hΔmK
    rw [ϕ_half μ L γ β hK0, hΔm, Nat.cast_one, one_mul] at this
    have h2 : 0 ≤ Real.sin (π / K) * (Am μ L γ β K m * Real.sin (π / K) -
        qm μ L γ β K m * Real.cos (π / K)) := by linarith
    have := (mul_nonneg_iff_of_pos_left hsa).1 h2
    linarith
  · intro h Δ hΔ1 hΔK
    rw [ϕ_half μ L γ β hK0]
    set j := m * Δ % K with hj
    have hjK : j < K := Nat.mod_lt _ (by omega)
    have hj0 : j ≠ 0 := by
      intro h0
      have hdvd : K ∣ m * Δ := Nat.dvd_of_mod_eq_zero h0
      have := Nat.le_of_dvd (by omega) (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hdvd)
      omega
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj0
    have hjK' : (j : ℝ) < K := by exact_mod_cast hjK
    have hx1 : π / K ≤ (j : ℝ) * π / K := by
      rw [mul_div_assoc]; nlinarith
    have hx2 : (j : ℝ) * π / K < π := by
      rw [div_lt_iff₀ hKr]; nlinarith [Real.pi_pos]
    have key := key_mono hq ha0 ha hx1 hx2 h
    have hsx : 0 ≤ Real.sin ((j : ℝ) * π / K) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hx2.le
    nlinarith [mul_nonneg hsx (sub_nonneg.2 key)]

/-- Strict version of `residual_system_iff`. -/
lemma residual_system_iff_strict {μ L γ β : ℝ} (hμL : μ < L) {K m : ℕ} (hK : 3 ≤ K)
    (hm : m ∈ U K) (h2m : 2 * m < K) (hp : (γ, β) ∈ Ωcv L) :
    (∀ Δ, 1 ≤ Δ → Δ < K → ϕ μ L γ β K m Δ < 0) ↔
      qm μ L γ β K m * Real.cos (π / K) < Am μ L γ β K m * Real.sin (π / K) := by
  obtain ⟨hm1, -, hcop⟩ := hm
  have hK0 : K ≠ 0 := by omega
  have hKr : (0 : ℝ) < K := by positivity
  have hq := qm_pos hμL hm1 h2m hp
  obtain ⟨ha0, ha⟩ := pi_div_bounds hK
  have hsa : 0 < Real.sin (π / K) := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  constructor
  · intro h
    obtain ⟨Δm, hΔmK, hΔm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega : 1 < K)
    have hΔm1 : 1 ≤ Δm := by
      rcases Nat.eq_zero_or_pos Δm with h0 | h0
      · simp [h0] at hΔm
      · exact h0
    have := h Δm hΔm1 hΔmK
    rw [ϕ_half μ L γ β hK0, hΔm, Nat.cast_one, one_mul] at this
    have h2 : 0 < Real.sin (π / K) * (Am μ L γ β K m * Real.sin (π / K) -
        qm μ L γ β K m * Real.cos (π / K)) := by linarith
    have := (mul_pos_iff_of_pos_left hsa).1 h2
    linarith
  · intro h Δ hΔ1 hΔK
    rw [ϕ_half μ L γ β hK0]
    set j := m * Δ % K with hj
    have hjK : j < K := Nat.mod_lt _ (by omega)
    have hj0 : j ≠ 0 := by
      intro h0
      have hdvd : K ∣ m * Δ := Nat.dvd_of_mod_eq_zero h0
      have := Nat.le_of_dvd (by omega) (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hdvd)
      omega
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj0
    have hjK' : (j : ℝ) < K := by exact_mod_cast hjK
    have hx1 : π / K ≤ (j : ℝ) * π / K := by
      rw [mul_div_assoc]; nlinarith
    have hx2 : (j : ℝ) * π / K < π := by
      rw [div_lt_iff₀ hKr]; nlinarith [Real.pi_pos]
    have key := key_mono_strict hq ha0 ha hx1 hx2 h
    have hsx : 0 < Real.sin ((j : ℝ) * π / K) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) hx2
    nlinarith [mul_pos hsx (sub_pos.2 key)]

/-- `ϕ(Δ_m) = -2 sin(π/K) (A sin(π/K) - q cos(π/K))` at the binding `Δ_m ≡ m⁻¹ (mod K)`. -/
lemma ϕ_binding (μ L γ β : ℝ) {K m Δm : ℕ} (hK0 : K ≠ 0) (hΔm : m * Δm % K = 1) :
    ϕ μ L γ β K m Δm = -2 * (Real.sin (π / K) * (Am μ L γ β K m * Real.sin (π / K) -
      qm μ L γ β K m * Real.cos (π / K))) := by
  rw [ϕ_half μ L γ β hK0, hΔm, Nat.cast_one, one_mul]

/-- **Lemma 3.1, binding constraint.** For `1 ≤ m ≤ (K - 1)/2`, the whole system reduces to the
single residual at the unique `Δ_m ∈ {1, …, K - 1}` with `m Δ_m ≡ 1 (mod K)`. -/
theorem lemma_3_1_binding {μ L γ β : ℝ} (hμL : μ < L) {K m : ℕ} (hK : 3 ≤ K) (hm : m ∈ U K)
    (h2m : 2 * m < K) (hp : (γ, β) ∈ Ωcv L) {Δm : ℕ} (hΔm : m * Δm % K = 1) :
    (∀ Δ, 1 ≤ Δ → Δ < K → ϕ μ L γ β K m Δ ≤ 0) ↔ ϕ μ L γ β K m Δm ≤ 0 := by
  have hK0 : K ≠ 0 := by omega
  obtain ⟨ha0, ha⟩ := pi_div_bounds hK
  have hsa : 0 < Real.sin (π / K) := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  rw [residual_system_iff hμL hK hm h2m hp, ϕ_binding μ L γ β hK0 hΔm]
  constructor
  · intro h; nlinarith [mul_nonneg hsa.le (sub_nonneg.2 h)]
  · intro h
    have h2 : 0 ≤ Real.sin (π / K) * (Am μ L γ β K m * Real.sin (π / K) -
        qm μ L γ β K m * Real.cos (π / K)) := by linarith
    have := (mul_nonneg_iff_of_pos_left hsa).1 h2
    linarith

/-- The binding `Δ_m` is unique in `{0, …, K - 1}`. -/
lemma binding_unique {K m : ℕ} (hm : Nat.Coprime m K) {Δ₁ Δ₂ : ℕ} (h₁ : Δ₁ < K) (h₂ : Δ₂ < K)
    (e₁ : m * Δ₁ % K = 1) (e₂ : m * Δ₂ % K = 1) : Δ₁ = Δ₂ := by
  have : m * Δ₁ ≡ m * Δ₂ [MOD K] := e₁.trans e₂.symm
  have := Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.coprime_comm] using hm) this
  rwa [Nat.ModEq, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at this

/-- **Lemma 3.1, case `m > (K - 1)/2`**: `Ω°_{K,m} = Ω°_{K,K-m}`, and the binding constraint is
`Δ_{K-m}`, i.e. `m Δ ≡ -1 (mod K)`. -/
theorem lemma_3_1_reflect {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L) {K m : ℕ} (hK : 3 ≤ K)
    (hm : m ∈ U K) : ΩRoU μ L K (K - m) = ΩRoU μ L K m := by
  obtain ⟨hm1, hmK, hcop⟩ := hm
  have hK0 : K ≠ 0 := by omega
  have hm' : K - m ∈ U K := ⟨by omega, by omega, (Nat.coprime_self_sub_left hmK.le).2 hcop⟩
  rw [lemma_3_1 hμ hμL hK hm', lemma_3_1 hμ hμL hK ⟨hm1, hmK, hcop⟩]
  ext x
  simp only [Set.mem_ofPred_eq, ϕ_reflect μ L x.1 x.2 hK0 hmK.le]

/-- **Lemma 3.1, binding constraint for `m > (K - 1)/2`**: the binding residual is
`Δ_m = Δ_{K-m}`, i.e. `m Δ_m ≡ -1 (mod K)`. -/
theorem lemma_3_1_binding_reflect {μ L γ β : ℝ} (hμL : μ < L) {K m : ℕ} (hK : 3 ≤ K)
    (hm : m ∈ U K) (h2m : K < 2 * m) (hp : (γ, β) ∈ Ωcv L) {Δm : ℕ}
    (hΔm : (K - m) * Δm % K = 1) :
    (∀ Δ, 1 ≤ Δ → Δ < K → ϕ μ L γ β K m Δ ≤ 0) ↔ ϕ μ L γ β K m Δm ≤ 0 := by
  obtain ⟨hm1, hmK, hcop⟩ := hm
  have hK0 : K ≠ 0 := by omega
  have hm' : K - m ∈ U K := ⟨by omega, by omega, (Nat.coprime_self_sub_left hmK.le).2 hcop⟩
  have h := lemma_3_1_binding hμL hK hm' (by omega) hp hΔm
  simp only [ϕ_reflect μ L γ β hK0 hmK.le] at h
  exact h

/-! ## Lemma 3.1 (ii): the angle condition -/

lemma arg_le_iff {Z : ℂ} (hre : 0 < Z.re) (him : 0 < Z.im) {a : ℝ} (ha0 : 0 < a)
    (ha : a < π / 2) : Complex.arg Z ≤ a ↔ Z.im * Real.cos a ≤ Z.re * Real.sin a := by
  have hZ : Z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; exact lt_irrefl 0 hre
  have hn : 0 < ‖Z‖ := norm_pos_iff.2 hZ
  have h1 := Complex.norm_mul_cos_arg Z
  have h2 := Complex.norm_mul_sin_arg Z
  have harg0 : 0 ≤ Complex.arg Z := Complex.arg_nonneg_iff.2 him.le
  have harg1 : Complex.arg Z < π / 2 := Complex.arg_lt_pi_div_two_iff.2 (Or.inl hre)
  have key : Z.re * Real.sin a - Z.im * Real.cos a = ‖Z‖ * Real.sin (a - Complex.arg Z) := by
    rw [Real.sin_sub, ← h1, ← h2]; ring
  constructor
  · intro h
    have : 0 ≤ Real.sin (a - Complex.arg Z) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
    nlinarith [mul_nonneg hn.le this]
  · intro h
    by_contra hlt
    push Not at hlt
    have : Real.sin (a - Complex.arg Z) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [Real.pi_pos])
    nlinarith [mul_neg_of_pos_of_neg hn this]

lemma arg_lt_iff {Z : ℂ} (hre : 0 < Z.re) (him : 0 < Z.im) {a : ℝ} (ha0 : 0 < a)
    (ha : a < π / 2) : Complex.arg Z < a ↔ Z.im * Real.cos a < Z.re * Real.sin a := by
  have hZ : Z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; exact lt_irrefl 0 hre
  have hn : 0 < ‖Z‖ := norm_pos_iff.2 hZ
  have h1 := Complex.norm_mul_cos_arg Z
  have h2 := Complex.norm_mul_sin_arg Z
  have harg0 : 0 ≤ Complex.arg Z := Complex.arg_nonneg_iff.2 him.le
  have harg1 : Complex.arg Z < π / 2 := Complex.arg_lt_pi_div_two_iff.2 (Or.inl hre)
  have key : Z.re * Real.sin a - Z.im * Real.cos a = ‖Z‖ * Real.sin (a - Complex.arg Z) := by
    rw [Real.sin_sub, ← h1, ← h2]; ring
  constructor
  · intro h
    have : 0 < Real.sin (a - Complex.arg Z) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    nlinarith [mul_pos hn this]
  · intro h
    by_contra hle
    push Not at hle
    have : Real.sin (a - Complex.arg Z) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [Real.pi_pos])
    nlinarith [mul_nonneg hn.le (neg_nonneg.2 this)]

/-- `-arg M + arg(1 - M) = arg((1 - M) M*)` for `M` in the open fourth quadrant with `Re M < 1`. -/
lemma angle_eq {Mc : ℂ} (hre : 0 < Mc.re) (hre1 : Mc.re < 1) (him : Mc.im < 0) :
    -Complex.arg Mc + Complex.arg (1 - Mc) = Complex.arg ((1 - Mc) * conj Mc) := by
  have hM0 : Mc ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; exact lt_irrefl 0 hre
  have h1re : 0 < (1 - Mc).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have h1im : 0 < (1 - Mc).im := by rw [Complex.sub_im, Complex.one_im]; linarith
  have h10 : 1 - Mc ≠ 0 := fun h => by rw [h, Complex.zero_re] at h1re; exact lt_irrefl 0 h1re
  have hargM : Complex.arg Mc < 0 := Complex.arg_neg_iff.2 him
  have hargM' : -(π / 2) < Complex.arg Mc := Complex.neg_pi_div_two_lt_arg_iff.2 (Or.inl hre)
  have harg1 : 0 ≤ Complex.arg (1 - Mc) := Complex.arg_nonneg_iff.2 h1im.le
  have harg1' : Complex.arg (1 - Mc) < π / 2 := Complex.arg_lt_pi_div_two_iff.2 (Or.inl h1re)
  have hconj : Complex.arg (conj Mc) = -Complex.arg Mc := by
    rw [Complex.arg_conj, ite_eq_right]
    intro h
    linarith [Real.pi_pos]
  have hc0 : conj Mc ≠ 0 := (map_ne_zero _).2 hM0
  rw [Complex.arg_mul h10 hc0, hconj]
  · ring
  · rw [hconj]
    constructor <;> linarith [Real.pi_pos]

lemma one_sub_mul_conj (pp qq : ℝ) :
    (1 - (↑pp - ↑qq * Complex.I)) * conj (↑pp - ↑qq * Complex.I) =
      ((pp * (1 - pp) - qq ^ 2 : ℝ) : ℂ) + ↑qq * Complex.I := by
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im] <;>
    ring

/-- The equivalence (i) ⟺ (ii) of Lemma 3.1 at the level of `p`, `q`. -/
lemma ii_iff {pp qq a : ℝ} (hq : 0 < qq) (ha0 : 0 < a) (ha : a < π / 2) :
    qq * Real.cos a ≤ (pp * (1 - pp) - qq ^ 2) * Real.sin a ↔
      qq ^ 2 < pp * (1 - pp) ∧
      (0 < (↑pp - ↑qq * Complex.I : ℂ).re ∧ (↑pp - ↑qq * Complex.I : ℂ).im < 0) ∧
      (0 < (1 - (↑pp - ↑qq * Complex.I) : ℂ).re ∧ 0 < (1 - (↑pp - ↑qq * Complex.I) : ℂ).im) ∧
      -Complex.arg (↑pp - ↑qq * Complex.I) + Complex.arg (1 - (↑pp - ↑qq * Complex.I)) ≤ a := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have hca : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, ha⟩
  have hre : (↑pp - ↑qq * Complex.I : ℂ).re = pp := by simp
  have him : (↑pp - ↑qq * Complex.I : ℂ).im = -qq := by simp
  have hre1 : (1 - (↑pp - ↑qq * Complex.I) : ℂ).re = 1 - pp := by simp
  have him1 : (1 - (↑pp - ↑qq * Complex.I) : ℂ).im = qq := by
    simp only [Complex.mul_im, Complex.sub_im,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      ]; ring
  have hZre :
      (((pp * (1 - pp) - qq ^ 2 : ℝ) : ℂ) + ↑qq * Complex.I : ℂ).re = pp * (1 - pp) - qq ^ 2 := by
    simp only [Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_re]; ring
  have hZim : (((pp * (1 - pp) - qq ^ 2 : ℝ) : ℂ) + ↑qq * Complex.I : ℂ).im = qq := by
    simp only [Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im]; ring
  rw [hre, him, hre1, him1]
  constructor
  · intro h
    have hA : 0 < pp * (1 - pp) - qq ^ 2 := by
      by_contra hA
      push Not at hA
      nlinarith [mul_pos hq hca, mul_le_mul_of_nonneg_right hA hsa.le]
    have hp0 : 0 < pp := by nlinarith [sq_nonneg pp, sq_nonneg qq]
    have hp1 : pp < 1 := by nlinarith [sq_nonneg qq]
    refine ⟨by linarith, ⟨hp0, by linarith⟩, ⟨by linarith, hq⟩, ?_⟩
    rw [angle_eq (by rw [hre]; exact hp0) (by rw [hre]; exact hp1) (by rw [him]; linarith),
      one_sub_mul_conj, arg_le_iff (by rw [hZre]; exact hA) (by rw [hZim]; exact hq) ha0 ha,
      hZre, hZim]
    exact h
  · rintro ⟨hA, ⟨hp0, -⟩, ⟨hp1, -⟩, hang⟩
    have hA' : 0 < pp * (1 - pp) - qq ^ 2 := by linarith
    rw [angle_eq (by rw [hre]; exact hp0) (by rw [hre]; linarith) (by rw [him]; linarith),
      one_sub_mul_conj, arg_le_iff (by rw [hZre]; exact hA') (by rw [hZim]; exact hq) ha0 ha,
      hZre, hZim] at hang
    exact hang

lemma ii_iff_strict {pp qq a : ℝ} (hq : 0 < qq) (ha0 : 0 < a) (ha : a < π / 2) :
    qq * Real.cos a < (pp * (1 - pp) - qq ^ 2) * Real.sin a ↔
      qq ^ 2 < pp * (1 - pp) ∧
      (0 < (↑pp - ↑qq * Complex.I : ℂ).re ∧ (↑pp - ↑qq * Complex.I : ℂ).im < 0) ∧
      (0 < (1 - (↑pp - ↑qq * Complex.I) : ℂ).re ∧ 0 < (1 - (↑pp - ↑qq * Complex.I) : ℂ).im) ∧
      -Complex.arg (↑pp - ↑qq * Complex.I) + Complex.arg (1 - (↑pp - ↑qq * Complex.I)) < a := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have hca : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, ha⟩
  have hre : (↑pp - ↑qq * Complex.I : ℂ).re = pp := by simp
  have him : (↑pp - ↑qq * Complex.I : ℂ).im = -qq := by simp
  have hre1 : (1 - (↑pp - ↑qq * Complex.I) : ℂ).re = 1 - pp := by simp
  have him1 : (1 - (↑pp - ↑qq * Complex.I) : ℂ).im = qq := by
    simp only [Complex.mul_im, Complex.sub_im,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      ]; ring
  have hZre :
      (((pp * (1 - pp) - qq ^ 2 : ℝ) : ℂ) + ↑qq * Complex.I : ℂ).re = pp * (1 - pp) - qq ^ 2 := by
    simp only [Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_re]; ring
  have hZim : (((pp * (1 - pp) - qq ^ 2 : ℝ) : ℂ) + ↑qq * Complex.I : ℂ).im = qq := by
    simp only [Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im]; ring
  rw [hre, him, hre1, him1]
  constructor
  · intro h
    have hA : 0 < pp * (1 - pp) - qq ^ 2 := by
      by_contra hA
      push Not at hA
      nlinarith [mul_pos hq hca, mul_le_mul_of_nonneg_right hA hsa.le]
    have hp0 : 0 < pp := by nlinarith [sq_nonneg pp, sq_nonneg qq]
    have hp1 : pp < 1 := by nlinarith [sq_nonneg qq]
    refine ⟨by linarith, ⟨hp0, by linarith⟩, ⟨by linarith, hq⟩, ?_⟩
    rw [angle_eq (by rw [hre]; exact hp0) (by rw [hre]; exact hp1) (by rw [him]; linarith),
      one_sub_mul_conj, arg_lt_iff (by rw [hZre]; exact hA) (by rw [hZim]; exact hq) ha0 ha,
      hZre, hZim]
    exact h
  · rintro ⟨hA, ⟨hp0, -⟩, ⟨hp1, -⟩, hang⟩
    have hA' : 0 < pp * (1 - pp) - qq ^ 2 := by linarith
    rw [angle_eq (by rw [hre]; exact hp0) (by rw [hre]; linarith) (by rw [him]; linarith),
      one_sub_mul_conj, arg_lt_iff (by rw [hZre]; exact hA') (by rw [hZim]; exact hq) ha0 ha,
      hZre, hZim] at hang
    exact hang

/-- **Lemma 3.1, (i) ⟺ (ii).** For `1 ≤ m ≤ (K - 1)/2` and `(γ, β) ∈ Ω_cv(Q_{μ,L})`: `q_m > 0`,
and `(γ, β) ∈ Ω°_{K,m}` iff `p_m (1 - p_m) > q_m²`, `M_m` and `1 - M_m` lie in the open fourth and
first quadrants, and `-arg M_m + arg(1 - M_m) ≤ π/K`. -/
theorem lemma_3_1_ii {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L) {K m : ℕ} (hK : 3 ≤ K)
    (hm : m ∈ U K) (h2m : 2 * m < K) {γ β : ℝ} (hp : (γ, β) ∈ Ωcv L) :
    0 < qm μ L γ β K m ∧
    ((γ, β) ∈ ΩRoU μ L K m ↔
      qm μ L γ β K m ^ 2 < pm μ L γ β K m * (1 - pm μ L γ β K m) ∧
      (0 < (M μ L γ β K m).re ∧ (M μ L γ β K m).im < 0) ∧
      (0 < (1 - M μ L γ β K m).re ∧ 0 < (1 - M μ L γ β K m).im) ∧
      -Complex.arg (M μ L γ β K m) + Complex.arg (1 - M μ L γ β K m) ≤ π / K) := by
  have hq := qm_pos hμL hm.1 h2m hp
  obtain ⟨ha0, ha⟩ := pi_div_bounds hK
  refine ⟨hq, ?_⟩
  have key := residual_system_iff hμL hK hm h2m hp
  have key2 := ii_iff (pp := pm μ L γ β K m) hq ha0 ha
  rw [Am] at key
  rw [lemma_3_1 hμ hμL hK hm, M_eq]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, h⟩
    exact key2.1 (key.1 h)
  · intro h
    exact ⟨hp, key.2 (key2.2 h)⟩

/-- **Lemma 3.1, strict version**: all residuals are negative iff (ii) holds with strict
inequalities. -/
theorem lemma_3_1_strict {μ L : ℝ} (hμL : μ < L) {K m : ℕ} (hK : 3 ≤ K)
    (hm : m ∈ U K) (h2m : 2 * m < K) {γ β : ℝ} (hp : (γ, β) ∈ Ωcv L) :
    (∀ Δ, 1 ≤ Δ → Δ < K → ϕ μ L γ β K m Δ < 0) ↔
      qm μ L γ β K m ^ 2 < pm μ L γ β K m * (1 - pm μ L γ β K m) ∧
      (0 < (M μ L γ β K m).re ∧ (M μ L γ β K m).im < 0) ∧
      (0 < (1 - M μ L γ β K m).re ∧ 0 < (1 - M μ L γ β K m).im) ∧
      -Complex.arg (M μ L γ β K m) + Complex.arg (1 - M μ L γ β K m) < π / K := by
  have hq := qm_pos hμL hm.1 h2m hp
  obtain ⟨ha0, ha⟩ := pi_div_bounds hK
  have key := residual_system_iff_strict hμL hK hm h2m hp
  rw [Am] at key
  rw [key, M_eq]
  exact ii_iff_strict hq ha0 ha

lemma isOpen_Ωcv (L : ℝ) : IsOpen (Ωcv L) := by
  have : Ωcv L = {x : ℝ × ℝ | |x.2| < 1} ∩ ({x | 0 < x.1} ∩ {x | x.1 < 2 * (1 + x.2) / L}) := by
    ext x
    simp [Ωcv]
  rw [this]
  exact (isOpen_lt (by fun_prop) continuous_const).inter
    ((isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt (by fun_prop) (by fun_prop)))

lemma ϕ_continuousOn {μ L : ℝ} (hμL : μ < L) (K m Δ : ℕ) :
    ContinuousOn (fun x : ℝ × ℝ => ϕ μ L x.1 x.2 K m Δ) (Ωcv L) := by
  have hden : ∀ x ∈ Ωcv L, (L - μ) * x.1 ≠ 0 := fun x hx =>
    mul_ne_zero (sub_ne_zero.2 hμL.ne') hx.2.1.ne'
  have hp : ContinuousOn (fun x : ℝ × ℝ => pm μ L x.1 x.2 K m) (Ωcv L) := by
    unfold pm
    exact ContinuousOn.div (by fun_prop) (by fun_prop) hden
  have hq : ContinuousOn (fun x : ℝ × ℝ => qm μ L x.1 x.2 K m) (Ωcv L) := by
    unfold qm
    exact ContinuousOn.div (by fun_prop) (by fun_prop) hden
  have e : (fun x : ℝ × ℝ => ϕ μ L x.1 x.2 K m Δ) = fun x =>
      (pm μ L x.1 x.2 K m * (1 - pm μ L x.1 x.2 K m) - qm μ L x.1 x.2 K m ^ 2) *
        (Real.cos ((m * Δ : ℕ) * θ K) - 1) + qm μ L x.1 x.2 K m * Real.sin ((m * Δ : ℕ) * θ K) := by
    funext x
    rw [ϕ_eq, Am]
  rw [e]
  exact (((hp.mul (continuousOn_const.sub hp)).sub (hq.pow 2)).mul continuousOn_const).add
    (hq.mul continuousOn_const)

/-- **Lemma 3.1, interior.** The parameters with all residuals negative form an open subset of
`Ω°_{K,m}`, hence lie in its interior. -/
theorem lemma_3_1_interior {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L) {K m : ℕ} (hK : 3 ≤ K)
    (hm : m ∈ U K) :
    {x | x ∈ Ωcv L ∧ ∀ Δ, 1 ≤ Δ → Δ < K → ϕ μ L x.1 x.2 K m Δ < 0} ⊆
      interior (ΩRoU μ L K m) := by
  apply interior_maximal
  · rintro x ⟨hx, hϕ⟩
    rw [lemma_3_1 hμ hμL hK hm]
    exact ⟨hx, fun Δ h1 h2 => (hϕ Δ h1 h2).le⟩
  · have e : {x | x ∈ Ωcv L ∧ ∀ Δ, 1 ≤ Δ → Δ < K → ϕ μ L x.1 x.2 K m Δ < 0} =
        ⋂ Δ ∈ Finset.Ico 1 K,
          (Ωcv L ∩ (fun x : ℝ × ℝ => ϕ μ L x.1 x.2 K m Δ) ⁻¹' Set.Iio 0) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_Ico, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_Iio]
      constructor
      · rintro ⟨hx, h⟩ Δ ⟨h1, h2⟩
        exact ⟨hx, h Δ h1 h2⟩
      · intro h
        exact ⟨(h 1 ⟨le_rfl, by omega⟩).1, fun Δ h1 h2 => (h Δ ⟨h1, h2⟩).2⟩
    rw [e]
    exact isOpen_biInter_finset fun Δ _ =>
      (ϕ_continuousOn hμL K m Δ).isOpen_inter_preimage (isOpen_Ωcv L) isOpen_Iio

/-! ## Theorem 2.3 from Lemma 3.1 -/

/-- The quadratic `h(v, c)` of Theorem 2.3 (Goujaud et al., 2025b, Thm. 3.5). -/
def hGTD (κ β v c : ℝ) : ℝ :=
  v ^ 2 - 2 * (β - c + κ * (1 - β * c)) * v + 2 * κ * (1 - c) * (1 + β ^ 2 - 2 * β * c)

/-- For `m = 1`, the binding residual `ϕ_{K,1}(1)` is a positive multiple of
`h(μγ, cos θ_K)`. -/
lemma ϕ_one_eq_hGTD {μ L γ β : ℝ} (hμ : 0 < μ) (hμL : μ < L) (hγ : γ ≠ 0) (K : ℕ) :
    μ * ((L - μ) * γ) ^ 2 * ϕ μ L γ β K 1 1 =
      -L * (Real.cos (θ K) - 1) * hGTD (μ / L) β (μ * γ) (Real.cos (θ K)) := by
  have hL : L ≠ 0 := by linarith
  have hℓ0 : L - μ ≠ 0 := sub_ne_zero.2 hμL.ne'
  have hD : (L - μ) * γ ≠ 0 := mul_ne_zero hℓ0 hγ
  have e : ((L - μ) * γ) ^ 2 * ϕ μ L γ β K 1 1 =
      (((1 + β - μ * γ) - (1 + β) * Real.cos (θ K)) *
          ((L - μ) * γ - ((1 + β - μ * γ) - (1 + β) * Real.cos (θ K))) -
        (1 - β) ^ 2 * Real.sin (θ K) ^ 2) * (Real.cos (θ K) - 1) +
      (1 - β) * ((L - μ) * γ) * Real.sin (θ K) ^ 2 := by
    rw [ϕ_eq, Am, pm, qm]
    simp only [Nat.cast_one, one_mul, mul_one]
    field_simp
  have hk : L * (μ / L) = μ := by field_simp
  have hsu := Real.sin_sq_add_cos_sq (θ K)
  rw [mul_assoc, e]
  unfold hGTD
  linear_combination
    (-μ * (β - 1) * (L * γ + β * Real.cos (θ K) - β - γ * μ - Real.cos (θ K) + 1)) * hsu +
    (2 * (Real.cos (θ K) - 1) * (-β ^ 2 * Real.cos (θ K) + β ^ 2 + β * γ * μ * Real.cos (θ K) +
      2 * β * Real.cos (θ K) ^ 2 - 2 * β * Real.cos (θ K) - γ * μ - Real.cos (θ K) + 1)) * hk

/-- **Theorem 2.3** (Goujaud et al., 2025b, Thm. 3.5) as a consequence of Lemma 3.1 with `m = 1`:
`Ω_{K-°-cycle} = {(γ, β) ∈ Ω_cv(Q_{μ,L}) : h(μγ, cos θ_K) ≤ 0}`. -/
theorem theorem_2_3 {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L) {K : ℕ} (hK : 3 ≤ K) :
    ΩRoU μ L K 1 = {x | x ∈ Ωcv L ∧ hGTD (μ / L) x.2 (μ * x.1) (Real.cos (θ K)) ≤ 0} := by
  have h1 : (1 : ℕ) ∈ U K := ⟨le_rfl, by omega, Nat.coprime_one_left K⟩
  rw [lemma_3_1 hμ hμL hK h1]
  ext ⟨γ, β⟩
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun hp => ?_
  have hγ : γ ≠ 0 := hp.2.1.ne'
  have hK0 : K ≠ 0 := by omega
  have hb : (∀ Δ, 1 ≤ Δ → Δ < K → ϕ μ L γ β K 1 Δ ≤ 0) ↔ ϕ μ L γ β K 1 1 ≤ 0 :=
    lemma_3_1_binding hμL hK h1 (by omega) hp (by rw [one_mul, Nat.mod_eq_of_lt (by omega)])
  rw [hb]
  have e := ϕ_one_eq_hGTD (β := β) hμ hμL hγ K
  have hc : Real.cos (θ K) < 1 := by
    have hθ0 : 0 < θ K := by unfold θ; positivity
    have hθ : θ K ≤ π := by
      unfold θ
      have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
      rw [div_le_iff₀ (by linarith)]
      nlinarith [Real.pi_pos]
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ hθ0
    rwa [Real.cos_zero] at this
  have hpos : 0 < μ * ((L - μ) * γ) ^ 2 := by
    have : 0 < ((L - μ) * γ) ^ 2 := by
      have : (L - μ) * γ ≠ 0 := mul_ne_zero (sub_ne_zero.2 hμL.ne') hγ
      positivity
    positivity
  have hL : 0 < L := hμ.trans hμL
  constructor
  · intro h
    by_contra hh
    push Not at hh
    have : 0 < -L * (Real.cos (θ K) - 1) * hGTD (μ / L) β (μ * γ) (Real.cos (θ K)) := by
      have : 0 < -L * (Real.cos (θ K) - 1) := by nlinarith
      positivity
    nlinarith [mul_nonpos_iff.2 (Or.inl ⟨hpos.le, h⟩)]
  · intro h
    have : -L * (Real.cos (θ K) - 1) * hGTD (μ / L) β (μ * γ) (Real.cos (θ K)) ≤ 0 := by
      have : 0 < -L * (Real.cos (θ K) - 1) := by nlinarith
      nlinarith
    by_contra hh
    push Not at hh
    nlinarith [mul_pos hpos hh]

/-! ## Example 3.2 -/

/-- `μ = κ L` with `κ = 4/5`. -/
def exμ (L : ℝ) : ℝ := 4 / 5 * L
/-- `γ` with `L γ = 18/5`. -/
def exγ (L : ℝ) : ℝ := 18 / (5 * L)
/-- `β = 17/20`. -/
def exβ : ℝ := 17 / 20

lemma ex_Ωcv {L : ℝ} (hL : 0 < L) : (exγ L, exβ) ∈ Ωcv L := by
  refine ⟨by norm_num [exβ, abs_lt], by unfold exγ; positivity, ?_⟩
  unfold exγ exβ
  rw [div_lt_div_iff₀ (by positivity) hL]
  nlinarith

lemma ex_μγ {L : ℝ} (hL : 0 < L) : exμ L * exγ L = 72 / 25 := by
  unfold exμ exγ; field_simp; ring

lemma cos_two_θ_five : Real.cos ((2 : ℕ) * θ 5) = -((1 + √5) / 4) := by
  rw [show ((2 : ℕ) : ℝ) * θ 5 = π - π / 5 by unfold θ; push_cast; ring, Real.cos_pi_sub,
    Real.cos_pi_div_five]

lemma sin_two_θ_five : Real.sin ((2 : ℕ) * θ 5) = Real.sin (π / 5) := by
  rw [show ((2 : ℕ) : ℝ) * θ 5 = π - π / 5 by unfold θ; push_cast; ring, Real.sin_pi_sub]

lemma ex_pm {L : ℝ} (hL : 0 < L) : pm (exμ L) L (exγ L) exβ 5 2 = (185 * √5 - 227) / 288 := by
  unfold pm
  rw [cos_two_θ_five]
  unfold exμ exγ exβ
  field_simp
  ring

lemma ex_qm {L : ℝ} (hL : 0 < L) : qm (exμ L) L (exγ L) exβ 5 2 = 5 / 24 * Real.sin (π / 5) := by
  unfold qm
  rw [sin_two_θ_five]
  unfold exμ exγ exβ
  field_simp
  ring

lemma sqrt5_bounds : (221 / 100 : ℝ) < √5 ∧ √5 < 224 / 100 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `p₂(1 - p₂) - q₂² = (17215 √5 - 36285)/10368` (Example 3.2). -/
lemma ex_Am {L : ℝ} (hL : 0 < L) :
    Am (exμ L) L (exγ L) exβ 5 2 = (17215 * √5 - 36285) / 10368 := by
  rw [Am, ex_pm hL, ex_qm hL]
  have hs2 : Real.sin (π / 5) ^ 2 + ((1 + √5) / 4) ^ 2 = 1 := by
    rw [← Real.cos_pi_div_five]; exact Real.sin_sq_add_cos_sq _
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination (-25 / 576) * hs2 + (-2125 / 5184) * h5

/-- `tan(π/5) (p₂(1 - p₂) - q₂²) - q₂ > 0` (Example 3.2). -/
lemma ex_tan {L : ℝ} (hL : 0 < L) :
    0 < Real.tan (π / 5) * Am (exμ L) L (exγ L) exβ 5 2 - qm (exμ L) L (exγ L) exβ 5 2 := by
  rw [ex_Am hL, ex_qm hL, Real.tan_eq_sin_div_cos, Real.cos_pi_div_five]
  have hs : 0 < Real.sin (π / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  have hc : 0 < (1 + √5) / 4 := by positivity
  have : Real.sin (π / 5) / ((1 + √5) / 4) * ((17215 * √5 - 36285) / 10368) -
      5 / 24 * Real.sin (π / 5) =
      Real.sin (π / 5) * ((17215 * √5 - 36285) / 10368 - 5 / 24 * ((1 + √5) / 4)) /
        ((1 + √5) / 4) := by
    field_simp
  rw [this]
  apply div_pos _ hc
  apply mul_pos hs
  nlinarith

/-- The quadratic `h(72/25, c)` of Theorem 2.3 at Example 3.2 has minimum `63/500` on
`[-1/2, 1]`, attained at `c = -1/2`. -/
lemma ex_hGTD_min {L : ℝ} (hL : 0 < L) :
    (∀ c ∈ Set.Icc (-1 / 2 : ℝ) 1, 63 / 500 ≤ hGTD (4 / 5) exβ (exμ L * exγ L) c) ∧
      hGTD (4 / 5) exβ (exμ L * exγ L) (-1 / 2) = 63 / 500 := by
  rw [ex_μγ hL]
  refine ⟨fun c hc => ?_, by norm_num [hGTD, exβ]⟩
  obtain ⟨h1, h2⟩ := hc
  unfold hGTD exβ
  nlinarith [mul_nonneg (show 0 ≤ c + 1 / 2 by linarith)
    (show 0 ≤ 68 / 25 * c + 3551 / 1250 by linarith)]

/-- At Example 3.2, no ordered root-of-unity cycle exists.  This proof follows the manuscript
literally: use Theorem 2.3, place `cos θ_K` in `[-1/2,1]`, and apply the exact minimum
`h(72/25,c) ≥ 63/500 > 0`. -/
lemma ex_not_ordered {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 3 ≤ K) :
    (exγ L, exβ) ∉ ΩRoU (exμ L) L K 1 := by
  have hμ : 0 < exμ L := by unfold exμ; positivity
  have hμL : exμ L < L := by unfold exμ; linarith
  -- PAPER STEP: Theorem 2.3 turns ordered cycling into `h(μγ,cos θ_K) ≤ 0`.
  rw [theorem_2_3 hμ hμL hK]
  rintro ⟨-, hh⟩
  have hkappa : exμ L / L = 4 / 5 := by
    unfold exμ
    field_simp
  have hμγ := ex_μγ hL
  rw [hkappa, hμγ] at hh
  -- PAPER STEP: `cos θ_K ∈ [-1/2,1)` for every `K ≥ 3`.
  have hθ0 : 0 ≤ θ K := by unfold θ; positivity
  have hθ : θ K ≤ 2 * π / 3 := by
    unfold θ
    have hKr : (3 : ℝ) ≤ K := by exact_mod_cast hK
    rw [div_le_div_iff₀ (by linarith [Real.pi_pos]) (by norm_num : (0 : ℝ) < 3)]
    nlinarith [Real.pi_pos, hKr]
  have hcoslo : -(1 / 2 : ℝ) ≤ Real.cos (θ K) := by
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos]) hθ
    rwa [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three] at hc
  have hcoshi : Real.cos (θ K) ≤ 1 := Real.cos_le_one _
  -- `ex_hGTD_min` uses the syntactic endpoint `-1 / 2`, whereas the cosine
  -- estimate above naturally produces `-(1 / 2)`.  Make the equality explicit.
  have hcoslo' : (-1 / 2 : ℝ) ≤ Real.cos (θ K) := by
    calc
      (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
      _ ≤ Real.cos (θ K) := hcoslo
  -- PAPER STEP: the displayed exact minimum is `63/500` on this whole interval.
  have hmin := (ex_hGTD_min hL).1 (Real.cos (θ K)) ⟨hcoslo', hcoshi⟩
  -- Put `hmin` and the Theorem 2.3 inequality `hh` into literally the same
  -- normal form before asking linear arithmetic to close the contradiction.
  rw [hμγ] at hmin
  have hh' : hGTD (4 / 5) exβ (72 / 25) (Real.cos (θ K)) ≤ 0 := by
    simpa using hh
  have h63500 : (0 : ℝ) < 63 / 500 := by norm_num
  linarith [hmin, hh', h63500]


/-- **Example 3.2.** With `κ = 4/5`, `β = 17/20` and `Lγ = 18/5`: `(γ, β) ∈ Ω_cv(Q_{μ,L})`;
condition (ii) of Lemma 3.1 holds strictly for `(K, m) = (5, 2)`; hence
`(γ, β) ∈ int(Ω°_{5,2}) ⊆ int(Ω_{aug-°})`; and `(γ, β) ∉ Ω°_{K',1}` for every `K' ≥ 3`. So
`int(Ω_{aug-°}) \ Ω_{°-cycle} ≠ ∅`. -/
theorem example_3_2 {L : ℝ} (hL : 0 < L) :
    (exγ L, exβ) ∈ Ωcv L ∧
    Am (exμ L) L (exγ L) exβ 5 2 = (17215 * √5 - 36285) / 10368 ∧
    0 < Am (exμ L) L (exγ L) exβ 5 2 ∧
    0 < Real.tan (π / 5) * Am (exμ L) L (exγ L) exβ 5 2 - qm (exμ L) L (exγ L) exβ 5 2 ∧
    (exγ L, exβ) ∈ interior (ΩRoU (exμ L) L 5 2) ∧
    (exγ L, exβ) ∈ interior (Ωaug (exμ L) L) ∧
    (∀ K ≥ 3, (exγ L, exβ) ∉ ΩRoU (exμ L) L K 1) ∧
    (interior (Ωaug (exμ L) L) \ ΩRoUcycle (exμ L) L).Nonempty := by
  have hμ : 0 < exμ L := by unfold exμ; positivity
  have hμL : exμ L < L := by unfold exμ; linarith
  have hp := ex_Ωcv hL
  have h2 : (2 : ℕ) ∈ U 5 := ⟨by norm_num, by norm_num, by norm_num⟩
  obtain ⟨h5a, h5b⟩ := sqrt5_bounds
  have hA := ex_Am hL
  have hApos : 0 < Am (exμ L) L (exγ L) exβ 5 2 := by rw [hA]; nlinarith
  have htan := ex_tan hL
  -- the strict binding inequality `q cos(π/5) < A sin(π/5)`
  have hstrict : qm (exμ L) L (exγ L) exβ 5 2 * Real.cos (π / (5 : ℕ)) <
      Am (exμ L) L (exγ L) exβ 5 2 * Real.sin (π / (5 : ℕ)) := by
    have hc : 0 < Real.cos (π / 5) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    rw [Real.tan_eq_sin_div_cos] at htan
    have := mul_pos htan hc
    push_cast
    field_simp at this ⊢
    nlinarith
  have hint : (exγ L, exβ) ∈ interior (ΩRoU (exμ L) L 5 2) :=
    lemma_3_1_interior hμ hμL (by norm_num) h2
      ⟨hp, (residual_system_iff_strict hμL (by norm_num) h2 (by norm_num) hp).2 hstrict⟩
  have hsub : ΩRoU (exμ L) L 5 2 ⊆ Ωaug (exμ L) L := by
    intro x hx
    simp only [Ωaug, Set.mem_iUnion]
    exact ⟨5, by norm_num, 2, h2, hx⟩
  have hint' := interior_mono hsub hint
  have hnot : ∀ K ≥ 3, (exγ L, exβ) ∉ ΩRoU (exμ L) L K 1 := fun K hK => ex_not_ordered hL hK
  refine ⟨hp, hA, hApos, htan, hint, hint', hnot, ⟨(exγ L, exβ), hint', ?_⟩⟩
  simp only [ΩRoUcycle, Set.mem_iUnion, not_exists]
  exact fun K hK => hnot K hK

end HeavyBall

/-! Each line prints `[propext, Classical.choice, Quot.sound]`: no `sorry`, no further axioms. -/

#print axioms HeavyBall.mixed_condition
#print axioms HeavyBall.lemma_3_1
#print axioms HeavyBall.lemma_3_1_binding
#print axioms HeavyBall.binding_unique
#print axioms HeavyBall.lemma_3_1_reflect
#print axioms HeavyBall.lemma_3_1_binding_reflect
#print axioms HeavyBall.lemma_3_1_ii
#print axioms HeavyBall.lemma_3_1_strict
#print axioms HeavyBall.lemma_3_1_interior
#print axioms HeavyBall.theorem_2_3
#print axioms HeavyBall.example_3_2
#print axioms HeavyBall.ex_hGTD_min

/-!
Supplementary material for "Non-acceleration of the heavy-ball method in 1D".
Part 3 of 4, Section 4: projected cycles and 1D non-acceleration

This is a complete proof for Section 4. The proof follows the manuscript's sort-order argument:

* `paper_phase_interval` is (15) for the midpoint phase (12).
* `paperOrder` is the displayed odd/even sort order.
* `paperOrder_strictMono` verifies that order for `-π/K < φ < 0`.
* `paper_eq14` verifies (14) for each consecutive sorted pair.
* `paper_slope_iff` is the real-part reformulation of the 1D slope bounds.
* `theorem_4_1` uses only consecutive sorted slopes and `theorem_2_2_1d`.
-/

noncomputable section

open Real Filter Topology Set Asymptotics
open scoped RealInnerProductSpace ComplexConjugate

namespace HeavyBall

/-! ## The one-dimensional points and gradients (12)--(13) -/

/-- `m` if `2m < K`, and `K-m` otherwise. -/
def mstar (K m : ℕ) : ℕ := if 2 * m < K then m else K - m

/-- The rotation phase `φ*` of (12). -/
def φstar (μ L γ β : ℝ) (K m : ℕ) : ℝ :=
  -(1 / 2) * Complex.arg ((1 - M μ L γ β K m) * M μ L γ β K m) - π / (2 * K)

/-- The one-dimensional points of (13). -/
def y1 (μ L γ β : ℝ) (K m t : ℕ) : ℝ :=
  2 * Real.cos (m * t * θ K + φstar μ L γ β K m)

/-- The one-dimensional gradient values of (13), with the predecessor read modulo `K`. -/
def g1 (μ L γ β : ℝ) (K m t : ℕ) : ℝ :=
  ((1 + β) * y1 μ L γ β K m t - y1 μ L γ β K m (t + 1) -
      β * y1 μ L γ β K m (t + K - 1)) / γ

lemma mstar_mem {K m : ℕ} (hK : 3 ≤ K) (hm : m ∈ U K) :
    mstar K m ∈ U K ∧ 2 * mstar K m < K := by
  obtain ⟨hm1, hmK, hcop⟩ := hm
  unfold mstar
  split_ifs with h
  · exact ⟨⟨hm1, hmK, hcop⟩, h⟩
  · have hne : 2 * m ≠ K := by
      intro h2
      have h1 : m = 1 := Nat.Coprime.eq_one_of_dvd hcop ⟨2, by omega⟩
      omega
    exact ⟨⟨by omega, by omega, (Nat.coprime_self_sub_left hmK.le).2 hcop⟩, by omega⟩

lemma ΩRoU_mstar {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L)
    {K m : ℕ} (hK : 3 ≤ K) (hm : m ∈ U K) :
    ΩRoU μ L K (mstar K m) = ΩRoU μ L K m := by
  unfold mstar
  split_ifs with h
  · rfl
  · exact lemma_3_1_reflect hμ hμL hK hm

/-! ## The midpoint phase and equation (15) -/

lemma paper_phase_interval {μ L γ β : ℝ} (hμ : 0 < μ) (hμL : μ < L)
    {K m : ℕ} (hK : 3 ≤ K) (hm : m ∈ U K)
    (hp : (γ,β) ∈ ΩRoU μ L K m) :
    -Complex.arg (M μ L γ β K (mstar K m)) - π / K ≤
        φstar μ L γ β K (mstar K m) ∧
      φstar μ L γ β K (mstar K m) ≤
        -Complex.arg (1 - M μ L γ β K (mstar K m)) ∧
      -π / K < φstar μ L γ β K (mstar K m) ∧
        φstar μ L γ β K (mstar K m) < 0 := by
  obtain ⟨hm', h2m'⟩ := mstar_mem hK hm
  have hp' : (γ, β) ∈ ΩRoU μ L K (mstar K m) := by
    rwa [ΩRoU_mstar hμ hμL hK hm]
  have hΩ : (γ, β) ∈ Ωcv L := by
    rw [lemma_3_1 hμ hμL hK hm'] at hp'
    exact hp'.1
  obtain ⟨-, hiff⟩ := lemma_3_1_ii hμ hμL hK hm' h2m' hΩ
  obtain ⟨-, ⟨hMre,hMim⟩, ⟨h1re,h1im⟩, hang⟩ := hiff.1 hp'
  set Mc := M μ L γ β K (mstar K m)
  have hM0 : Mc ≠ 0 := fun h => by rw [h, Complex.zero_re] at hMre; linarith
  have h10 : 1 - Mc ≠ 0 := fun h => by rw [h, Complex.zero_re] at h1re; linarith
  have hargM : Complex.arg Mc < 0 := Complex.arg_neg_iff.2 hMim
  have harg1 : 0 < Complex.arg (1-Mc) := by
    rcases (Complex.arg_nonneg_iff.2 h1im.le).lt_or_eq with h | h
    · exact h
    · have hz := (Complex.arg_eq_zero_iff.1 h.symm).2
      linarith
  have hsum : -Complex.arg Mc + Complex.arg (1-Mc) ≤ π / (K : ℝ) := hang
  have hargsum_lt : Complex.arg Mc + Complex.arg (1-Mc) < π / (K : ℝ) := by
    calc
      Complex.arg Mc + Complex.arg (1-Mc)
          < -Complex.arg Mc + Complex.arg (1-Mc) := by linarith [hargM]
      _ ≤ π / (K : ℝ) := hsum
  have hnegargsum_lt : -Complex.arg Mc - Complex.arg (1-Mc) < π / (K : ℝ) := by
    calc
      -Complex.arg Mc - Complex.arg (1-Mc)
          < -Complex.arg Mc + Complex.arg (1-Mc) := by linarith [harg1]
      _ ≤ π / (K : ℝ) := hsum
  have hargmul : Complex.arg ((1-Mc)*Mc) =
      Complex.arg (1-Mc) + Complex.arg Mc := by
    rw [Complex.arg_mul h10 hM0]
    constructor
    · have hlo := Complex.neg_pi_lt_arg Mc
      linarith
    · have hhi := Complex.arg_le_pi (1-Mc)
      linarith
  have hφ : φstar μ L γ β K (mstar K m) =
      (-Complex.arg Mc - Complex.arg (1-Mc)) / 2 - π / (2*K) := by
    rw [φstar, hargmul]
    ring
  have hK0r : (K : ℝ) ≠ 0 := by
    exact_mod_cast (show K ≠ 0 by omega)
  have hhalf : π / (2 * (K : ℝ)) = (π / (K : ℝ)) / 2 := by
    field_simp [hK0r]
  rw [hhalf] at hφ
  rw [hφ]
  constructor
  · linarith [hsum]
  constructor
  · linarith [hsum]
  constructor
  · have hgap : 0 < π / (K : ℝ) - (Complex.arg Mc + Complex.arg (1 - Mc)) :=
      sub_pos.mpr hargsum_lt
    have hgap_half :
        0 < (π / (K : ℝ) - (Complex.arg Mc + Complex.arg (1 - Mc))) / 2 := by
      exact div_pos hgap (by norm_num)
    calc
      -π / (K : ℝ) <
          -π / (K : ℝ) +
            (π / (K : ℝ) - (Complex.arg Mc + Complex.arg (1 - Mc))) / 2 := by
              have h := add_lt_add_left hgap_half (-π / (K : ℝ))
              simpa using h
      _ = (-Complex.arg Mc - Complex.arg (1 - Mc)) / 2 - π / (K : ℝ) / 2 := by
          ring
  · linarith [hnegargsum_lt]

/-! ## The displayed sort order before equation (14) -/

/-- The explicit order printed in the manuscript.

For `K=2r+1`: `r+1,r,r+2,r-1,...,2r,1,0`.
For `K=2r`:   `r,r+1,r-1,r+2,...,2r-1,1,0`.
-/
def paperOrder (K n : ℕ) : ℕ :=
  let r := K / 2
  if K % 2 = 1 then
    if n % 2 = 0 then (r + 1 + n / 2) % K else r - n / 2
  else
    if n % 2 = 0 then r - n / 2 else (r + 1 + n / 2) % K

lemma paperOrder_lt {K n : ℕ} (_hK : 3 ≤ K) : paperOrder K n < K := by
  unfold paperOrder
  have hK0 : 0 < K := by omega
  split_ifs
  · exact Nat.mod_lt _ hK0
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.div_lt_self hK0 (by omega))
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.div_lt_self hK0 (by omega))
  · exact Nat.mod_lt _ hK0

/-- Arithmetic content of the displayed order. -/
lemma paperOrder_step_relation {K n : ℕ} (_hK : 3 ≤ K) (hn : n + 1 < K) :
    let a := paperOrder K n
    let b := paperOrder K (n + 1)
    (a + b = K ∧ b < a) ∨ (a + b = K + 1 ∧ a < b) ∨ (a = 1 ∧ b = 0) := by
  have hKrem : K % 2 < 2 := Nat.mod_lt _ (by omega)
  have hnrem : n % 2 < 2 := Nat.mod_lt _ (by omega)
  have hsrem : (n + 1) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hKdec : K % 2 + 2 * (K / 2) = K := Nat.mod_add_div K 2
  have hndec : n % 2 + 2 * (n / 2) = n := Nat.mod_add_div n 2
  have hsdec : (n + 1) % 2 + 2 * ((n + 1) / 2) = n + 1 := Nat.mod_add_div (n + 1) 2
  unfold paperOrder
  by_cases hKo : K % 2 = 1
  · have hKodd : K % 2 = 1 := hKo
    simp only [hKo, ite_true]
    by_cases hne : n % 2 = 0
    · have hso : (n + 1) % 2 = 1 := by omega
      simp only [hne, ite_true, hso, one_ne_zero, ite_false]
      have hraw : K / 2 + 1 + n / 2 < K := by omega
      rw [Nat.mod_eq_of_lt hraw]
      left
      constructor <;> omega
    · have hno : n % 2 = 1 := by omega
      have hse : (n + 1) % 2 = 0 := by omega
      simp only [hne, ite_false, hse, ite_true]
      by_cases heq : K / 2 + 1 + (n + 1) / 2 = K
      · rw [heq, Nat.mod_self]
        right; right
        constructor <;> omega
      · have hraw : K / 2 + 1 + (n + 1) / 2 < K := by omega
        rw [Nat.mod_eq_of_lt hraw]
        right; left
        constructor <;> omega
  · have hKe : K % 2 = 0 := by omega
    simp only [hKo, ite_false]
    by_cases hne : n % 2 = 0
    · have hso : (n + 1) % 2 = 1 := by omega
      simp only [hne, ite_true, hso, one_ne_zero, ite_false]
      by_cases heq : K / 2 + 1 + (n + 1) / 2 = K
      · rw [heq, Nat.mod_self]
        right; right
        constructor <;> omega
      · have hraw : K / 2 + 1 + (n + 1) / 2 < K := by omega
        rw [Nat.mod_eq_of_lt hraw]
        right; left
        constructor <;> omega
    · have hno : n % 2 = 1 := by omega
      have hse : (n + 1) % 2 = 0 := by omega
      simp only [hne, ite_false, hse, ite_true]
      have hraw : K / 2 + 1 + n / 2 < K := by omega
      rw [Nat.mod_eq_of_lt hraw]
      left
      constructor <;> omega

/-- The numbers sorted in the manuscript. -/
def paperRootValue (K : ℕ) (φ : ℝ) (l : ℕ) : ℝ :=
  Real.cos ((l : ℝ) * θ K + φ)

private lemma paper_halfdiff (K a b : ℕ) (φ : ℝ) :
    (((b : ℝ) * θ K + φ) - ((a : ℝ) * θ K + φ)) / 2 =
      ((b : ℝ) - a) * (π / (K : ℝ)) := by
  unfold θ
  ring

private lemma paper_halfavg (K a b : ℕ) (φ : ℝ) :
    (((b : ℝ) * θ K + φ) + ((a : ℝ) * θ K + φ)) / 2 =
      φ + ((a : ℝ) + b) * (π / (K : ℝ)) := by
  unfold θ
  ring

lemma paperOrder_step_cos {K n : ℕ} (hK : 3 ≤ K) (hn : n + 1 < K)
    {φ : ℝ} (hφlo : -π / K < φ) (hφhi : φ < 0) :
    paperRootValue K φ (paperOrder K n) <
      paperRootValue K φ (paperOrder K (n + 1)) := by
  let a := paperOrder K n
  let b := paperOrder K (n + 1)
  have haK : a < K := paperOrder_lt hK
  have hbK : b < K := paperOrder_lt hK
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hπK : 0 < π / (K : ℝ) := div_pos Real.pi_pos hKr
  have hπKlt : π / (K : ℝ) < π := by
    rw [div_lt_iff₀ hKr]
    have hK3 : (3 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith [Real.pi_pos]
  have hKcancel : (K : ℝ) * (π / (K : ℝ)) = π := by
    field_simp [hKr.ne']
  have hrel0 := paperOrder_step_relation hK hn
  change (a + b = K ∧ b < a) ∨ (a + b = K + 1 ∧ a < b) ∨ (a = 1 ∧ b = 0) at hrel0
  obtain hrel | hrel | hrel := hrel0
  · obtain ⟨hsum, hba⟩ := hrel
    have hsumR : (a : ℝ) + b = K := by exact_mod_cast hsum
    have hbaR : (b : ℝ) < a := by exact_mod_cast hba
    have hδneg :
        (((b : ℝ) * θ K + φ) - ((a : ℝ) * θ K + φ)) / 2 < 0 := by
      rw [paper_halfdiff]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hbaR) hπK
    have hδlo :
        -π < (((b : ℝ) * θ K + φ) - ((a : ℝ) * θ K + φ)) / 2 := by
      rw [paper_halfdiff]
      have hlow : -(K : ℝ) < (b : ℝ) - a := by
        have haR : (a : ℝ) < K := by exact_mod_cast haK
        have hbR : (0 : ℝ) ≤ b := by positivity
        linarith
      have hm := mul_lt_mul_of_pos_right hlow hπK
      have hleft : (-(K : ℝ)) * (π / (K : ℝ)) = -π := by
        rw [neg_mul, hKcancel]
      rwa [hleft] at hm
    have havg :
        (((b : ℝ) * θ K + φ) + ((a : ℝ) * θ K + φ)) / 2 = φ + π := by
      rw [paper_halfavg, hsumR, hKcancel]
    have hφlo' : -(π / (K : ℝ)) < φ := by
      simpa [neg_div] using hφlo
    have hφgt : -π < φ := by
      have hneg : -π < -(π / (K : ℝ)) := by linarith
      exact lt_trans hneg hφlo'
    have hsφ : Real.sin φ < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt hφhi hφgt
    have savg :
        0 < Real.sin ((((b : ℝ) * θ K + φ) + ((a : ℝ) * θ K + φ)) / 2) := by
      rw [havg, Real.sin_add_pi]
      linarith
    rw [havg] at savg
    have sdiff :
        Real.sin ((((b : ℝ) * θ K + φ) - ((a : ℝ) * θ K + φ)) / 2) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt hδneg hδlo
    have hcos :
        0 < Real.cos ((b : ℝ) * θ K + φ) - Real.cos ((a : ℝ) * θ K + φ) := by
      rw [Real.cos_sub_cos, havg]
      have hneg : -2 * Real.sin (φ + π) < 0 := by nlinarith
      exact mul_pos_of_neg_of_neg hneg sdiff
    change Real.cos ((a : ℝ) * θ K + φ) < Real.cos ((b : ℝ) * θ K + φ)
    exact sub_pos.mp hcos
  · obtain ⟨hsum, hab⟩ := hrel
    have hsumR : (a : ℝ) + b = K + 1 := by exact_mod_cast hsum
    have habR : (a : ℝ) < b := by exact_mod_cast hab
    have hδ0 :
        0 < (((b : ℝ) * θ K + φ) - ((a : ℝ) * θ K + φ)) / 2 := by
      rw [paper_halfdiff]
      exact mul_pos (sub_pos.mpr habR) hπK
    have hδπ :
        (((b : ℝ) * θ K + φ) - ((a : ℝ) * θ K + φ)) / 2 < π := by
      rw [paper_halfdiff]
      have hu : (b : ℝ) - a < K := by
        have hbR : (b : ℝ) < K := by exact_mod_cast hbK
        have haR : (0 : ℝ) ≤ a := by positivity
        linarith
      have hm := mul_lt_mul_of_pos_right hu hπK
      rwa [hKcancel] at hm
    have havg :
        (((b : ℝ) * θ K + φ) + ((a : ℝ) * θ K + φ)) / 2 =
          φ + π + π / (K : ℝ) := by
      rw [paper_halfavg, hsumR]
      calc
        φ + ((K : ℝ) + 1) * (π / (K : ℝ))
            = φ + (K : ℝ) * (π / (K : ℝ)) + π / (K : ℝ) := by ring
        _ = φ + π + π / (K : ℝ) := by rw [hKcancel]
    have hφlo' : -(π / (K : ℝ)) < φ := by
      simpa [neg_div] using hφlo
    have hu0 : 0 < φ + π / (K : ℝ) := by linarith
    have huπ : φ + π / (K : ℝ) < π := by linarith [hπKlt]
    have su : 0 < Real.sin (φ + π / (K : ℝ)) :=
      Real.sin_pos_of_pos_of_lt_pi hu0 huπ
    have savg :
        Real.sin ((((b : ℝ) * θ K + φ) + ((a : ℝ) * θ K + φ)) / 2) < 0 := by
      rw [havg, show φ + π + π / (K : ℝ) = (φ + π / (K : ℝ)) + π by ring,
        Real.sin_add_pi]
      linarith
    rw [havg] at savg
    have sdiff :
        0 < Real.sin ((((b : ℝ) * θ K + φ) - ((a : ℝ) * θ K + φ)) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi hδ0 hδπ
    have hcos :
        0 < Real.cos ((b : ℝ) * θ K + φ) - Real.cos ((a : ℝ) * θ K + φ) := by
      rw [Real.cos_sub_cos, havg]
      have hpos : 0 < -2 * Real.sin (φ + π + π / (K : ℝ)) := by nlinarith
      exact mul_pos hpos sdiff
    change Real.cos ((a : ℝ) * θ K + φ) < Real.cos ((b : ℝ) * θ K + φ)
    exact sub_pos.mp hcos
  · obtain ⟨ha, hb⟩ := hrel
    have havg :
        (((0 : ℝ) * θ K + φ) + ((1 : ℝ) * θ K + φ)) / 2 =
          φ + π / (K : ℝ) := by
      unfold θ
      ring
    have hδ :
        (((0 : ℝ) * θ K + φ) - ((1 : ℝ) * θ K + φ)) / 2 =
          -π / (K : ℝ) := by
      unfold θ
      ring
    have hφlo' : -(π / (K : ℝ)) < φ := by
      simpa [neg_div] using hφlo
    have hu0 : 0 < φ + π / (K : ℝ) := by linarith
    have huπ : φ + π / (K : ℝ) < π := by linarith [hπKlt]
    have savg : 0 < Real.sin (φ + π / (K : ℝ)) :=
      Real.sin_pos_of_pos_of_lt_pi hu0 huπ
    have hnegpi : -π < -π / (K : ℝ) := by linarith [hπKlt]
    have sdiff : Real.sin (-π / (K : ℝ)) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hπK]) hnegpi
    have hcos :
        0 < Real.cos ((0 : ℝ) * θ K + φ) - Real.cos ((1 : ℝ) * θ K + φ) := by
      rw [Real.cos_sub_cos, havg, hδ]
      have hneg : -2 * Real.sin (φ + π / (K : ℝ)) < 0 := by nlinarith
      exact mul_pos_of_neg_of_neg hneg sdiff
    change paperRootValue K φ a < paperRootValue K φ b
    simpa [paperRootValue, ha, hb] using (sub_pos.mp hcos)

/-- The displayed list is genuinely the strict increasing sort order. -/
lemma paperOrder_strictMono {K : ℕ} (hK : 3 ≤ K) {φ : ℝ}
    (hφlo : -π / K < φ) (hφhi : φ < 0) :
    StrictMono (fun i : Fin K => paperRootValue K φ (paperOrder K i)) := by
  have H : ∀ j : ℕ, j < K → ∀ i : ℕ, i < j →
      paperRootValue K φ (paperOrder K i) < paperRootValue K φ (paperOrder K j) := by
    intro j
    induction j with
    | zero =>
        intro hj i hi
        omega
    | succ j ih =>
        intro hj i hi
        by_cases h : i = j
        · subst i
          exact paperOrder_step_cos hK (by omega) hφlo hφhi
        · have hij : i < j := by omega
          exact lt_trans (ih (by omega) i hij)
            (paperOrder_step_cos hK (by omega) hφlo hφhi)
  intro i j hij
  exact H j.1 j.2 i.1 hij

/-- The root-label map from sorted position to label is a permutation. -/
lemma paperOrder_bijective {K : ℕ} (hK : 3 ≤ K) {φ : ℝ}
    (hφlo : -π / K < φ) (hφhi : φ < 0) :
    Function.Bijective (fun i : Fin K =>
      (⟨paperOrder K i, paperOrder_lt hK⟩ : Fin K)) := by
  let p : Fin K → Fin K := fun i => ⟨paperOrder K i, paperOrder_lt hK⟩
  have hmono := paperOrder_strictMono hK hφlo hφhi
  have hinj : Function.Injective p := by
    intro i j hij
    apply hmono.injective
    change paperRootValue K φ (paperOrder K i) = paperRootValue K φ (paperOrder K j)
    have hv : paperOrder K i = paperOrder K j := congrArg Fin.val hij
    exact congrArg (paperRootValue K φ) hv
  exact hinj.bijective_of_finite

/-! ## The paper chord and equation (14) -/

private def paperAngle (K : ℕ) (φ : ℝ) (l : ℕ) : ℝ :=
  (l : ℝ) * θ K + φ

private def paperY (K : ℕ) (φ : ℝ) (l : ℕ) : ℝ :=
  2 * Real.cos (paperAngle K φ l)

private def paperG (γ β : ℝ) (K m : ℕ) (φ : ℝ) (l : ℕ) : ℝ :=
  2 * ((Mhat γ β K m).re * Real.cos (paperAngle K φ l) -
    (Mhat γ β K m).im * Real.sin (paperAngle K φ l))

/-- `w_{a,b}` as a complex chord.  This is exactly
`e^{iφ}(ω_K^b-ω_K^a)` written in Cartesian coordinates. -/
def paperW (K : ℕ) (φ : ℝ) (a b : ℕ) : ℂ :=
  ⟨Real.cos (paperAngle K φ b) - Real.cos (paperAngle K φ a),
    Real.sin (paperAngle K φ b) - Real.sin (paperAngle K φ a)⟩

lemma paperW_re (K : ℕ) (φ : ℝ) (a b : ℕ) :
    (paperW K φ a b).re =
      Real.cos (paperAngle K φ b) - Real.cos (paperAngle K φ a) := rfl

lemma paperW_im (K : ℕ) (φ : ℝ) (a b : ℕ) :
    (paperW K φ a b).im =
      Real.sin (paperAngle K φ b) - Real.sin (paperAngle K φ a) := rfl

/-- Chord factorization used to read off its direction. -/
lemma paperW_factor {K a b : ℕ} (φ : ℝ) :
    paperW K φ a b =
      ((2 * Real.sin ((((b : ℝ) * θ K) - ((a : ℝ) * θ K)) / 2) : ℝ) : ℂ) *
        Complex.exp (((φ + (((a : ℝ) * θ K + (b : ℝ) * θ K) / 2) + π / 2 : ℝ) : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp only [paperW_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [Real.cos_sub_cos,
      show (paperAngle K φ b + paperAngle K φ a) / 2 =
        φ + (((a : ℝ) * θ K + (b : ℝ) * θ K) / 2) by
          unfold paperAngle; ring,
      show (paperAngle K φ b - paperAngle K φ a) / 2 =
        (((b : ℝ) * θ K - (a : ℝ) * θ K) / 2) by
          unfold paperAngle; ring,
      Real.cos_add_pi_div_two]
    ring
  · simp only [paperW_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [Real.sin_sub_sin,
      show (paperAngle K φ b + paperAngle K φ a) / 2 =
        φ + (((a : ℝ) * θ K + (b : ℝ) * θ K) / 2) by
          unfold paperAngle; ring,
      show (paperAngle K φ b - paperAngle K φ a) / 2 =
        (((b : ℝ) * θ K - (a : ℝ) * θ K) / 2) by
          unfold paperAngle; ring,
      Real.sin_add_pi_div_two]
    ring

private lemma arg_pos_ray {r α : ℝ} (hr : 0 < r) (hα : α ∈ Set.Ioc (-π) π) :
    Complex.arg (((r : ℝ) : ℂ) * Complex.exp (((α : ℝ) : ℂ) * Complex.I)) = α := by
  rw [Complex.exp_ofReal_mul_I]
  simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
    (Complex.arg_mul_cos_add_sin_mul_I hr hα)

private lemma exp_ray_add_pi (r α : ℝ) :
    ((-r : ℝ) : ℂ) * Complex.exp (((α + π : ℝ) : ℂ) * Complex.I) =
      ((r : ℝ) : ℂ) * Complex.exp (((α : ℝ) : ℂ) * Complex.I) := by
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  · rw [Real.cos_add_pi]
    ring
  · rw [Real.sin_add_pi]
    ring

private lemma exp_ray_add_two_pi (r α : ℝ) :
    ((r : ℝ) : ℂ) * Complex.exp (((α + 2 * π : ℝ) : ℂ) * Complex.I) =
      ((r : ℝ) : ℂ) * Complex.exp (((α : ℝ) : ℂ) * Complex.I) := by
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  · rw [Real.cos_add_two_pi]
    ring
  · rw [Real.sin_add_two_pi]
    ring

/-- Equation (14), for consecutive entries of the displayed sort order. -/
lemma paper_eq14 {K n : ℕ} (hK : 3 ≤ K) (hn : n + 1 < K)
    {φ : ℝ} (hφlo : -π / K < φ) (hφhi : φ < 0) :
    let a := paperOrder K n
    let b := paperOrder K (n + 1)
    Complex.arg (paperW K φ a b) = π / 2 + φ ∨
      Complex.arg (paperW K φ a b) = -π / 2 + π / K + φ := by
  dsimp
  set a := paperOrder K n
  set b := paperOrder K (n + 1)
  -- change Complex.arg (paperW K φ a b) = π / 2 + φ ∨
  --   Complex.arg (paperW K φ a b) = -π / 2 + π / K + φ
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hπK : 0 < π / (K : ℝ) := div_pos Real.pi_pos hKr
  have hπKhalf : π / (K : ℝ) < π / 2 := (pi_div_bounds hK).2
  have hφlo' : -(π / (K : ℝ)) < φ := by
    simpa [neg_div] using hφlo
  have hrel0 := paperOrder_step_relation hK hn
  change (a + b = K ∧ b < a) ∨ (a + b = K + 1 ∧ a < b) ∨ (a = 1 ∧ b = 0) at hrel0
  obtain hrel | hrel | hrel := hrel0
  · obtain ⟨hsum, hba⟩ := hrel
    left
    rw [paperW_factor]
    have hsumR : (a : ℝ) + b = K := by exact_mod_cast hsum
    have hbaR : (b : ℝ) < a := by exact_mod_cast hba
    have hδneg : (((b : ℝ) * θ K - (a : ℝ) * θ K) / 2) < 0 := by
      rw [show ((b : ℝ) * θ K - (a : ℝ) * θ K) / 2 =
        ((b : ℝ) - a) * (π / (K : ℝ)) by unfold θ; ring]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hbaR) hπK
    have hδlo : -π < ((b : ℝ) * θ K - (a : ℝ) * θ K) / 2 := by
      rw [show ((b : ℝ) * θ K - (a : ℝ) * θ K) / 2 =
        ((b : ℝ) - a) * (π / (K : ℝ)) by unfold θ; ring]
      have haK : a < K := paperOrder_lt hK
      have hlow : -(K : ℝ) < (b : ℝ) - a := by
        have haR : (a : ℝ) < K := by exact_mod_cast haK
        have hbR : (0 : ℝ) ≤ b := by positivity
        linarith
      have hm := mul_lt_mul_of_pos_right hlow hπK
      have hleft : (-(K : ℝ)) * (π / (K : ℝ)) = -π := by
        field_simp [hKr.ne']
      rwa [hleft] at hm
    have hsneg : Real.sin (((b : ℝ) * θ K - (a : ℝ) * θ K) / 2) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt hδneg hδlo
    have hr : 0 < -(2 * Real.sin (((b : ℝ) * θ K - (a : ℝ) * θ K) / 2)) := by
      nlinarith
    have havg : ((a : ℝ) * θ K + (b : ℝ) * θ K) / 2 = π := by
      unfold θ
      have hKcancel : (K : ℝ) * (π / (K : ℝ)) = π := by field_simp [hKr.ne']
      calc
        ((a : ℝ) * (2 * π / (K : ℝ)) + (b : ℝ) * (2 * π / (K : ℝ))) / 2
            = ((a : ℝ) + b) * (π / (K : ℝ)) := by ring
        _ = (K : ℝ) * (π / (K : ℝ)) := by rw [hsumR]
        _ = π := hKcancel
    rw [havg]
    have heq :
        ((2 * Real.sin (((b : ℝ) * θ K - (a : ℝ) * θ K) / 2) : ℝ) : ℂ) *
            Complex.exp (((φ + π + π / 2 : ℝ) : ℂ) * Complex.I) =
          (((-(2 * Real.sin (((b : ℝ) * θ K - (a : ℝ) * θ K) / 2)) : ℝ) : ℂ) *
            Complex.exp ((((π / 2 + φ) : ℝ) : ℂ) * Complex.I)) := by
      have hshift : φ + π + π / 2 = (π / 2 + φ) + π := by ring
      rw [hshift]
      simpa using
        (exp_ray_add_pi (-(2 * Real.sin (((b : ℝ) * θ K - (a : ℝ) * θ K) / 2)))
          (π / 2 + φ))
    rw [heq]
    have hα0 : 0 < π / 2 + φ := by
      linarith [hφlo', hπKhalf]
    have hα : π / 2 + φ ∈ Set.Ioc (-π) π := by
      constructor
      · linarith [hα0, Real.pi_pos]
      · linarith [hφhi, Real.pi_pos]
    exact arg_pos_ray hr hα
  · obtain ⟨hsum, hab⟩ := hrel
    right
    rw [paperW_factor]
    have hsumR : (a : ℝ) + b = K + 1 := by exact_mod_cast hsum
    have habR : (a : ℝ) < b := by exact_mod_cast hab
    have hδ0 : 0 < ((b : ℝ) * θ K - (a : ℝ) * θ K) / 2 := by
      rw [show ((b : ℝ) * θ K - (a : ℝ) * θ K) / 2 =
        ((b : ℝ) - a) * (π / (K : ℝ)) by unfold θ; ring]
      exact mul_pos (sub_pos.mpr habR) hπK
    have hδπ : ((b : ℝ) * θ K - (a : ℝ) * θ K) / 2 < π := by
      rw [show ((b : ℝ) * θ K - (a : ℝ) * θ K) / 2 =
        ((b : ℝ) - a) * (π / (K : ℝ)) by unfold θ; ring]
      have hbK : b < K := paperOrder_lt hK
      have hu : (b : ℝ) - a < K := by
        have hbR : (b : ℝ) < K := by exact_mod_cast hbK
        have haR : (0 : ℝ) ≤ a := by positivity
        linarith
      have hm := mul_lt_mul_of_pos_right hu hπK
      have hright : (K : ℝ) * (π / (K : ℝ)) = π := by field_simp [hKr.ne']
      rwa [hright] at hm
    have hspos : 0 < Real.sin (((b : ℝ) * θ K - (a : ℝ) * θ K) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi hδ0 hδπ
    have hr : 0 < 2 * Real.sin (((b : ℝ) * θ K - (a : ℝ) * θ K) / 2) := by
      nlinarith
    have havg : ((a : ℝ) * θ K + (b : ℝ) * θ K) / 2 = π + π / (K : ℝ) := by
      unfold θ
      have hKcancel : (K : ℝ) * (π / (K : ℝ)) = π := by field_simp [hKr.ne']
      calc
        ((a : ℝ) * (2 * π / (K : ℝ)) + (b : ℝ) * (2 * π / (K : ℝ))) / 2
            = ((a : ℝ) + b) * (π / (K : ℝ)) := by ring
        _ = ((K : ℝ) + 1) * (π / (K : ℝ)) := by rw [hsumR]
        _ = (K : ℝ) * (π / (K : ℝ)) + π / (K : ℝ) := by ring
        _ = π + π / (K : ℝ) := by rw [hKcancel]
    rw [havg]
    have hbase : φ + (π + π / (K : ℝ)) + π / 2 =
        (-π / 2 + π / (K : ℝ) + φ) + 2 * π := by ring
    rw [hbase]
    have heq := exp_ray_add_two_pi
      (2 * Real.sin (((b : ℝ) * θ K - (a : ℝ) * θ K) / 2))
      (-π / 2 + π / (K : ℝ) + φ)
    rw [heq]
    have hα : -π / 2 + π / (K : ℝ) + φ ∈ Set.Ioc (-π) π := by
      constructor
      · linarith [hφlo', Real.pi_pos]
      · linarith [hφhi, hπKhalf, Real.pi_pos]
    exact arg_pos_ray hr hα
  · obtain ⟨ha, hb⟩ := hrel
    right
    rw [ha, hb, paperW_factor]
    simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul]
    have hδ : (0 - θ K) / 2 = -π / (K : ℝ) := by
      unfold θ
      ring
    rw [hδ]
    have hnegpi : -π < -π / (K : ℝ) := by
      have hπKlt : π / (K : ℝ) < π := by
        exact lt_trans hπKhalf (by linarith [Real.pi_pos])
      simpa [neg_div] using (neg_lt_neg hπKlt)
    have hsneg : Real.sin (-π / (K : ℝ)) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hπK]) hnegpi
    have hr : 0 < -(2 * Real.sin (-π / (K : ℝ))) := by nlinarith
    have havg : (θ K + 0) / 2 = π / (K : ℝ) := by
      unfold θ
      ring
    rw [havg]
    have hshift : φ + π / (K : ℝ) + π / 2 =
        (-π / 2 + π / (K : ℝ) + φ) + π := by ring
    rw [hshift]
    have hrewrite :
        ((2 * Real.sin (-π / (K : ℝ)) : ℝ) : ℂ) *
            Complex.exp ((((-π / 2 + π / (K : ℝ) + φ) + π : ℝ) : ℂ) * Complex.I) =
          (((-(2 * Real.sin (-π / (K : ℝ))) : ℝ) : ℂ) *
            Complex.exp (((-π / 2 + π / (K : ℝ) + φ : ℝ) : ℂ) * Complex.I)) := by
      simpa using (exp_ray_add_pi (-(2 * Real.sin (-π / (K : ℝ))))
        (-π / 2 + π / (K : ℝ) + φ))
    rw [hrewrite]
    have hα : -π / 2 + π / (K : ℝ) + φ ∈ Set.Ioc (-π) π := by
      constructor
      · linarith [hφlo', Real.pi_pos]
      · linarith [hφhi, hπKhalf, Real.pi_pos]
    exact arg_pos_ray hr hα

/-! ## Slope inequalities in the paper's complex form -/

lemma paperW_differences {γ β : ℝ} {K m a b : ℕ} {φ : ℝ} :
    paperY K φ b - paperY K φ a = 2 * (paperW K φ a b).re ∧
    paperG γ β K m φ b - paperG γ β K m φ a =
      2 * (Mhat γ β K m * paperW K φ a b).re := by
  constructor
  · simp [paperY, paperW]
    ring
  · simp only [paperG, paperW, Complex.mul_re]
    ring

private lemma paper_slope_iff {μ L γ β : ℝ} (hμL : μ < L) (hγ : γ ≠ 0)
    {K m : ℕ} {w : ℂ} (hwre : 0 < w.re) :
    let dy := 2 * w.re
    let dg := 2 * (Mhat γ β K m * w).re
    (μ ≤ dg / dy ∧ dg / dy ≤ L) ↔
      0 ≤ (M μ L γ β K m * w).re ∧ 0 ≤ ((1 - M μ L γ β K m) * w).re := by
  dsimp
  have hdy : 0 < 2 * w.re := by linarith
  have hMhatC :
      Mhat γ β K m * w =
        (μ : ℂ) * w + ((L - μ : ℝ) : ℂ) * (M μ L γ β K m * w) := by
    rw [Mhat_eq (β := β) hγ hμL.ne K m]
    ring
  have hMhat := congrArg Complex.re hMhatC
  have hMhat :
      (Mhat γ β K m * w).re =
        μ * w.re + (L - μ) * (M μ L γ β K m * w).re := by
    simpa [Complex.mul_re] using hMhat
  have hOneC : (1 - M μ L γ β K m) * w =
      w - M μ L γ β K m * w := by ring
  have hOne := congrArg Complex.re hOneC
  have hOne :
      ((1 - M μ L γ β K m) * w).re =
        w.re - (M μ L γ β K m * w).re := by
    simpa using hOne
  rw [hMhat, hOne]
  constructor
  · rintro ⟨hlo, hhi⟩
    rw [le_div_iff₀ hdy] at hlo
    rw [div_le_iff₀ hdy] at hhi
    constructor <;> nlinarith [sub_pos.2 hμL]
  · rintro ⟨hlo, hhi⟩
    rw [le_div_iff₀ hdy, div_le_iff₀ hdy]
    constructor <;> nlinarith [sub_pos.2 hμL]

private lemma re_mul_arg (z w : ℂ) :
    (z * w).re = ‖z‖ * ‖w‖ * Real.cos (Complex.arg z + Complex.arg w) := by
  rw [Complex.mul_re,
    ← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z,
    ← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg w,
    Real.cos_add]
  ring

private lemma eq14_gives_realpart {M0 w : ℂ} {K : ℕ} (hK : 3 ≤ K)
    {φ : ℝ}
    (_hargM : -(π / 2) < Complex.arg M0) (hargM0 : Complex.arg M0 < 0)
    (harg1 : 0 < Complex.arg (1 - M0)) (_harg1' : Complex.arg (1 - M0) < π / 2)
    (hφ1 : -Complex.arg M0 - π / K ≤ φ)
    (hφ2 : φ ≤ -Complex.arg (1 - M0))
    (hφlo : -π / K < φ) (hφhi : φ < 0)
    (hwarg : Complex.arg w = π / 2 + φ ∨
      Complex.arg w = -π / 2 + π / K + φ) :
    0 ≤ (M0 * w).re ∧ 0 ≤ ((1 - M0) * w).re := by
  have hkhalf : π / (K : ℝ) < π / 2 := (pi_div_bounds hK).2
  have hkpos : 0 < π / (K : ℝ) := (pi_div_bounds hK).1
  have hφlo' : -(π / (K : ℝ)) < φ := by
    simpa [neg_div] using hφlo
  have hreM := re_mul_arg M0 w
  have hre1 := re_mul_arg (1 - M0) w
  have hnormM : 0 ≤ ‖M0‖ := norm_nonneg _
  have hnorm1 : 0 ≤ ‖1 - M0‖ := norm_nonneg _
  have hnormw : 0 ≤ ‖w‖ := norm_nonneg _
  have cosM : 0 ≤ Real.cos (Complex.arg M0 + Complex.arg w) := by
    rcases hwarg with hwarg | hwarg
    · rw [hwarg]
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · linarith [hφ1, hkhalf, Real.pi_pos]
      · linarith [hargM0, hφhi]
    · rw [hwarg]
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · linarith [hφ1]
      · linarith [hargM0, hφhi, hkhalf]
  have cos1 : 0 ≤ Real.cos (Complex.arg (1 - M0) + Complex.arg w) := by
    rcases hwarg with hwarg | hwarg
    · rw [hwarg]
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · linarith [harg1, hφlo', hkhalf, Real.pi_pos]
      · linarith [hφ2]
    · rw [hwarg]
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · linarith [harg1, hφlo', hkpos]
      · linarith [hφ2, hkhalf]
  rw [hreM, hre1]
  exact ⟨mul_nonneg (mul_nonneg hnormM hnormw) cosM,
    mul_nonneg (mul_nonneg hnorm1 hnormw) cos1⟩

/-! ## Relating the root-labelled data to the time-labelled HB orbit -/

private lemma Mhat_re_formula (γ β : ℝ) (K m : ℕ) :
    (Mhat γ β K m).re =
      ((1 + β) * (1 - Real.cos (m * θ K))) / γ := by
  rw [Mhat, ω_pow_inv_eq, ω_pow_eq]
  simp only [Complex.div_ofReal_re, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re]
  ring

private lemma Mhat_im_formula (γ β : ℝ) (K m : ℕ) :
    (Mhat γ β K m).im =
      -((1 - β) * Real.sin (m * θ K)) / γ := by
  rw [Mhat, ω_pow_inv_eq, ω_pow_eq]
  simp only [Complex.div_ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im]
  ring

private lemma y1_eq_paperY {μ L γ β : ℝ} (K m t : ℕ) :
    y1 μ L γ β K m t =
      paperY K (φstar μ L γ β K m) (m * t) := by
  rw [y1, paperY, paperAngle]
  push_cast; ring

private lemma g1_eq_paperG {μ L γ β : ℝ} {K m t : ℕ}
    (hK : 3 ≤ K) (hγ : γ ≠ 0) :
    g1 μ L γ β K m t =
      paperG γ β K m (φstar μ L γ β K m) (m * t) := by
  let φ := φstar μ L γ β K m
  let x := (m : ℝ) * (t : ℝ) * θ K + φ
  let c := (m : ℝ) * θ K
  have hnext :
      (m : ℝ) * ((t + 1 : ℕ) : ℝ) * θ K + φ = x + c := by
    dsimp [x, c]
    push_cast
    ring
  have hprevAngle :
      (m : ℝ) * ((t + K - 1 : ℕ) : ℝ) * θ K + φ =
        x - c + (m : ℕ) * (2 * π) := by
    dsimp [x, c]
    push_cast [Nat.cast_sub (by omega : 1 ≤ t + K)]
    unfold θ
    have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    (field_simp [hKr.ne']; ring)
  have hprev :
      Real.cos ((m : ℝ) * ((t + K - 1 : ℕ) : ℝ) * θ K + φ) =
        Real.cos (x - c) := by
    rw [hprevAngle, Real.cos_add_nat_mul_two_pi]
  have hyt : y1 μ L γ β K m t = 2 * Real.cos x := by
    rw [y1]
  have hy1 : y1 μ L γ β K m (t + 1) = 2 * Real.cos (x + c) := by
    rw [y1]
    rw [show (m : ℝ) * ((t + 1 : ℕ) : ℝ) * θ K + φstar μ L γ β K m = x + c by
      simpa [φ] using hnext]
  have hyp : y1 μ L γ β K m (t + K - 1) = 2 * Real.cos (x - c) := by
    rw [y1]
    rw [show (m : ℝ) * ((t + K - 1 : ℕ) : ℝ) * θ K + φstar μ L γ β K m =
        (m : ℝ) * ((t + K - 1 : ℕ) : ℝ) * θ K + φ by rfl]
    exact congrArg (fun z : ℝ => 2 * z) hprev
  have hangle : paperAngle K φ (m * t) = x := by
    unfold paperAngle
    dsimp [x]
    push_cast
    ring
  rw [g1, hyt, hy1, hyp, paperG, hangle,
    Mhat_re_formula, Mhat_im_formula]
  have hc : (m : ℝ) * θ K = c := rfl
  rw [hc]
  rw [Real.cos_add x c, Real.cos_sub x c]
  (field_simp [hγ]; ring)

private lemma paperY_periodic {K : ℕ} (hK : 0 < K) (φ : ℝ) :
    ∀ l, paperY K φ (l + K) = paperY K φ l := by
  intro l
  rw [paperY, paperY, paperAngle, paperAngle]
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hang :
      ((l + K : ℕ) : ℝ) * θ K + φ =
        (l : ℝ) * θ K + φ + 2 * π := by
    push_cast
    unfold θ
    field_simp [hKr.ne']
    ring
  rw [hang, Real.cos_add_two_pi]

private lemma paperG_periodic {γ β : ℝ} {K m : ℕ} (hK : 0 < K) (φ : ℝ) :
    ∀ l, paperG γ β K m φ (l + K) = paperG γ β K m φ l := by
  intro l
  rw [paperG, paperG, paperAngle, paperAngle]
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hang :
      ((l + K : ℕ) : ℝ) * θ K + φ =
        (l : ℝ) * θ K + φ + 2 * π := by
    push_cast
    unfold θ
    field_simp [hKr.ne']
    ring
  rw [hang, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-! ## Theorem 4.1 -/

theorem theorem_4_1 {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L)
    {K m : ℕ} (hK : 3 ≤ K) (hm : m ∈ U K) {γ β : ℝ}
    (hp : (γ, β) ∈ ΩRoU μ L K m) :
    ∃ f ∈ F μ L ℝ,
      (∀ t, gradient f (y1 μ L γ β K (mstar K m) t) =
        g1 μ L γ β K (mstar K m) t) ∧
      Cycles L γ β f K (y1 μ L γ β K (mstar K m)) := by
  obtain ⟨hm', h2m'⟩ := mstar_mem hK hm
  have hp' : (γ, β) ∈ ΩRoU μ L K (mstar K m) := by
    rwa [ΩRoU_mstar hμ hμL hK hm]
  generalize mstar K m = m' at hm' h2m' hp' ⊢
  have hΩ : (γ, β) ∈ Ωcv L := by
    rw [lemma_3_1 hμ hμL hK hm'] at hp'
    exact hp'.1
  have hγ : γ ≠ 0 := hΩ.2.1.ne'
  obtain ⟨-, hiff⟩ := lemma_3_1_ii hμ hμL hK hm' h2m' hΩ
  obtain ⟨-, ⟨hMre,hMim⟩, ⟨h1re,h1im⟩, -⟩ := hiff.1 hp'
  set Mc := M μ L γ β K m'
  have hargM : Complex.arg Mc < 0 := Complex.arg_neg_iff.2 hMim
  have hargM' : -(π / 2) < Complex.arg Mc :=
    Complex.neg_pi_div_two_lt_arg_iff.2 (Or.inl hMre)
  have harg1 : 0 < Complex.arg (1-Mc) := by
    rcases (Complex.arg_nonneg_iff.2 h1im.le).lt_or_eq with h | h
    · exact h
    · have hz := (Complex.arg_eq_zero_iff.1 h.symm).2
      linarith
  have harg1' : Complex.arg (1-Mc) < π/2 :=
    Complex.arg_lt_pi_div_two_iff.2 (Or.inl h1re)
  set φ := φstar μ L γ β K m'
  have hphase0 := paper_phase_interval hμ hμL hK hm' hp'
  have hphase :
      -Complex.arg (M μ L γ β K m') - π / K ≤ φstar μ L γ β K m' ∧
      φstar μ L γ β K m' ≤ -Complex.arg (1 - M μ L γ β K m') ∧
      -π / K < φstar μ L γ β K m' ∧ φstar μ L γ β K m' < 0 := by
    simpa [mstar, h2m'] using hphase0
  have hφ1 : -Complex.arg Mc - π / K ≤ φ := by simpa [Mc, φ] using hphase.1
  have hφ2 : φ ≤ -Complex.arg (1 - Mc) := by simpa [Mc, φ] using hphase.2.1
  have hφlo : -π / K < φ := by simpa [φ] using hphase.2.2.1
  have hφhi : φ < 0 := by simpa [φ] using hphase.2.2.2

  let ys : Fin K → ℝ := fun i => paperY K φ (paperOrder K i)
  let gs : Fin K → ℝ := fun i => paperG γ β K m' φ (paperOrder K i)

  have hmono : StrictMono ys := by
    intro i j hij
    have h := paperOrder_strictMono hK hφlo hφhi hij
    have h2 := mul_lt_mul_of_pos_left h (show (0 : ℝ) < 2 by norm_num)
    simpa [ys, paperY, paperRootValue, paperAngle] using h2
  have hyinj : Function.Injective ys := hmono.injective

  let pord : Fin K → Fin K := fun i => ⟨paperOrder K i, paperOrder_lt hK⟩
  have hpord_bij : Function.Bijective pord := by
    simpa [pord] using (paperOrder_bijective hK hφlo hφhi)

  have hadj : ∀ n : ℕ, n + 1 < K →
      μ ≤ (paperG γ β K m' φ (paperOrder K (n + 1)) -
            paperG γ β K m' φ (paperOrder K n)) /
          (paperY K φ (paperOrder K (n + 1)) -
            paperY K φ (paperOrder K n)) ∧
      (paperG γ β K m' φ (paperOrder K (n + 1)) -
            paperG γ β K m' φ (paperOrder K n)) /
          (paperY K φ (paperOrder K (n + 1)) -
            paperY K φ (paperOrder K n)) ≤ L := by
    intro n hn
    let a := paperOrder K n
    let b := paperOrder K (n + 1)
    have hwarg : Complex.arg (paperW K φ a b) = π / 2 + φ ∨
        Complex.arg (paperW K φ a b) = -π / 2 + π / K + φ := by
      simpa [a, b] using paper_eq14 hK hn hφlo hφhi
    have hre := eq14_gives_realpart (M0 := Mc) (w := paperW K φ a b) hK
      hargM' hargM harg1 harg1' hφ1 hφ2 hφlo hφhi hwarg
    have hwre : 0 < (paperW K φ a b).re := by
      change 0 < Real.cos (paperAngle K φ b) - Real.cos (paperAngle K φ a)
      have hs := paperOrder_step_cos hK hn hφlo hφhi
      simpa [paperRootValue, paperAngle, a, b] using (sub_pos.mpr hs)
    have hslope := (paper_slope_iff hμL hγ (K := K) (m := m')
      (w := paperW K φ a b) hwre).2 hre
    have hd := paperW_differences (γ := γ) (β := β) (K := K) (m := m')
      (a := a) (b := b) (φ := φ)
    rw [← hd.1, ← hd.2] at hslope
    simpa [a, b] using hslope

  have hconsecutive : ∀ i j : Fin K, ys i < ys j →
      (∀ k, ¬ (ys i < ys k ∧ ys k < ys j)) →
      μ ≤ (gs j - gs i) / (ys j - ys i) ∧
      (gs j - gs i) / (ys j - ys i) ≤ L := by
    intro i j hij hnone
    have hijidx : (i : ℕ) < (j : ℕ) := by
      by_contra hnot
      have hji : (j : ℕ) ≤ (i : ℕ) := le_of_not_gt hnot
      by_cases heq : (i : ℕ) = (j : ℕ)
      · have hijFin : i = j := Fin.ext heq
        subst j
        exact (lt_irrefl _ hij)
      · have hlt : (j : ℕ) < (i : ℕ) := lt_of_le_of_ne hji (Ne.symm heq)
        have hltFin : j < i := by exact hlt
        have hback := hmono hltFin
        linarith
    have hiK : (i : ℕ) < K := i.isLt
    have hjK : (j : ℕ) < K := j.isLt
    have hsucc : (j : ℕ) = (i : ℕ) + 1 := by
      by_contra hne
      have hgap : (i : ℕ) + 1 < (j : ℕ) := by omega
      have hkK : (i : ℕ) + 1 < K := lt_trans hgap hjK
      let k : Fin K := ⟨(i : ℕ) + 1, hkK⟩
      have hik : i < k := by
        change (i : ℕ) < (i : ℕ) + 1
        omega
      have hkj : k < j := by
        change (i : ℕ) + 1 < (j : ℕ)
        exact hgap
      exact hnone k ⟨hmono hik, hmono hkj⟩
    have hi1K : (i : ℕ) + 1 < K := by
      rw [← hsucc]
      exact hjK
    let j' : Fin K := ⟨(i : ℕ) + 1, hi1K⟩
    have hj : j = j' := by
      apply Fin.ext
      exact hsucc
    rw [hj]
    dsimp [ys, gs, j']
    exact hadj (i : ℕ) hi1K

  obtain ⟨f, hf, hfgs⟩ := (theorem_2_2_1d hμ hμL ys gs hyinj).2 hconsecutive

  have hYper : ∀ l, paperY K φ (l + K) = paperY K φ l :=
    paperY_periodic (by omega) φ
  have hGper : ∀ l, paperG γ β K m' φ (l + K) = paperG γ β K m' φ l :=
    paperG_periodic (by omega) φ

  have hrootgrad : ∀ l < K,
      gradient f (paperY K φ l) = paperG γ β K m' φ l := by
    intro l hl
    obtain ⟨i, hi⟩ := hpord_bij.2 ⟨l, hl⟩
    have hv : paperOrder K i = l := congrArg Fin.val hi
    have h := hfgs i
    dsimp [ys, gs] at h
    rwa [hv] at h

  have hgrad : ∀ t,
      gradient f (y1 μ L γ β K m' t) = g1 μ L γ β K m' t := by
    intro t
    let l := m' * t % K
    have hl : l < K := Nat.mod_lt _ (by omega)
    have hyraw : y1 μ L γ β K m' t = paperY K φ (m' * t) := by
      simpa [φ] using
        (y1_eq_paperY (μ := μ) (L := L) (γ := γ) (β := β) K m' t)
    have hgraw : g1 μ L γ β K m' t = paperG γ β K m' φ (m' * t) := by
      simpa [φ] using
        (g1_eq_paperG (μ := μ) (L := L) (γ := γ) (β := β)
          (K := K) (m := m') (t := t) hK hγ)
    have hyMod : paperY K φ (m' * t) = paperY K φ l := by
      have h := periodic_mod hYper (m' * t)
      simpa [l] using h.symm
    have hgMod : paperG γ β K m' φ (m' * t) = paperG γ β K m' φ l := by
      have h := periodic_mod hGper (m' * t)
      simpa [l] using h.symm
    rw [hyraw, hgraw, hyMod, hgMod]
    exact hrootgrad l hl

  have hYinj : ∀ a < K, ∀ b < K,
      paperY K φ a = paperY K φ b → a = b := by
    intro a ha b hb hab
    obtain ⟨ia, hia⟩ := hpord_bij.2 ⟨a, ha⟩
    obtain ⟨ib, hib⟩ := hpord_bij.2 ⟨b, hb⟩
    have hva : paperOrder K ia = a := congrArg Fin.val hia
    have hvb : paperOrder K ib = b := congrArg Fin.val hib
    have hyab : ys ia = ys ib := by
      dsimp [ys]
      rw [hva, hvb, hab]
    have hij := hyinj hyab
    rw [← hva, ← hvb, hij]

  have hdist : ∀ a < K, ∀ b < K, a ≠ b →
      y1 μ L γ β K m' a ≠ y1 μ L γ β K m' b := by
    intro a ha b hb hab heq
    let la := m' * a % K
    let lb := m' * b % K
    have hla : la < K := Nat.mod_lt _ (by omega)
    have hlb : lb < K := Nat.mod_lt _ (by omega)
    have hYa : y1 μ L γ β K m' a = paperY K φ (m' * a) := by
      simpa [φ] using
        (y1_eq_paperY (μ := μ) (L := L) (γ := γ) (β := β) K m' a)
    have hYb : y1 μ L γ β K m' b = paperY K φ (m' * b) := by
      simpa [φ] using
        (y1_eq_paperY (μ := μ) (L := L) (γ := γ) (β := β) K m' b)
    have hYma : paperY K φ (m' * a) = paperY K φ la := by
      have h := periodic_mod hYper (m' * a)
      simpa [la] using h.symm
    have hYmb : paperY K φ (m' * b) = paperY K φ lb := by
      have h := periodic_mod hYper (m' * b)
      simpa [lb] using h.symm
    have hlabel : la = lb := by
      apply hYinj la hla lb hlb
      rw [← hYma, ← hYmb]
      rw [← hYa, ← hYb, heq]
    have hpow : ω K ^ (m' * a) = ω K ^ (m' * b) := by
      rw [ω_pow_mod (by omega : K ≠ 0) (m' * a),
        ω_pow_mod (by omega : K ≠ 0) (m' * b)]
      simpa [la, lb] using congrArg (fun q : ℕ => ω K ^ q) hlabel
    exact hab (ω_pow_inj (by omega : K ≠ 0) hm'.2.2 ha hb hpow)

  have hper : ∀ t,
      y1 μ L γ β K m' (t + K) = y1 μ L γ β K m' t := by
    intro t
    rw [y1, y1]
    have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have hang :
        (m' : ℝ) * ((t + K : ℕ) : ℝ) * θ K + φstar μ L γ β K m' =
          (m' : ℝ) * (t : ℝ) * θ K + φstar μ L γ β K m' +
            (m' : ℕ) * (2 * π) := by
      push_cast
      unfold θ
      field_simp [hKr.ne']
      ring
    rw [hang, Real.cos_add_nat_mul_two_pi]

  refine ⟨f, hf, hgrad, cycles_of_grad (by omega) hΩ hper
    (fun a ha b hb h => by
      by_contra hne
      exact hdist a ha b hb hne h) ?_⟩
  intro t
  rw [hgrad, g1]
  have hprev : y1 μ L γ β K m' (t + 1 + K - 1) =
      y1 μ L γ β K m' t := by
    have ht : t + 1 + K - 1 = t + K := by omega
    rw [ht, hper]
  rw [hprev]
  simp only [smul_eq_mul]
  field_simp [hγ]

/-! ## Corollary 4.2 -/

theorem theorem_4_1' {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L)
    {K m : ℕ} (hK : 3 ≤ K) (hm : m ∈ U K) :
    ΩRoU μ L K m ⊆ ΩKcycle μ L ℝ K := by
  rintro ⟨γ, β⟩ hp
  obtain ⟨f, hf, -, hc⟩ := theorem_4_1 hμ hμL hK hm hp
  exact ⟨f, hf, _, hc⟩

theorem corollary_4_2 {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L) :
    Ωaug μ L ⊆ Ωcycle μ L ℝ := by
  intro x hx
  simp only [Ωaug, Set.mem_iUnion] at hx
  obtain ⟨K, hK, m, hm, hx⟩ := hx
  simp only [Ωcycle, Set.mem_iUnion]
  exact ⟨K, hK, theorem_4_1' hμ hμL hK hm hx⟩

lemma ΩRoUcycle_subset_Ωaug (μ L : ℝ) : ΩRoUcycle μ L ⊆ Ωaug μ L := by
  intro x hx
  simp only [ΩRoUcycle, Ωaug, Set.mem_iUnion] at hx ⊢
  obtain ⟨K, hK, hx⟩ := hx
  exact ⟨K, hK, 1, ⟨le_rfl, by omega, Nat.coprime_one_left K⟩, hx⟩

theorem corollary_4_2_nonacceleration (C : ℝ)
    (ρ : ℝ → ℝ → ℝ × ℝ → ℝ)
    (h36 : ∀ μ L : ℝ, 0 < μ → μ < L → ∀ x : ℝ × ℝ,
      ρ μ L x ≤ (1 - C * (μ / L)) / (1 + C * (μ / L)) → x ∈ ΩRoUcycle μ L)
    {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L) (x : ℝ × ℝ)
    (hρ : ρ μ L x ≤ (1 - C * (μ / L)) / (1 + C * (μ / L))) :
    ∃ K ≥ 3, ∃ f ∈ F μ L ℝ, ∃ z : ℕ → ℝ, Cycles L x.1 x.2 f K z := by
  have := corollary_4_2 hμ hμL
    (ΩRoUcycle_subset_Ωaug μ L (h36 μ L hμ hμL x hρ))
  simp only [Ωcycle, Set.mem_iUnion] at this
  obtain ⟨K, hK, f, hf, z, hz⟩ := this
  exact ⟨K, hK, f, hf, z, hz⟩

/-! ## Summary -/

theorem sections_3_4 {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L) :
    (∀ K ≥ 3, ∀ m ∈ U K, ΩRoU μ L K m =
      {x | x ∈ Ωcv L ∧ ∀ Δ, 1 ≤ Δ → Δ < K → ϕ μ L x.1 x.2 K m Δ ≤ 0}) ∧
    (∀ K ≥ 3, ΩRoU μ L K 1 =
      {x | x ∈ Ωcv L ∧ hGTD (μ / L) x.2 (μ * x.1) (Real.cos (θ K)) ≤ 0}) ∧
    (interior (Ωaug (exμ L) L) \ ΩRoUcycle (exμ L) L).Nonempty ∧
    Ωaug μ L ⊆ Ωcycle μ L ℝ :=
  ⟨fun _ hK _ hm => lemma_3_1 hμ hμL hK hm,
    fun _ hK => theorem_2_3 hμ hμL hK,
    (example_3_2 (hμ.trans hμL)).2.2.2.2.2.2.2,
    corollary_4_2 hμ hμL⟩

end HeavyBall

#print axioms HeavyBall.paper_phase_interval
#print axioms HeavyBall.paperOrder_strictMono
#print axioms HeavyBall.paper_eq14
#print axioms HeavyBall.theorem_4_1
#print axioms HeavyBall.theorem_4_1'
#print axioms HeavyBall.corollary_4_2
#print axioms HeavyBall.corollary_4_2_nonacceleration
#print axioms HeavyBall.sections_3_4

/-
Supplementary material for "Non-acceleration of the heavy-ball method in 1D".
Part 4 of 4, Appendix B: Compact certificate for the Section-5 counterexample and Appendix B.

The proof deliberately reuses the Section-3 residual lemmas.  The large-K
part is the Appendix-B proof, but squared where convenient: this avoids
introducing `sqrt(sinMinSq)` and turns the numerical part into rational
arithmetic.
-/

noncomputable section

open Real Filter Topology Set Asymptotics
open scoped RealInnerProductSpace ComplexConjugate

namespace HeavyBall
namespace Counterexample

/-! ## P₁ and its residual -/

def κP : ℝ := 531 / 10 ^ 4
def βP : ℝ := 4879 / 10 ^ 4
def γP : ℝ := 32829 / 12500

def aP : ℝ := (1 + βP - κP * γP) / ((1 - κP) * γP)
def bP : ℝ := (1 + βP) / ((1 - κP) * γP)
def cP : ℝ := (1 - βP) / ((1 - κP) * γP)

def gP (u : ℝ) : ℝ :=
  (aP - bP * u) * (1 - aP + bP * u) - cP ^ 2 * (1 - u ^ 2)

def ang (K n : ℕ) : ℝ := 2 * π * (n : ℝ) / (K : ℝ)
def φP (K m Δ : ℕ) : ℝ := ϕ κP 1 γP βP K m Δ

lemma κP_lt_one : κP < 1 := by norm_num [κP]
lemma P_in_Ωcv : (γP, βP) ∈ Ωcv 1 := by norm_num [Ωcv, γP, βP, abs_lt]
lemma aP_eq : aP = 168555301 / 310857801 := by norm_num [aP, κP, βP, γP]
lemma bP_eq : bP = 185987500 / 310857801 := by norm_num [bP, κP, βP, γP]
lemma cP_eq : cP = 64012500 / 310857801 := by norm_num [cP, κP, βP, γP]
lemma cP_pos : 0 < cP := by rw [cP_eq]; norm_num

lemma theta_mul_eq_ang (K n : ℕ) : (n : ℝ) * θ K = ang K n := by
  unfold θ ang
  ring

lemma pmP_eq (K m : ℕ) :
    pm κP 1 γP βP K m = aP - bP * cos (ang K m) := by
  rw [pm, aP, bP, theta_mul_eq_ang]
  ring

lemma qmP_eq (K m : ℕ) :
    qm κP 1 γP βP K m = cP * sin (ang K m) := by
  rw [qm, cP, theta_mul_eq_ang]
  ring

lemma AmP_eq (K m : ℕ) :
    Am κP 1 γP βP K m = gP (cos (ang K m)) := by
  rw [Am, pmP_eq, qmP_eq, gP]
  have ht := sin_sq_add_cos_sq (ang K m)
  nlinarith

lemma φP_eq (K m Δ : ℕ) :
    φP K m Δ =
      gP (cos (ang K m)) * (cos (ang K (m * Δ)) - 1) +
        cP * sin (ang K m) * sin (ang K (m * Δ)) := by
  rw [φP, ϕ_eq, AmP_eq, qmP_eq, theta_mul_eq_ang K (m * Δ)]

/-! ## Exact mixed condition for K=10 -/

lemma ang_mod (n K : ℕ) (hK : 0 < K) :
    ang K n = ang K (n % K) + ((n / K : ℕ) : ℝ) * (2 * π) := by
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hnR : (n : ℝ) = (n % K : ℕ) + (K : ℝ) * ((n / K : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div n K).symm
  unfold ang
  rw [hnR]
  field_simp [hK0]

lemma cos_ang_mod (n K : ℕ) (hK : 0 < K) :
    cos (ang K n) = cos (ang K (n % K)) := by
  rw [ang_mod n K hK, cos_add_nat_mul_two_pi]

/-- `w = cos(2π/5)`. -/
def w : ℝ := (√5 - 1) / 4

lemma w_sq : w ^ 2 = (1 - 2 * w) / 4 := by
  rw [w]
  linear_combination (1 / 16) * sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)

lemma w_bounds : 3 / 10 < w ∧ w < 31 / 100 := by
  have h1 : (22 / 10 : ℝ) < √5 := (lt_sqrt (by norm_num)).2 (by norm_num)
  have h2 : √5 < (224 / 100 : ℝ) := (sqrt_lt' (by norm_num)).2 (by norm_num)
  constructor <;> rw [w] <;> linarith

def cosTab10 : ℕ → ℝ
  | 0 => 1
  | 1 => w + 1 / 2
  | 2 => w
  | 3 => -w
  | 4 => -w - 1 / 2
  | 5 => -1
  | 6 => -w - 1 / 2
  | 7 => -w
  | 8 => w
  | 9 => w + 1 / 2
  | _ => 0

lemma cos_tenth (n : ℕ) : cos (ang 10 n) = cosTab10 (n % 10) := by
  rw [cos_ang_mod n 10 (by norm_num)]
  let r := n % 10
  change cos (ang 10 r) = cosTab10 r
  have hr : r < 10 := by
    dsimp [r]
    exact Nat.mod_lt _ (by norm_num)
  have h1 : cos (π / 5) = w + 1 / 2 := by
    rw [cos_pi_div_five, w]
    ring
  have h2 : cos (2 * (π / 5)) = w := by
    rw [cos_two_mul, h1]
    linear_combination 2 * w_sq
  interval_cases r <;> simp only [cosTab10]
  · simp [ang]
  · rw [show ang 10 1 = π / 5 by unfold ang; norm_num; ring, h1]
  · rw [show ang 10 2 = 2 * (π / 5) by unfold ang; norm_num; ring, h2]
  · rw [show ang 10 3 = π - 2 * (π / 5) by unfold ang; norm_num; ring,
      cos_pi_sub, h2]
  · rw [show ang 10 4 = π - π / 5 by unfold ang; norm_num; ring,
      cos_pi_sub, h1]; ring
  · rw [show ang 10 5 = π by unfold ang; norm_num; ring, cos_pi]
  · rw [show ang 10 6 = π / 5 + π by unfold ang; norm_num; ring,
      cos_add_pi, h1]; ring
  · rw [show ang 10 7 = 2 * (π / 5) + π by unfold ang; norm_num; ring,
      cos_add_pi, h2]
  · rw [show ang 10 8 = 2 * π - 2 * (π / 5) by unfold ang; norm_num; ring,
      cos_two_pi_sub, h2]
  · rw [show ang 10 9 = 2 * π - π / 5 by unfold ang; norm_num; ring,
      cos_two_pi_sub, h1]

lemma sin_mul_sin_rev (x y : ℝ) :
    sin x * sin y = (cos (y - x) - cos (y + x)) / 2 := by
  rw [cos_sub, cos_add]
  ring

lemma φP_tenth (j Δ : ℕ) (hΔ : 1 ≤ Δ) :
    φP 10 j Δ =
      gP (cosTab10 (j % 10)) * (cosTab10 (j * Δ % 10) - 1) +
        cP / 2 *
          (cosTab10 (j * (Δ - 1) % 10) - cosTab10 (j * (Δ + 1) % 10)) := by
  rw [φP_eq]
  have eminus : ang 10 (j * Δ) - ang 10 j = ang 10 (j * (Δ - 1)) := by
    unfold ang
    push_cast [Nat.cast_sub hΔ]
    ring
  have eplus : ang 10 (j * Δ) + ang 10 j = ang 10 (j * (Δ + 1)) := by
    unfold ang
    push_cast
    ring
  have hprod :
      cP * sin (ang 10 j) * sin (ang 10 (j * Δ)) =
        cP / 2 *
          (cos (ang 10 (j * (Δ - 1))) - cos (ang 10 (j * (Δ + 1)))) := by
    calc
      cP * sin (ang 10 j) * sin (ang 10 (j * Δ)) =
          cP * (sin (ang 10 j) * sin (ang 10 (j * Δ))) := by ring
      _ = cP *
          ((cos (ang 10 (j * Δ) - ang 10 j) -
            cos (ang 10 (j * Δ) + ang 10 j)) / 2) := by
            rw [sin_mul_sin_rev]
      _ = cP / 2 *
          (cos (ang 10 (j * (Δ - 1))) - cos (ang 10 (j * (Δ + 1)))) := by
            rw [eminus, eplus]
            ring
  rw [hprod]
  rw [cos_tenth j, cos_tenth (j * Δ), cos_tenth (j * (Δ - 1)),
    cos_tenth (j * (Δ + 1))]

/-- Equation (24): all nine mixed inequalities are strict. -/
theorem mixed_condition (Δ : ℕ) (h1 : 1 ≤ Δ) (h9 : Δ ≤ 9) :
    137 / 500 * φP 10 2 Δ + 363 / 500 * φP 10 3 Δ < 0 := by
  have hw2 := w_sq
  have hw3 : w ^ 3 = (4 * w - 1) / 8 := by
    linear_combination (w - 1 / 2) * w_sq
  obtain ⟨hw0, hw1⟩ := w_bounds
  rw [φP_tenth 2 Δ h1, φP_tenth 3 Δ h1]
  interval_cases Δ <;>
    norm_num [cosTab10, gP, aP_eq, bP_eq, cP_eq] <;>
    linarith

/-! ## Reflection and the binding necessary condition -/

lemma φP_mstar {K m : ℕ} (hK : 3 ≤ K) (hm : m ∈ U K) (Δ : ℕ) :
    φP K (mstar K m) Δ = φP K m Δ := by
  unfold φP mstar
  split_ifs with h
  · rfl
  · exact ϕ_reflect κP 1 γP βP (by omega) hm.2.1.le Δ

lemma binding_necessary {K m : ℕ} (hK : 3 ≤ K) (hm : m ∈ U K)
    (hfeas : ∀ Δ, 1 ≤ Δ → Δ < K → φP K m Δ ≤ 0) :
    let mr := mstar K m
    qm κP 1 γP βP K mr * cos (π / K) ≤
      Am κP 1 γP βP K mr * sin (π / K) := by
  dsimp
  obtain ⟨hmr, hhalf⟩ := mstar_mem hK hm
  have hfeas' : ∀ Δ, 1 ≤ Δ → Δ < K →
      ϕ κP 1 γP βP K (mstar K m) Δ ≤ 0 := by
    intro Δ hΔ1 hΔK
    change φP K (mstar K m) Δ ≤ 0
    rw [φP_mstar hK hm Δ]
    exact hfeas Δ hΔ1 hΔK
  exact (residual_system_iff κP_lt_one hK hmr hhalf P_in_Ωcv).1 hfeas'

lemma A_pos_and_cot_necessary {K m : ℕ} (hK : 3 ≤ K) (hm : m ∈ U K)
    (hfeas : ∀ Δ, 1 ≤ Δ → Δ < K → φP K m Δ ≤ 0) :
    let mr := mstar K m
    0 < Am κP 1 γP βP K mr ∧
      cos (π / K) / sin (π / K) ≤
        Am κP 1 γP βP K mr / qm κP 1 γP βP K mr := by
  dsimp
  obtain ⟨hmr, hhalf⟩ := mstar_mem hK hm
  have hb := binding_necessary hK hm hfeas
  have hb' :
      cos (π / K) * qm κP 1 γP βP K (mstar K m) ≤
        Am κP 1 γP βP K (mstar K m) * sin (π / K) := by
    simpa [mul_comm] using hb
  have hq : 0 < qm κP 1 γP βP K (mstar K m) :=
    qm_pos κP_lt_one hmr.1 hhalf P_in_Ωcv
  obtain ⟨hx0, hxhalf⟩ := pi_div_bounds hK
  have hs : 0 < sin (π / K) := sin_pos_of_pos_of_lt_pi hx0 (by linarith [pi_pos])
  have hc : 0 < cos (π / K) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hxhalf⟩
  have hright : 0 < Am κP 1 γP βP K (mstar K m) * sin (π / K) :=
    lt_of_lt_of_le (mul_pos hc hq) hb'
  have hA : 0 < Am κP 1 γP βP K (mstar K m) := by
    rcases (mul_pos_iff.mp hright) with h | h
    · exact h.1
    · exfalso; linarith [hs, h.2]
  exact ⟨hA, (div_le_div_iff₀ hs hq).2 hb'⟩

/-! ## Appendix B: the large-K upper bound -/

def uLo : ℝ := -56921 / 74395
def uHi : ℝ := 168555301 / 185987500
def sinMinSq : ℝ := 6180460661049399 / 34591350156250000

/-- We use the square of the bound in (28), avoiding an unnecessary square root in Lean. -/
def rMaxSq : ℝ := 217216154001052573943 / 26331249736617936912

lemma sinMinSq_identity : sinMinSq = 1 - uHi ^ 2 := by
  norm_num [sinMinSq, uHi]

lemma rMaxSq_identity : rMaxSq * (cP ^ 2 * sinMinSq) = 1 / 16 := by
  norm_num [rMaxSq, cP_eq, sinMinSq]

lemma u_interval_of_p_interval {u : ℝ}
    (hp : 0 ≤ aP - bP * u ∧ aP - bP * u ≤ 1) :
    uLo ≤ u ∧ u ≤ uHi := by
  rw [aP_eq, bP_eq] at hp
  constructor
  · rw [uLo]
    norm_num at hp ⊢
    linarith [hp.2]
  · rw [uHi]
    norm_num at hp ⊢
    linarith [hp.1]

lemma sinMinSq_le_sin_sq {x u : ℝ} (hu : u = cos x)
    (hub : uLo ≤ u ∧ u ≤ uHi) :
    sinMinSq ≤ sin x ^ 2 := by
  have hdom : -uHi ≤ uLo := by norm_num [uHi, uLo]
  have hlo : -uHi ≤ u := le_trans hdom hub.1
  have h1 : 0 ≤ uHi - u := sub_nonneg.mpr hub.2
  have h2 : 0 ≤ uHi + u := by linarith
  have hsq : u ^ 2 ≤ uHi ^ 2 := by
    have hp := mul_nonneg h1 h2
    nlinarith
  have ht := sin_sq_add_cos_sq x
  rw [← hu] at ht
  rw [sinMinSq_identity]
  nlinarith

lemma p_interval_of_A_pos {K m : ℕ}
    (hA : 0 < Am κP 1 γP βP K m) :
    0 ≤ pm κP 1 γP βP K m ∧ pm κP 1 γP βP K m ≤ 1 := by
  have hpProd :
      0 < pm κP 1 γP βP K m * (1 - pm κP 1 γP βP K m) := by
    unfold Am at hA
    nlinarith [sq_nonneg (qm κP 1 γP βP K m)]
  rcases (mul_pos_iff.mp hpProd) with h | h
  · exact ⟨h.1.le, by linarith [h.2]⟩
  · exfalso; linarith [h.1, h.2]

/-- Squared form of (28): `(A/q)^2 ≤ rMaxSq`. -/
lemma r_sq_upper_of_feasible {K m : ℕ} (hK : 10 ≤ K) (hm : m ∈ U K)
    (hfeas : ∀ Δ, 1 ≤ Δ → Δ < K → φP K m Δ ≤ 0) :
    let mr := mstar K m
    (Am κP 1 γP βP K mr / qm κP 1 γP βP K mr) ^ 2 ≤ rMaxSq := by
  dsimp
  obtain ⟨hmr, hhalf⟩ := mstar_mem (by omega) hm
  obtain ⟨hA, -⟩ := A_pos_and_cot_necessary (by omega) hm hfeas
  let mr := mstar K m
  let p := pm κP 1 γP βP K mr
  let q := qm κP 1 γP βP K mr
  let A := Am κP 1 γP βP K mr
  let u := cos (ang K mr)
  have hA' : 0 < A := by simpa [A, mr] using hA
  have hp : 0 ≤ p ∧ p ≤ 1 := by
    simpa [p, mr] using p_interval_of_A_pos (K := K) (m := mstar K m) hA
  have hpform : p = aP - bP * u := by
    simpa [p, u, mr] using pmP_eq K (mstar K m)
  have hub : uLo ≤ u ∧ u ≤ uHi := by
    apply u_interval_of_p_interval
    rwa [← hpform]
  have hspos : 0 < sin (ang K mr) := by
    apply sin_pos_of_pos_of_lt_pi
    · unfold ang
      have hmr0 : (0 : ℝ) < mr := by exact_mod_cast hmr.1
      positivity
    · unfold ang
      have hKr : (0 : ℝ) < K := by positivity
      rw [div_lt_iff₀ hKr]
      have hh : (2 * mr : ℝ) < K := by exact_mod_cast hhalf
      nlinarith [pi_pos]
  have hs2 : sinMinSq ≤ sin (ang K mr) ^ 2 :=
    sinMinSq_le_sin_sq rfl hub
  have hqform : q = cP * sin (ang K mr) := by
    simpa [q, mr] using qmP_eq K (mstar K m)
  have hq : 0 < q := by rw [hqform]; exact mul_pos cP_pos hspos
  have hq2min : cP ^ 2 * sinMinSq ≤ q ^ 2 := by
    rw [hqform]
    calc
      cP ^ 2 * sinMinSq ≤ cP ^ 2 * sin (ang K mr) ^ 2 :=
        mul_le_mul_of_nonneg_left hs2 (sq_nonneg cP)
      _ = (cP * sin (ang K mr)) ^ 2 := by ring
  have hAle : A ≤ 1 / 4 := by
    dsimp [A]
    unfold Am
    have hpq := sq_nonneg (pm κP 1 γP βP K (mstar K m) - 1 / 2)
    have hqq := sq_nonneg (qm κP 1 γP βP K (mstar K m))
    nlinarith
  have hA2 : A ^ 2 ≤ 1 / 16 := by nlinarith [hA'.le, hAle]
  have hR0 : 0 ≤ rMaxSq := by norm_num [rMaxSq]
  have hRq : 1 / 16 ≤ rMaxSq * q ^ 2 := by
    calc
      (1 / 16 : ℝ) = rMaxSq * (cP ^ 2 * sinMinSq) := rMaxSq_identity.symm
      _ ≤ rMaxSq * q ^ 2 := mul_le_mul_of_nonneg_left hq2min hR0
  have hAq : A ^ 2 ≤ rMaxSq * q ^ 2 := hA2.trans hRq
  have hq2 : 0 < q ^ 2 := pow_pos hq 2
  rw [div_pow]
  exact (div_le_iff₀ hq2).2 hAq

/-! ## Exact separation at K=10 and monotonicity of cot -/

lemma cot10_sq :
    (cos (π / 10) / sin (π / 10)) ^ 2 = 5 + 2 * √5 := by
  have hs5 : (√5 : ℝ) ^ 2 = 5 := sq_sqrt (by norm_num)
  have hc2 := cos_two_mul (π / 10)
  have hc : cos (π / 10) ^ 2 = (5 + √5) / 8 := by
    rw [show 2 * (π / 10) = π / 5 by ring, cos_pi_div_five] at hc2
    nlinarith
  have ht := sin_sq_add_cos_sq (π / 10)
  have hs : sin (π / 10) ^ 2 = (3 - √5) / 8 := by nlinarith
  have hne : (3 - √5 : ℝ) ≠ 0 := by
    have h : (√5 : ℝ) < 3 := (sqrt_lt' (by norm_num)).2 (by norm_num)
    linarith
  rw [div_pow, hc, hs]
  field_simp [hne]
  nlinarith

/-- Equation (29), in the squared form actually used by the certificate. -/
lemma exact_exclusion_number :
    (cos (π / 10) / sin (π / 10)) ^ 2 - rMaxSq =
      2 * √5 - 85559905317962889383 / 26331249736617936912 := by
  rw [cot10_sq]
  unfold rMaxSq
  ring_nf

lemma rMaxSq_lt_cot10_sq :
    rMaxSq < (cos (π / 10) / sin (π / 10)) ^ 2 := by
  rw [← sub_pos]
  rw [exact_exclusion_number]
  have hs : (2 : ℝ) < √5 := (lt_sqrt (by norm_num)).2 (by norm_num)
  have hr :
      (85559905317962889383 : ℝ) / 26331249736617936912 < 4 := by norm_num
  linarith

lemma cot10_le_cotK {K : ℕ} (hK : 10 ≤ K) :
    cos (π / 10) / sin (π / 10) ≤ cos (π / K) / sin (π / K) := by
  have hK3 : 3 ≤ K := by omega
  obtain ⟨ha0, haHalf⟩ := pi_div_bounds hK3
  obtain ⟨hb0, hbHalf⟩ := pi_div_bounds (show 3 ≤ 10 by norm_num)
  have hKr : (0 : ℝ) < K := by positivity
  have hab : π / (K : ℝ) ≤ π / 10 := by
    rw [div_le_div_iff₀ hKr (by norm_num : (0 : ℝ) < 10)]
    have hKr10 : (10 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith [pi_pos]
  have hsa : 0 < sin (π / K) := sin_pos_of_pos_of_lt_pi ha0 (by linarith [pi_pos])
  have hsb : 0 < sin (π / 10) := sin_pos_of_pos_of_lt_pi hb0 (by linarith [pi_pos])
  have hsd : 0 ≤ sin (π / 10 - π / K) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hbHalf, pi_pos])
  rw [sin_sub] at hsd
  exact (div_le_div_iff₀ hsb hsa).2 (by linarith)

/-- Appendix B, `K ≥ 10`. -/
theorem no_pure_mode_large {K m : ℕ} (hK : 10 ≤ K) (hm : m ∈ U K) :
    ¬ (∀ Δ, 1 ≤ Δ → Δ < K → φP K m Δ ≤ 0) := by
  intro hfeas
  obtain ⟨-, hcot⟩ := A_pos_and_cot_necessary (by omega) hm hfeas
  have hup := r_sq_upper_of_feasible hK hm hfeas
  have hmono := cot10_le_cotK hK
  obtain ⟨hx0, hxhalf⟩ := pi_div_bounds (by omega : 3 ≤ K)
  have hxpi : π / (K : ℝ) < π := lt_trans hxhalf (by linarith [pi_pos])
  have hsK : 0 < sin (π / K) := sin_pos_of_pos_of_lt_pi hx0 hxpi
  have hcK : 0 < cos (π / K) :=
    cos_pos_of_mem_Ioo ⟨by linarith [hx0, pi_pos], hxhalf⟩
  have hcot0 : 0 ≤ cos (π / K) / sin (π / K) := (div_pos hcK hsK).le
  have hr0 : 0 ≤ Am κP 1 γP βP K (mstar K m) / qm κP 1 γP βP K (mstar K m) :=
    le_trans hcot0 hcot
  have hsq1 :
      (cos (π / 10) / sin (π / 10)) ^ 2 ≤
        (cos (π / K) / sin (π / K)) ^ 2 := by
    obtain ⟨hx10, hx10half⟩ := pi_div_bounds (show 3 ≤ 10 by norm_num)
    have hx10pi : π / (10 : ℝ) < π := lt_trans hx10half (by linarith [pi_pos])
    have hs10 : 0 < sin (π / 10) := sin_pos_of_pos_of_lt_pi hx10 hx10pi
    have hc10 : 0 < cos (π / 10) :=
      cos_pos_of_mem_Ioo ⟨by linarith [hx10, pi_pos], hx10half⟩
    nlinarith [div_pos hc10 hs10]
  have hsq2 :
      (cos (π / K) / sin (π / K)) ^ 2 ≤
        (Am κP 1 γP βP K (mstar K m) / qm κP 1 γP βP K (mstar K m)) ^ 2 := by
    nlinarith
  exact (not_lt_of_ge (hsq1.trans (hsq2.trans hup))) rMaxSq_lt_cot10_sq


/-! ## Finite exact certificate for `3 ≤ K ≤ 9`

The paper treats these as a literal finite computation.  We therefore do not
use a uniform analytic inequality here.  Instead we evaluate the binding
residual in exact algebraic arithmetic for each of the thirteen canonical
primitive modes.

For `x = π/K`, if `m Δ ≡ 1 (mod K)`, then

  φ_{K,m}(Δ)
    = g(cos(2mx)) (cos(2x)-1) + c sin(2mx) sin(2x).

The four definitions below are exactly this expression after eliminating
`sin x` with `sin²x+cos²x=1`, for `m=1,2,3,4` respectively.
-/

lemma sin_ang_mod (n K : ℕ) (hK : 0 < K) :
    sin (ang K n) = sin (ang K (n % K)) := by
  rw [ang_mod n K hK, sin_add_nat_mul_two_pi]

lemma φP_binding {K m Δ : ℕ} (hK : 0 < K) (hmod : m * Δ % K = 1) :
    φP K m Δ =
      gP (cos (ang K m)) * (cos (ang K 1) - 1) +
        cP * sin (ang K m) * sin (ang K 1) := by
  rw [φP_eq, cos_ang_mod (m * Δ) K hK, sin_ang_mod (m * Δ) K hK, hmod]

private def F1 (z : ℝ) : ℝ :=
  2 * (1 - z^2) * (2 * cP * z^2 - gP (2*z^2 - 1))

private def F2 (z : ℝ) : ℝ :=
  2 * (1 - z^2) *
    (cP * z * (8*z^3 - 4*z) - gP (8*z^4 - 8*z^2 + 1))

private def F3 (z : ℝ) : ℝ :=
  2 * (1 - z^2) *
    (cP * z * (32*z^5 - 32*z^3 + 6*z) -
      gP (32*z^6 - 48*z^4 + 18*z^2 - 1))

private def F4 (z : ℝ) : ℝ :=
  2 * (1 - z^2) *
    (cP * z * (128*z^7 - 192*z^5 + 80*z^3 - 8*z) -
      gP (128*z^8 - 256*z^6 + 160*z^4 - 32*z^2 + 1))

private lemma cos_three_poly (x : ℝ) :
    cos (3*x) = 4*cos x^3 - 3*cos x := by
  rw [show 3*x = 2*x + x by ring, cos_add, cos_two_mul, sin_two_mul]
  have ht := sin_sq_add_cos_sq x
  linear_combination -2 * cos x * ht

private lemma sin_three_poly (x : ℝ) :
    sin (3*x) = sin x * (4*cos x^2 - 1) := by
  rw [show 3*x = 2*x + x by ring, sin_add, sin_two_mul, cos_two_mul]
  ring

private lemma cos_four_poly (x : ℝ) :
    cos (4*x) = 8*cos x^4 - 8*cos x^2 + 1 := by
  rw [show 4*x = 2*(2*x) by ring, cos_two_mul, cos_two_mul]
  ring

private lemma sin_four_poly (x : ℝ) :
    sin (4*x) = sin x * (8*cos x^3 - 4*cos x) := by
  rw [show 4*x = 2*(2*x) by ring, sin_two_mul, sin_two_mul, cos_two_mul]
  ring

private lemma cos_six_poly (x : ℝ) :
    cos (6*x) = 32*cos x^6 - 48*cos x^4 + 18*cos x^2 - 1 := by
  rw [show 6*x = 2*(3*x) by ring, cos_two_mul, cos_three_poly]
  ring

private lemma sin_six_poly (x : ℝ) :
    sin (6*x) = sin x * (32*cos x^5 - 32*cos x^3 + 6*cos x) := by
  rw [show 6*x = 2*(3*x) by ring, sin_two_mul, sin_three_poly, cos_three_poly]
  ring

private lemma cos_eight_poly (x : ℝ) :
    cos (8*x) = 128*cos x^8 - 256*cos x^6 + 160*cos x^4 - 32*cos x^2 + 1 := by
  rw [show 8*x = 2*(4*x) by ring, cos_two_mul, cos_four_poly]
  ring

private lemma sin_eight_poly (x : ℝ) :
    sin (8*x) = sin x *
      (128*cos x^7 - 192*cos x^5 + 80*cos x^3 - 8*cos x) := by
  rw [show 8*x = 2*(4*x) by ring, sin_two_mul, sin_four_poly, cos_four_poly]
  ring

private lemma binding_formula_m1 {K Δ : ℕ} (hK : 0 < K) (hmod : Δ % K = 1) :
    φP K 1 Δ = F1 (cos (π / K)) := by
  rw [φP_binding hK (by simpa using hmod)]
  set x : ℝ := π / K
  have ha1 : ang K 1 = 2*x := by unfold ang x; norm_num; ring
  rw [ha1, cos_two_mul, sin_two_mul]
  have ht := sin_sq_add_cos_sq x
  have hs2 : sin x ^ 2 = 1 - cos x ^ 2 := by nlinarith
  unfold F1
  ring_nf
  rw [hs2]
  ring

private lemma binding_formula_m2 {K Δ : ℕ} (hK : 0 < K) (hmod : 2 * Δ % K = 1) :
    φP K 2 Δ = F2 (cos (π / K)) := by
  rw [φP_binding hK hmod]
  set x : ℝ := π / K
  have ha1 : ang K 1 = 2*x := by unfold ang x; norm_num; ring
  have ha2 : ang K 2 = 4*x := by unfold ang x; norm_num; ring
  rw [ha1, ha2, cos_two_mul, sin_two_mul, cos_four_poly, sin_four_poly]
  have ht := sin_sq_add_cos_sq x
  have hs2 : sin x ^ 2 = 1 - cos x ^ 2 := by nlinarith
  unfold F2
  ring_nf
  rw [hs2]
  ring

private lemma binding_formula_m3 {K Δ : ℕ} (hK : 0 < K) (hmod : 3 * Δ % K = 1) :
    φP K 3 Δ = F3 (cos (π / K)) := by
  rw [φP_binding hK hmod]
  set x : ℝ := π / K
  have ha1 : ang K 1 = 2*x := by unfold ang x; norm_num; ring
  have ha3 : ang K 3 = 6*x := by unfold ang x; norm_num; ring
  rw [ha1, ha3, cos_two_mul, sin_two_mul, cos_six_poly, sin_six_poly]
  have ht := sin_sq_add_cos_sq x
  have hs2 : sin x ^ 2 = 1 - cos x ^ 2 := by nlinarith
  unfold F3
  ring_nf
  rw [hs2]
  ring

private lemma binding_formula_m4 {K Δ : ℕ} (hK : 0 < K) (hmod : 4 * Δ % K = 1) :
    φP K 4 Δ = F4 (cos (π / K)) := by
  rw [φP_binding hK hmod]
  set x : ℝ := π / K
  have ha1 : ang K 1 = 2*x := by unfold ang x; norm_num; ring
  have ha4 : ang K 4 = 8*x := by unfold ang x; norm_num; ring
  rw [ha1, ha4, cos_two_mul, sin_two_mul, cos_eight_poly, sin_eight_poly]
  have ht := sin_sq_add_cos_sq x
  have hs2 : sin x ^ 2 = 1 - cos x ^ 2 := by nlinarith
  unfold F4
  ring_nf
  rw [hs2]
  ring

/-! ### Exact values printed by the finite table

All thirteen values use one common denominator.  For K=7 and K=9 the exact
algebraic values are written in the power basis generated by `cos(π/K)`;
this avoids any floating-point arithmetic or a choice of radicals for the cubic
extensions.
-/

/-- Common denominator used in the exact finite residual table. -/
def tableDen : ℝ := 96632572442555601
def cK (K : ℕ) : ℝ := cos (π / K)

def table_v31 : ℝ := 188903762921250 / tableDen
def table_v41 : ℝ := 10544422210000 / tableDen
def table_v51 : ℝ :=
  2500 * (4672702289116 - 3192062472569 * cK 5) / tableDen
def table_v52 : ℝ :=
  1250 * (41834524701442 * cK 5 - 22723434239663) / tableDen
def table_v61 : ℝ := 7571014001236250 / tableDen
def table_v71 : ℝ :=
  1250 * (-24965749890276 * (cK 7)^2 + 12289813135790 * cK 7 + 15586842050801) / tableDen
def table_v72 : ℝ :=
  1250 * (47261175674464 * (cK 7)^2 - 10097217396580 * cK 7 - 22341228158279) / tableDen
def table_v73 : ℝ :=
  5000 * (6048375663221 * (cK 7)^2 + 3431608062500 * cK 7 - 5953878585096) / tableDen
def table_v81 : ℝ :=
  2500 * (-193061809348 * (cK 8)^2 + 3196280241453) / tableDen
def table_v83 : ℝ :=
  10000 * (1904811678058 * (cK 8)^2 - 665737787433) / tableDen
def table_v91 : ℝ :=
  7500 * (-4160958315046 * (cK 9)^2 + 1031843855965 * cK 9 + 3621958103116) / tableDen
def table_v92 : ℝ :=
  3750 * (11687891891488 * (cK 9)^2 - 3334968086930 * cK 9 - 5064112285523) / tableDen
def table_v94 : ℝ :=
  15000 * (3668223741907 * (cK 9)^2 + 317820093750 * cK 9 - 3064790038782) / tableDen

/-! Minimal algebraic relations for the cosines occurring in the table. -/

private lemma c3_poly : 2 * cK 3 - 1 = 0 := by
  change 2 * cos (π / 3) - 1 = 0
  rw [cos_pi_div_three]
  norm_num

private lemma c4_poly : 2 * (cK 4)^2 - 1 = 0 := by
  change 2 * cos (π / 4)^2 - 1 = 0
  rw [cos_pi_div_four]
  have h2 : (√2 : ℝ)^2 = 2 := sq_sqrt (by norm_num)
  nlinarith

private lemma c5_poly : 4 * (cK 5)^2 - 2 * cK 5 - 1 = 0 := by
  change 4 * cos (π / 5)^2 - 2 * cos (π / 5) - 1 = 0
  rw [cos_pi_div_five]
  have h5 : (√5 : ℝ)^2 = 5 := sq_sqrt (by norm_num)
  nlinarith

private lemma c6_poly : 4 * (cK 6)^2 - 3 = 0 := by
  change 4 * cos (π / 6)^2 - 3 = 0
  rw [cos_pi_div_six]
  have h3 : (√3 : ℝ)^2 = 3 := sq_sqrt (by norm_num)
  nlinarith

private lemma c7_poly :
    8 * (cK 7)^3 - 4 * (cK 7)^2 - 4 * cK 7 + 1 = 0 := by
  set x : ℝ := π / 7
  have hrel : cos (4*x) = -cos (3*x) := by
    rw [show 4*x = π - 3*x by dsimp [x]; ring, cos_pi_sub]
  rw [cos_four_poly, cos_three_poly] at hrel
  have hquart :
      8 * cos x^4 + 4 * cos x^3 - 8 * cos x^2 - 3 * cos x + 1 = 0 := by
    linarith
  have hfac :
      (cos x + 1) * (8*cos x^3 - 4*cos x^2 - 4*cos x + 1) = 0 := by
    calc
      (cos x + 1) * (8*cos x^3 - 4*cos x^2 - 4*cos x + 1) =
          8 * cos x^4 + 4 * cos x^3 - 8 * cos x^2 - 3 * cos x + 1 := by ring
      _ = 0 := hquart
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hxhalf : x < π / 2 := by dsimp [x]; nlinarith [pi_pos]
  have hxpos : 0 < cos x :=
    cos_pos_of_mem_Ioo ⟨by linarith [hx0, pi_pos], hxhalf⟩
  have hne : cos x + 1 ≠ 0 := by linarith
  have hp := (mul_eq_zero.mp hfac).resolve_left hne
  simpa [cK, x] using hp

private lemma c8_poly :
    8 * (cK 8)^4 - 8 * (cK 8)^2 + 1 = 0 := by
  have h := cos_four_poly (π / 8)
  rw [show 4 * (π / 8) = π / 2 by ring, cos_pi_div_two] at h
  simpa [cK] using h.symm

private lemma c9_poly :
    8 * (cK 9)^3 - 6 * cK 9 - 1 = 0 := by
  have h := cos_three_poly (π / 9)
  rw [show 3 * (π / 9) = π / 3 by ring, cos_pi_div_three] at h
  simpa [cK] using (show 8 * cos (π / 9)^3 - 6 * cos (π / 9) - 1 = 0 by nlinarith [h])

/-! Exact row evaluations.  Each proof is algebraic reduction modulo the
corresponding cosine polynomial; there is no approximate arithmetic. -/

lemma row_3_1_value : φP 3 1 1 = table_v31 := by
  rw [binding_formula_m1 (by norm_num) (by norm_num)]
  change F1 (cK 3) = table_v31
  unfold F1 table_v31 tableDen gP
  rw [aP_eq, bP_eq, cP_eq]
  have hpoly := c3_poly
  unfold cK at hpoly ⊢
  field_simp
  linear_combination
    (96632572442555601 : ℝ) * (-1250 * (2*cos (π / 3) + 1) *
      (48790000000000*(cos (π / 3))^4 - 73369626271580*(cos (π / 3))^2 + 24630000608359)) * hpoly

lemma row_4_1_value : φP 4 1 1 = table_v41 := by
  rw [binding_formula_m1 (by norm_num) (by norm_num)]
  change F1 (cK 4) = table_v41
  unfold F1 table_v41 tableDen gP
  rw [aP_eq, bP_eq, cP_eq]
  have hpoly := c4_poly
  unfold cK at hpoly ⊢
  field_simp
  linear_combination
    (96632572442555601 : ℝ) * (-10000 * (12197500000000*(cos (π / 4))^4 - 15293031567895*(cos (π / 4))^2 + 3096586010116)) * hpoly

lemma row_5_1_value : φP 5 1 1 = table_v51 := by
  rw [binding_formula_m1 (by norm_num) (by norm_num)]
  change F1 (cK 5) = table_v51
  unfold F1 table_v51 tableDen gP
  rw [aP_eq, bP_eq, cP_eq]
  have hpoly := c5_poly
  unfold cK at hpoly ⊢
  field_simp
  linear_combination
    (96632572442555601 : ℝ) * (-2500 * (24395000000000*(cos (π / 5))^4 + 12197500000000*(cos (π / 5))^3 -
      30586063135790*(cos (π / 5))^2 - 12243656567895*cos (π / 5) + 7717859520232)) * hpoly

lemma row_5_2_value : φP 5 2 3 = table_v52 := by
  rw [binding_formula_m2 (by norm_num) (by norm_num)]
  change F2 (cK 5) = table_v52
  unfold F2 table_v52 tableDen gP
  rw [aP_eq, bP_eq, cP_eq]
  have hpoly := c5_poly
  unfold cK at hpoly ⊢
  field_simp
  linear_combination
    (96632572442555601 : ℝ) * (-1250 * (780640000000000*(cos (π / 5))^8 + 390320000000000*(cos (π / 5))^7 -
      1951600000000000*(cos (π / 5))^6 - 878220000000000*(cos (π / 5))^5 +
      1658121494913680*(cos (π / 5))^4 + 609505747456840*(cos (π / 5))^3 -
      515941686392100*(cos (π / 5))^2 - 105594406331840*cos (π / 5) + 31879940815199)) * hpoly

lemma row_6_1_value : φP 6 1 1 = table_v61 := by
  rw [binding_formula_m1 (by norm_num) (by norm_num)]
  change F1 (cK 6) = table_v61
  unfold F1 table_v61 tableDen gP
  rw [aP_eq, bP_eq, cP_eq]
  have hpoly := c6_poly
  unfold cK at hpoly ⊢
  field_simp
  linear_combination
    (96632572442555601 : ℝ) * (-1250 * (48790000000000*(cos (π / 6))^4 - 48974626271580*(cos (π / 6))^2 + 6241437472569)) * hpoly

lemma row_7_1_value : φP 7 1 1 = table_v71 := by
  rw [binding_formula_m1 (by norm_num) (by norm_num)]
  change F1 (cK 7) = table_v71
  unfold F1 table_v71 tableDen gP
  rw [aP_eq, bP_eq, cP_eq]
  have hpoly := c7_poly
  unfold cK at hpoly ⊢
  field_simp
  linear_combination
    (96632572442555601 : ℝ) * (-6250 * (4879000000000*(cos (π / 7))^3 + 2439500000000*(cos (π / 7))^2 -
      4897462627158*cos (π / 7) - 1838856313579)) * hpoly

lemma row_7_2_value : φP 7 2 4 = table_v72 := by
  rw [binding_formula_m2 (by norm_num) (by norm_num)]
  change F2 (cK 7) = table_v72
  unfold F2 table_v72 tableDen gP
  rw [aP_eq, bP_eq, cP_eq]
  have hpoly := c7_poly
  unfold cK at hpoly ⊢
  field_simp
  linear_combination
    (96632572442555601 : ℝ) * (-6250 * (78064000000000*(cos (π / 7))^7 + 39032000000000*(cos (π / 7))^6 -
      175644000000000*(cos (π / 7))^5 - 78064000000000*(cos (π / 7))^4 +
      126780149491368*(cos (π / 7))^3 + 46313574745684*(cos (π / 7))^2 -
      27217631266368*cos (π / 7) - 6299546946763)) * hpoly

lemma row_7_3_value : φP 7 3 5 = table_v73 := by
  rw [binding_formula_m3 (by norm_num) (by norm_num)]
  change F3 (cK 7) = table_v73
  unfold F3 table_v73 tableDen gP
  rw [aP_eq, bP_eq, cP_eq]
  have hpoly := c7_poly
  unfold cK at hpoly ⊢
  field_simp
  linear_combination
    (96632572442555601 : ℝ) * (-25000 * (312256000000000*(cos (π / 7))^11 + 156128000000000*(cos (π / 7))^10 -
      1014832000000000*(cos (π / 7))^9 - 468384000000000*(cos (π / 7))^8 +
      1229508000000000*(cos (π / 7))^7 + 507416000000000*(cos (π / 7))^6 -
      668496850508632*(cos (π / 7))^5 - 234228925254316*(cos (π / 7))^4 +
      150902793987948*(cos (π / 7))^3 + 41899040680395*(cos (π / 7))^2 -
      9033005979316*cos (π / 7) - 2429831897954)) * hpoly

lemma row_8_1_value : φP 8 1 1 = table_v81 := by
  rw [binding_formula_m1 (by norm_num) (by norm_num)]
  change F1 (cK 8) = table_v81
  unfold F1 table_v81 tableDen gP
  rw [aP_eq, bP_eq, cP_eq]
  have hpoly := c8_poly
  unfold cK at hpoly ⊢
  field_simp
  linear_combination
    (96632572442555601 : ℝ) * (-12500 * (2439500000000*(cos (π / 8))^2 - 1838856313579)) * hpoly

lemma row_8_3_value : φP 8 3 3 = table_v83 := by
  rw [binding_formula_m3 (by norm_num) (by norm_num)]
  change F3 (cK 8) = table_v83
  unfold F3 table_v83 tableDen gP
  rw [aP_eq, bP_eq, cP_eq]
  have hpoly := c8_poly
  unfold cK at hpoly ⊢
  field_simp
  linear_combination
    (96632572442555601 : ℝ) * (-50000 * (156128000000000*(cos (π / 8))^10 - 468384000000000*(cos (π / 8))^8 +
      507416000000000*(cos (π / 8))^6 - 231789425254316*(cos (π / 8))^4 +
      37629915680395*(cos (π / 8))^2 - 752675647954)) * hpoly

lemma row_9_1_value : φP 9 1 1 = table_v91 := by
  rw [binding_formula_m1 (by norm_num) (by norm_num)]
  change F1 (cK 9) = table_v91
  unfold F1 table_v91 tableDen gP
  rw [aP_eq, bP_eq, cP_eq]
  have hpoly := c9_poly
  unfold cK at hpoly ⊢
  field_simp
  linear_combination
    (96632572442555601 : ℝ) * (-12500 * (2439500000000*(cos (π / 9))^3 - 2448731313579*cos (π / 9) + 304937500000)) * hpoly

lemma row_9_2_value : φP 9 2 5 = table_v92 := by
  rw [binding_formula_m2 (by norm_num) (by norm_num)]
  change F2 (cK 9) = table_v92
  unfold F2 table_v92 tableDen gP
  rw [aP_eq, bP_eq, cP_eq]
  have hpoly := c9_poly
  unfold cK at hpoly ⊢
  field_simp
  linear_combination
    (96632572442555601 : ℝ) * (-6250 * (78064000000000*(cos (π / 9))^7 - 175644000000000*(cos (π / 9))^5 +
      9758000000000*(cos (π / 9))^4 + 126780149491368*(cos (π / 9))^3 -
      14637000000000*(cos (π / 9))^2 - 27217631266368*cos (π / 9) + 4869768686421)) * hpoly

lemma row_9_4_value : φP 9 4 7 = table_v94 := by
  rw [binding_formula_m4 (by norm_num) (by norm_num)]
  change F4 (cK 9) = table_v94
  unfold F4 table_v94 tableDen gP
  rw [aP_eq, bP_eq, cP_eq]
  have hpoly := c9_poly
  unfold cK at hpoly ⊢
  field_simp
  linear_combination
    (96632572442555601 : ℝ) * (-25000 * (4996096000000000*(cos (π / 9))^15 - 21233408000000000*(cos (π / 9))^13 +
      624512000000000*(cos (π / 9))^12 + 36533952000000000*(cos (π / 9))^11 -
      2185792000000000*(cos (π / 9))^10 - 32474624000000000*(cos (π / 9))^9 +
      2927400000000000*(cos (π / 9))^8 + 15749116597965472*(cos (π / 9))^7 -
      1863778000000000*(cos (π / 9))^6 - 4026412123030944*(cos (π / 9))^5 +
      570806074745684*(cos (π / 9))^4 + 469555350733998*(cos (π / 9))^3 -
      75196959319605*(cos (π / 9))^2 - 13970888168526*cos (π / 9) + 2296699352046)) * hpoly

/-- Exact values of all thirteen rows.  This theorem is the formal counterpart
of the numerical-value column of the finite table. -/
theorem finite_table_values :
    φP 3 1 1 = table_v31 ∧ φP 4 1 1 = table_v41 ∧
    φP 5 1 1 = table_v51 ∧ φP 5 2 3 = table_v52 ∧ φP 6 1 1 = table_v61 ∧
    φP 7 1 1 = table_v71 ∧ φP 7 2 4 = table_v72 ∧ φP 7 3 5 = table_v73 ∧
    φP 8 1 1 = table_v81 ∧ φP 8 3 3 = table_v83 ∧
    φP 9 1 1 = table_v91 ∧ φP 9 2 5 = table_v92 ∧ φP 9 4 7 = table_v94 := by
  exact ⟨row_3_1_value, row_4_1_value,
    row_5_1_value, row_5_2_value, row_6_1_value,
    row_7_1_value, row_7_2_value, row_7_3_value,
    row_8_1_value, row_8_3_value,
    row_9_1_value, row_9_2_value, row_9_4_value⟩

/-! ### Positivity of the exact table values -/

private lemma c7_bounds :
    0 ≤ cK 7 ∧ cK 7 ≤ 1 ∧ 3/4 ≤ (cK 7)^2 ∧ 4/5 ≤ cK 7 := by
  have hmono : cos (π / 6) ≤ cos (π / 7) :=
    cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos]) (by nlinarith [pi_pos])
  rw [cos_pi_div_six] at hmono
  have hs3 : (√3 : ℝ)^2 = 3 := sq_sqrt (by norm_num)
  have hs30 : 0 ≤ (√3 : ℝ) := sqrt_nonneg _
  have hs34 : (4/5 : ℝ) ≤ √3/2 := by nlinarith
  have hc0 : 0 ≤ cK 7 := by
    unfold cK
    exact (cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩).le
  have hc1 : cK 7 ≤ 1 := cos_le_one _
  have hlo : √3/2 ≤ cK 7 := by simpa [cK] using hmono
  have hsq : 3/4 ≤ (cK 7)^2 := by
    have hp : 0 ≤ (cK 7 - √3/2) * (cK 7 + √3/2) :=
      mul_nonneg (sub_nonneg.mpr hlo) (by nlinarith)
    nlinarith
  exact ⟨hc0, hc1, hsq, le_trans hs34 hlo⟩

private lemma c8_gt_nine_tenths : (9/10 : ℝ) < cK 8 := by
  change (9/10 : ℝ) < cos (π / 8)
  rw [cos_pi_div_eight]
  have hs2 : (31/25 : ℝ) < √2 := (lt_sqrt (by norm_num)).2 (by norm_num)
  have hnon : 0 ≤ 2 + √2 := by positivity
  have hs : (√(2 + √2) : ℝ)^2 = 2 + √2 := sq_sqrt hnon
  have hroot : 0 ≤ √(2 + √2) := sqrt_nonneg _
  nlinarith

private lemma c9_bounds :
    0 ≤ cK 9 ∧ cK 9 ≤ 1 ∧ 4/5 ≤ (cK 9)^2 ∧ 9/10 ≤ cK 9 := by
  have hmono : cos (π / 8) ≤ cos (π / 9) :=
    cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos]) (by nlinarith [pi_pos])
  have hc8 := c8_gt_nine_tenths
  have hc9lo : (9/10 : ℝ) < cK 9 := by
    simpa [cK] using lt_of_lt_of_le hc8 hmono
  have hc0 : 0 ≤ cK 9 := by linarith
  have hc1 : cK 9 ≤ 1 := cos_le_one _
  have hsq : 4/5 ≤ (cK 9)^2 := by
    have hp : 0 < (cK 9 - 9/10) * (cK 9 + 9/10) :=
      mul_pos (sub_pos.mpr hc9lo) (by linarith)
    nlinarith
  exact ⟨hc0, hc1, hsq, hc9lo.le⟩

lemma table_v31_pos : 0 < table_v31 := by norm_num [table_v31, tableDen]
lemma table_v41_pos : 0 < table_v41 := by norm_num [table_v41, tableDen]
lemma table_v61_pos : 0 < table_v61 := by norm_num [table_v61, tableDen]

lemma table_v51_pos : 0 < table_v51 := by
  have hc : cK 5 ≤ 1 := cos_le_one _
  unfold table_v51 tableDen
  norm_num
  nlinarith

lemma table_v52_pos : 0 < table_v52 := by
  have hs5 : (2 : ℝ) < √5 := (lt_sqrt (by norm_num)).2 (by norm_num)
  have hc : (3/4 : ℝ) < cK 5 := by
    change (3/4 : ℝ) < cos (π / 5)
    rw [cos_pi_div_five]
    nlinarith
  unfold table_v52 tableDen
  norm_num
  nlinarith

lemma table_v71_pos : 0 < table_v71 := by
  obtain ⟨hc0, hc1, -, -⟩ := c7_bounds
  have hp : 0 ≤ (1 - cK 7) *
      (24965749890276 * (cK 7 + 1) - 12289813135790) := by
    exact mul_nonneg (sub_nonneg.mpr hc1) (by nlinarith)
  unfold table_v71 tableDen
  norm_num
  nlinarith

lemma table_v72_pos : 0 < table_v72 := by
  obtain ⟨-, hc1, hsq, -⟩ := c7_bounds
  unfold table_v72 tableDen
  norm_num
  nlinarith

lemma table_v73_pos : 0 < table_v73 := by
  obtain ⟨-, -, hsq, hc4⟩ := c7_bounds
  unfold table_v73 tableDen
  norm_num
  nlinarith

lemma table_v81_pos : 0 < table_v81 := by
  have hs : (cK 8)^2 ≤ 1 := by
    have h := abs_cos_le_one (π / 8)
    rw [sq_le_one_iff_abs_le_one]
    simpa [cK] using h
  unfold table_v81 tableDen
  norm_num
  nlinarith

lemma table_v83_pos : 0 < table_v83 := by
  have hmono : cos (π / 4) ≤ cos (π / 8) :=
    cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos]) (by nlinarith [pi_pos])
  rw [cos_pi_div_four] at hmono
  have hs2 : (√2 : ℝ)^2 = 2 := sq_sqrt (by norm_num)
  have hs20 : 0 ≤ (√2 : ℝ) := sqrt_nonneg _
  have hc0 : 0 ≤ cK 8 := by
    unfold cK
    exact (cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩).le
  have hlo : √2/2 ≤ cK 8 := by simpa [cK] using hmono
  have hsq : 1/2 ≤ (cK 8)^2 := by
    have hp : 0 ≤ (cK 8 - √2/2) * (cK 8 + √2/2) :=
      mul_nonneg (sub_nonneg.mpr hlo) (by nlinarith)
    nlinarith
  unfold table_v83 tableDen
  norm_num
  nlinarith

lemma table_v91_pos : 0 < table_v91 := by
  obtain ⟨hc0, hc1, -, -⟩ := c9_bounds
  have hp : 0 ≤ (1 - cK 9) *
      (4160958315046 * (cK 9 + 1) - 1031843855965) := by
    exact mul_nonneg (sub_nonneg.mpr hc1) (by nlinarith)
  unfold table_v91 tableDen
  norm_num
  nlinarith

lemma table_v92_pos : 0 < table_v92 := by
  obtain ⟨-, hc1, hsq, -⟩ := c9_bounds
  unfold table_v92 tableDen
  norm_num
  nlinarith

lemma table_v94_pos : 0 < table_v94 := by
  obtain ⟨-, -, hsq, hc9⟩ := c9_bounds
  unfold table_v94 tableDen
  norm_num
  nlinarith

/-- Every exact finite-table value is positive. -/
theorem finite_table_positive :
    0 < table_v31 ∧ 0 < table_v41 ∧ 0 < table_v51 ∧ 0 < table_v52 ∧ 0 < table_v61 ∧
    0 < table_v71 ∧ 0 < table_v72 ∧ 0 < table_v73 ∧ 0 < table_v81 ∧ 0 < table_v83 ∧
    0 < table_v91 ∧ 0 < table_v92 ∧ 0 < table_v94 := by
  exact ⟨table_v31_pos, table_v41_pos, table_v51_pos, table_v52_pos, table_v61_pos,
    table_v71_pos, table_v72_pos, table_v73_pos, table_v81_pos, table_v83_pos,
    table_v91_pos, table_v92_pos, table_v94_pos⟩

/-- The thirteen finite rows, now deduced only from their exact evaluated
values rather than from a uniform K≥5 argument. -/
theorem finite_table :
    0 < φP 3 1 1 ∧ 0 < φP 4 1 1 ∧
    0 < φP 5 1 1 ∧ 0 < φP 5 2 3 ∧ 0 < φP 6 1 1 ∧
    0 < φP 7 1 1 ∧ 0 < φP 7 2 4 ∧ 0 < φP 7 3 5 ∧
    0 < φP 8 1 1 ∧ 0 < φP 8 3 3 ∧
    0 < φP 9 1 1 ∧ 0 < φP 9 2 5 ∧ 0 < φP 9 4 7 := by
  rw [row_3_1_value, row_4_1_value, row_5_1_value, row_5_2_value, row_6_1_value,
    row_7_1_value, row_7_2_value, row_7_3_value, row_8_1_value, row_8_3_value,
    row_9_1_value, row_9_2_value, row_9_4_value]
  exact finite_table_positive

private lemma finite_canonical_cases {K m : ℕ} (hK3 : 3 ≤ K) (hK9 : K ≤ 9)
    (hm : m ∈ U K) (hhalf : 2*m < K) :
    (K=3 ∧ m=1) ∨ (K=4 ∧ m=1) ∨
    (K=5 ∧ (m=1 ∨ m=2)) ∨ (K=6 ∧ m=1) ∨
    (K=7 ∧ (m=1 ∨ m=2 ∨ m=3)) ∨
    (K=8 ∧ (m=1 ∨ m=3)) ∨
    (K=9 ∧ (m=1 ∨ m=2 ∨ m=4)) := by
  rcases (show 1 ≤ m ∧ m < K ∧ Nat.Coprime m K by
    simpa [U] using hm) with ⟨hm1, hmK, hcop⟩
  have hmb : m ≤ 4 := by omega
  interval_cases K <;> interval_cases m <;> norm_num at *

private lemma table_row_transfer {K m m0 Δ : ℕ} (hK : 3 ≤ K)
    (hm : m ∈ U K) (hms : mstar K m = m0)
    (hrow : 0 < φP K m0 Δ) : 0 < φP K m Δ := by
  calc
    0 < φP K (mstar K m) Δ := by simpa [hms] using hrow
    _ = φP K m Δ := φP_mstar hK hm Δ

/-- Finite exclusion, exactly by lookup in the thirteen evaluated rows. -/
theorem no_pure_mode_small {K m : ℕ} (hK3 : 3 ≤ K) (hK9 : K ≤ 9) (hm : m ∈ U K) :
    ∃ Δ, 1 ≤ Δ ∧ Δ < K ∧ 0 < φP K m Δ := by
  obtain ⟨hmr, hhalf⟩ := mstar_mem hK3 hm
  have hcases := finite_canonical_cases hK3 hK9 hmr hhalf
  rcases hcases with h31 | h41 | h5 | h61 | h7 | h8 | h9
  · rcases h31 with ⟨rfl, hmr1⟩
    refine ⟨1, by norm_num, by norm_num, ?_⟩
    exact table_row_transfer (by norm_num) hm hmr1 finite_table.1
  · rcases h41 with ⟨rfl, hmr1⟩
    refine ⟨1, by norm_num, by norm_num, ?_⟩
    exact table_row_transfer (by norm_num) hm hmr1 finite_table.2.1
  · rcases h5 with ⟨rfl, hmr1 | hmr2⟩
    · refine ⟨1, by norm_num, by norm_num, ?_⟩
      exact table_row_transfer (by norm_num) hm hmr1 finite_table.2.2.1
    · refine ⟨3, by norm_num, by norm_num, ?_⟩
      exact table_row_transfer (by norm_num) hm hmr2 finite_table.2.2.2.1
  · rcases h61 with ⟨rfl, hmr1⟩
    refine ⟨1, by norm_num, by norm_num, ?_⟩
    exact table_row_transfer (by norm_num) hm hmr1 finite_table.2.2.2.2.1
  · rcases h7 with ⟨rfl, hmr1 | hmr2 | hmr3⟩
    · refine ⟨1, by norm_num, by norm_num, ?_⟩
      exact table_row_transfer (by norm_num) hm hmr1 finite_table.2.2.2.2.2.1
    · refine ⟨4, by norm_num, by norm_num, ?_⟩
      exact table_row_transfer (by norm_num) hm hmr2 finite_table.2.2.2.2.2.2.1
    · refine ⟨5, by norm_num, by norm_num, ?_⟩
      exact table_row_transfer (by norm_num) hm hmr3 finite_table.2.2.2.2.2.2.2.1
  · rcases h8 with ⟨rfl, hmr1 | hmr3⟩
    · refine ⟨1, by norm_num, by norm_num, ?_⟩
      exact table_row_transfer (by norm_num) hm hmr1 finite_table.2.2.2.2.2.2.2.2.1
    · refine ⟨3, by norm_num, by norm_num, ?_⟩
      exact table_row_transfer (by norm_num) hm hmr3 finite_table.2.2.2.2.2.2.2.2.2.1
  · rcases h9 with ⟨rfl, hmr1 | hmr2 | hmr4⟩
    · refine ⟨1, by norm_num, by norm_num, ?_⟩
      exact table_row_transfer (by norm_num) hm hmr1 finite_table.2.2.2.2.2.2.2.2.2.2.1
    · refine ⟨5, by norm_num, by norm_num, ?_⟩
      exact table_row_transfer (by norm_num) hm hmr2 finite_table.2.2.2.2.2.2.2.2.2.2.2.1
    · refine ⟨7, by norm_num, by norm_num, ?_⟩
      exact table_row_transfer (by norm_num) hm hmr4 finite_table.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## Final certificate -/

theorem pure_mode_excluded (K m : ℕ) (hK : 3 ≤ K) (hm : m ∈ U K) :
    ∃ Δ, 1 ≤ Δ ∧ Δ < K ∧ 0 < φP K m Δ := by
  by_cases hlarge : 10 ≤ K
  · by_contra hnone
    have hfeas : ∀ Δ, 1 ≤ Δ → Δ < K → φP K m Δ ≤ 0 := by
      intro Δ h1 h2
      exact le_of_not_gt (fun hp => hnone ⟨Δ, h1, h2, hp⟩)
    exact no_pure_mode_large hlarge hm hfeas
  · exact no_pure_mode_small hK (by omega) hm

theorem certificate :
    (γP, βP) ∈ Ωcv 1 ∧
    (∀ Δ, 1 ≤ Δ → Δ ≤ 9 →
      137 / 500 * φP 10 2 Δ + 363 / 500 * φP 10 3 Δ < 0) ∧
    (∀ K m, 3 ≤ K → m ∈ U K →
      ∃ Δ, 1 ≤ Δ ∧ Δ < K ∧ 0 < φP K m Δ) := by
  exact ⟨P_in_Ωcv, mixed_condition, fun K m hK hm => pure_mode_excluded K m hK hm⟩

end Counterexample
end HeavyBall

#print axioms HeavyBall.Counterexample.mixed_condition
#print axioms HeavyBall.Counterexample.no_pure_mode_large
#print axioms HeavyBall.Counterexample.finite_table_values
#print axioms HeavyBall.Counterexample.finite_table
#print axioms HeavyBall.Counterexample.pure_mode_excluded
#print axioms HeavyBall.Counterexample.certificate
