/-
Copyright (c) 2023 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Ruichong Zhang
-/
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Analysis.Gradient
/-!
  the subdifferential of a convex function
-/

open Filter Topology Set InnerProductSpace

/- 次梯度 -/

/- 何琬仪 北京大学 -/

noncomputable section

variable {n : Type _} [Fintype n] [DecidableEq n]

variable {s : Set (EuclideanSpace ℝ n)}

variable {f : (EuclideanSpace ℝ n) → ℝ} {g : EuclideanSpace ℝ n} {x : EuclideanSpace ℝ n}

variable {f' : EuclideanSpace ℝ n → EuclideanSpace ℝ n →L[ℝ] ℝ}

set_option quotPrecheck false

local notation gradient "∇*" => (toDualMap ℝ _) gradient

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y


def IsSubgradAt (_ : ConvexOn ℝ s f) (g x :  EuclideanSpace ℝ n) : Prop :=
  ∀ y ∈ s, f y ≥ f x + inner g (y - x)

-- def HasSubderivAt (hf : ConvexOn ℝ s f) (x :  EuclideanSpace ℝ n) :
-- 这个定义里没要求 x ∈ s
def SubderivAt (hf : ConvexOn ℝ s f) (x :  EuclideanSpace ℝ n) : Set (EuclideanSpace ℝ n) :=
  {g : EuclideanSpace ℝ n| IsSubgradAt hf g x}

@[simp]
theorem mem_SubderivAt (hf : ConvexOn ℝ s f) : IsSubgradAt hf g x ↔ g ∈ SubderivAt hf x := ⟨id, id⟩


/- 次梯度的存在性 -/

variable (hf : ConvexOn ℝ s f)

theorem existence_of_subgrad (hx : x ∈ interior s) : ∃ g, IsSubgradAt hf g x := by
  sorry



/- 次梯度的性质 -/

-- 次微分在一定条件下分别为闭凸集和非空有界集

open EuclideanSpace

theorem Subderiv_closed : ∀ x ∈ s, IsClosed (SubderivAt hf x) := by
  intro x _
  by_cases e : SubderivAt hf x = ∅
  · apply Eq.subst (Eq.symm e) isClosed_empty
  rw [← isSeqClosed_iff_isClosed]
  intro g g' hg cg y ys
  obtain cg' := Tendsto.const_add (f x) (Filter.Tendsto.inner cg tendsto_const_nhds)
  apply le_of_tendsto_of_tendsto' cg' tendsto_const_nhds (fun n => hg n y ys)

theorem Subderiv_convex : ∀ x ∈ s, Convex ℝ (SubderivAt hf x) := by
  intro x _
  by_cases e : SubderivAt hf x = ∅
  · apply Eq.subst (Eq.symm e) convex_empty
  intro g₁ h1 g₂ h2 a b lea leb abeq y ys
  have ineq1 : a • f y ≥ a • f x + a • ⟪g₁, y - x⟫ := by
    rw [← smul_add]
    apply smul_le_smul_of_nonneg (h1 y ys) lea
  have ineq2 : b • f y ≥ b • f x + b • inner g₂ (y - x) := by
    rw [← smul_add]
    apply smul_le_smul_of_nonneg (h2 y ys) leb
  have eq : (a • f x + a • inner g₁ (y - x)) + (b • f x + b • inner g₂ (y - x)) = f x + inner (a • g₁ + b • g₂) (y - x) := by
    rw [add_add_add_comm, ← Eq.symm (Convex.combo_self abeq (f x))]
    apply congrArg (HAdd.hAdd (f x))
    rw [inner_add_left, inner_smul_left, inner_smul_left]; rfl
  rw [Eq.symm (Convex.combo_self abeq (f y)), ← eq]
  apply add_le_add ineq1 ineq2

theorem Subderiv_bounded : ∀ x ∈ interior s, Metric.Bounded (SubderivAt hf x) := by
  intro x h
  rw [bounded_iff_forall_norm_le]
  rw [interior_eq_nhds', mem_setOf, Metric.mem_nhds_iff] at h
  obtain ⟨ε, εpos, bs⟩ := h
  have ineq : ∀ i ∈ Finset.univ, ‖(ε / 2) • single (i : n) (1 : ℝ)‖ < ε := by
    intro i _
    rw [norm_smul, congrArg (HMul.hMul ‖ε / 2‖) (norm_single i (1 : ℝ)), ← norm_mul, congrArg norm (mul_one (ε / 2))]
    apply lt_of_eq_of_lt _ (half_lt_self_iff.mpr εpos)
    have : ‖ε / 2‖ = |ε / 2| := rfl
    rw [this, (abs_eq_self.mpr (le_of_lt (half_pos εpos)))]
  have eq : ∀ i ∈ Finset.univ,
    ‖x - (x + (ε / 2) • single (i : n) (1 : ℝ))‖ = ‖(ε / 2) • single i (1 : ℝ)‖ := by
      intro i _; rw [norm_sub_rev]; congr; rw [add_sub_cancel']
  have eq' : ∀ i ∈ Finset.univ,
    ‖x - (x - (ε / 2) • single (i : n) (1 : ℝ))‖ = ‖(ε / 2) • single i (1 : ℝ)‖ := by
      intro i _; congr; field_simp
  obtain his := fun i is => bs (mem_ball_iff_norm'.mpr (by linarith [ineq i is, eq i is]))
  obtain his' := fun i is => bs (mem_ball_iff_norm'.mpr (by linarith [ineq i is, eq' i is]))
  let C := fun i =>
    (max |(- ((f (x - (ε / 2) • single i (1 : ℝ)) - f x) / (ε / 2)))|
        |((f (x + (ε / 2) • single i (1 : ℝ)) - f x) / (ε / 2))|) ^ 2
  use Real.sqrt (Finset.sum Finset.univ C); intro g hg
  have eq2 : ∀ i ∈ Finset.univ, g i = (1 / (ε / 2)) * (⟪g, (ε / 2) • single i (1 : ℝ)⟫) := by
    intro i _
    have eq' : (1 : ℝ) * ⟪g, single i (1 : ℝ)⟫ = 1 / (ε / 2) * (ε / 2) * ⟪g, single i (1 : ℝ)⟫ := by
      apply congrFun (congrArg HMul.hMul _) (⟪g, single i 1⟫)
      exact Eq.symm (one_div_mul_cancel (ne_iff_lt_or_gt.mpr <|Or.inr (half_pos εpos)))
    have eq1 : ⟪g, single i 1⟫ = g i := by rw [inner_single_right, one_mul]; rfl
    rw [← eq1, ← (one_mul ⟪g, (single i (1 : ℝ))⟫), eq', mul_assoc, mul_eq_mul_left_iff]
    left; rw [← inner_smul_right]
  have ineq1 : ∀ i ∈ Finset.univ, g i ≤ (f (x + (ε / 2) • single i (1 : ℝ)) - f x) / (ε / 2) := by
    intro i is; specialize hg (x + (ε / 2) • single i (1 : ℝ)) (his i is)
    have hg' : f (x + (ε / 2) • single i (1 : ℝ)) - f x ≥ ⟪g, (ε / 2) • single i (1 : ℝ)⟫ := by
      calc
        ⟪g, (ε / 2) • single i (1 : ℝ)⟫ = ⟪g, x + (ε / 2) • single i (1 : ℝ) - x⟫ := by
          congr; field_simp
        _ ≤ f (x + (ε / 2) • single i (1 : ℝ)) - f x := Iff.mpr le_sub_iff_add_le' hg
    calc
      g i = (1 / (ε / 2)) * (⟪g, (ε / 2) • single i (1 : ℝ)⟫) := eq2 i is
      _ ≤ (1 / (ε / 2)) * (f (x + (ε / 2) • single i (1 : ℝ)) - f x) :=
        (mul_le_mul_left (one_div_pos.mpr (half_pos εpos))).mpr hg'
      _ = (f (x + (ε / 2) • single i (1 : ℝ)) - f x) / (ε / 2) := by rw [mul_comm, mul_one_div]
  have ineq2 : ∀ i ∈ Finset.univ, - (g i) ≤ (f (x - (ε / 2) • single i (1 : ℝ)) - f x) / (ε / 2) := by
    intro i is; specialize hg (x - (ε / 2) • single i (1 : ℝ)) (his' i is)
    have hg' : f (x - (ε / 2) • single i (1 : ℝ)) - f x ≥ - (⟪g, (ε / 2) • EuclideanSpace.single i (1 : ℝ)⟫) := by
      calc
        - (⟪g, (ε / 2) • single i (1 : ℝ)⟫) = ⟪g, x - (ε / 2) • single i (1 : ℝ) - x⟫ := by
          rw [← inner_neg_right g ((ε / 2) • single i (1 : ℝ))]
          congr; field_simp
        _ ≤ f (x - (ε / 2) • single i (1 : ℝ)) - f x := Iff.mpr le_sub_iff_add_le' hg
    calc
      - (g i) = (1 / (ε / 2)) * (- (⟪g, (ε / 2) • single i (1 : ℝ)⟫)) := by rw [eq2 i is, neg_mul_eq_mul_neg]
      _ ≤ (1 / (ε / 2)) * (f (x - (ε / 2) • single i (1 : ℝ)) - f x) := by
        rw [(mul_le_mul_left (one_div_pos.mpr (half_pos εpos)))]; exact hg'
      _ = (f (x - (ε / 2) • single i (1 : ℝ)) - f x) / (ε / 2) := by rw [mul_comm, mul_one_div]
  have ineq3 : Finset.sum Finset.univ (fun i => ‖g i‖ ^ 2) ≤ (Finset.sum Finset.univ C) := by
    apply Finset.sum_le_sum
    intro i is; simp only [Real.rpow_two]
    apply sq_le_sq.mpr; simp only [abs_abs, abs_norm]
    calc
      ‖g i‖ = |g i| := rfl
      _ ≤ max |(-((f (x - (ε / 2) • single i (1 : ℝ)) - f x) / (ε / 2)))|
        |((f (x + (ε / 2) • single i (1 : ℝ)) - f x) / (ε / 2))| :=
          abs_le_max_abs_abs (neg_le.mpr (ineq2 i is)) (ineq1 i is)
      _ ≤ |(max |(-((f (x - (ε / 2) • single i (1 : ℝ)) - f x) / (ε / 2)))|
        |((f (x + (ε / 2) • single i (1 : ℝ)) - f x) / (ε / 2))|)| :=
          le_abs_self (max |(-((f (x - (ε / 2) • single i (1 : ℝ)) - f x) / (ε / 2)))|
              |(f (x + (ε / 2) • single i (1 : ℝ)) - f x) / (ε / 2)|)
  calc
    ‖g‖ = Real.sqrt (Finset.sum Finset.univ (fun i => ‖g i‖ ^ 2)) := by
      simp only [Real.rpow_two]; rw [norm_eq]
    _ ≤ Real.sqrt (Finset.sum Finset.univ C) := by
      apply (Real.sqrt_le_sqrt_iff _ ).mpr ineq3
      apply Finset.sum_nonneg'
      intro i; simp only [Real.rpow_two]; apply sq_nonneg


lemma first_order_condition_gradn' {f: (EuclideanSpace ℝ n) → ℝ} {gradf : (EuclideanSpace ℝ n)}
  {s : Set (EuclideanSpace ℝ n)} {x: (EuclideanSpace ℝ n)} (h: HasGradnAt f gradf x) (hf: ConvexOn ℝ s f) (xs: x∈ s) :
  ∀ (y:(EuclideanSpace ℝ n)), y ∈ s → f x + inner gradf (y - x) ≤ f y:= by
  have H1: ∀ (y:(EuclideanSpace ℝ n)), y ∈ s → f x + (gradf ∇*) (y - x) ≤ f y:= by
    rw [HasGradnAt] at h
    apply first_order_condition; apply h;
    apply hf; apply xs
  intro y ys
  specialize H1 y ys
  exact H1

-- 函数在可微点处次梯度唯一
theorem subgrad_of_grad (hx : x ∈ interior s) (hf : ConvexOn ℝ s f) (h : HasGradnAt f g x) :
  SubderivAt hf x = {g} := by
  obtain h' := HasGradn_HasFDeriv h
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  constructor
  · use g; intro y ys
    exact first_order_condition_gradn h hf (interior_subset hx) y ys
  intro g' hg'; by_contra neq
  apply not_le_of_lt (norm_sub_pos_iff.mpr neq)
  let v := g' - g; obtain vneq := sub_ne_zero.mpr neq
  have : Tendsto (fun (t : ℝ) => (f (x + t • v) - f x - ⟪g, t • v⟫) * ‖t • v‖⁻¹) (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]; intro ε εpos
    unfold HasFDerivAt at h'
    rw [hasFDerivAtFilter_iff_tendsto, Metric.tendsto_nhds_nhds] at h'
    obtain ⟨δ, δpos, hδ⟩ := h' ε εpos
    use (δ * ‖v‖⁻¹)
    obtain pos := mul_pos δpos (inv_pos.mpr (norm_pos_iff.mpr vneq))
    constructor
    · exact pos
    intro t _ ht; rw [dist_eq_norm] at ht; rw [dist_eq_norm]
    have : dist (x + t • v) x < δ := by
      rw [dist_eq_norm, add_sub_cancel', norm_smul, ← (sub_zero t)]
      apply lt_of_lt_of_eq ((mul_lt_mul_right (norm_sub_pos_iff.mpr neq)).mpr ht)
      rw [mul_assoc, inv_mul_cancel (norm_ne_zero_iff.mpr vneq), mul_one]
    specialize hδ this; rw [dist_eq_norm] at hδ
    have eq1 : ‖‖x + t • v - x‖⁻¹‖ = ‖t • v‖⁻¹ := by
      rw [add_sub_cancel', norm_inv, norm_norm]
    have eq2 : (g ∇*) (x + t • v - x) = ⟪g, t • v⟫ := by rw [add_sub_cancel']; exact rfl
    have eq3 : ‖(f (x + t • v) - f x - ⟪g, t • v⟫) * ‖t • v‖⁻¹ - 0‖ =
      ‖f (x + t • v) - f x - ⟪g, t • v⟫‖ * ‖t • v‖⁻¹ := by
        rw [sub_zero, norm_mul, norm_inv, norm_norm]
    have eq : ‖‖x + t • v - x‖⁻¹ * ‖f (x + t • v) - f x - (g ∇*) (x + t • v - x)‖ - 0‖ =
      ‖(f (x + t • v) - f x - ⟪g, t • v⟫) * ‖t • v‖⁻¹ - 0‖ := by
        rw [sub_zero, norm_mul, norm_norm, mul_comm, eq1, eq2, ← eq3]
    apply Eq.trans_lt (Eq.symm eq) hδ
  apply ge_of_tendsto this
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff]
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨ε, εpos, ballmem⟩ := hx
  obtain pos := mul_pos εpos (inv_pos.mpr (norm_pos_iff.mpr vneq))
  use (ε * ‖v‖⁻¹); use pos; intro t ht
  have tball := ht.1; have tlt : t > 0 := ht.2
  have tvpos : ‖t • v‖⁻¹ > 0 := by
    apply inv_pos.mpr; rw [norm_smul]
    apply smul_pos (abs_pos_of_pos tlt) (norm_sub_pos_iff.mpr neq)
  have mems : x + t • v ∈ s := by
    apply ballmem
    rw [mem_ball_iff_norm, sub_zero] at tball
    rw [mem_ball_iff_norm, add_sub_cancel', norm_smul]
    have : ‖t‖ * ‖v‖ < ε * ‖v‖⁻¹ * ‖v‖ := by
      apply (mul_lt_mul_right (norm_sub_pos_iff.mpr neq)).mpr tball
    rwa [mul_assoc, inv_mul_cancel (norm_ne_zero_iff.mpr vneq), mul_one] at this
  obtain ineq1 := hg' (x + t • v) mems; rw [add_sub_cancel'] at ineq1
  have eq1 : ‖v‖ = (⟪g', t • v⟫ - ⟪g, t • v⟫) * ‖t • v‖⁻¹ := by
    have eq2 : ‖v‖ = ⟪v, v⟫ * ‖v‖⁻¹ := by
      rw [real_inner_self_eq_norm_sq]
      apply (div_eq_iff _).mp
      · rw [div_inv_eq_mul, pow_two]
      exact inv_ne_zero (norm_ne_zero_iff.mpr vneq)
    have eq3 : ⟪v, v⟫ * ‖v‖⁻¹ = ⟪v, t • v⟫ * ‖t • v‖⁻¹ := by
      have : ⟪v, t • v⟫ = ⟪v, v⟫ * t := by rw [inner_smul_right, mul_comm]
      rw [this, mul_assoc]
      have : ‖v‖⁻¹ = t * ‖t • v‖⁻¹ := by
        have :  t * ‖t • v‖⁻¹ = t / ‖t • v‖ := rfl
        rw [this, inv_eq_one_div]
        have : t = ‖t‖ := by
          have : ‖t‖ = |t| := rfl
          rw [this, abs_of_pos tlt]
        rw [this, norm_smul, norm_norm, div_mul_eq_div_div, div_self]
        rw [norm_ne_zero_iff]
        exact ne_of_gt tlt
      rw [this]
    rw [eq2, eq3, mul_eq_mul_right_iff];
    left; rw [inner_sub_left]
  rw [mem_setOf, eq1, mul_le_mul_right tvpos]
  apply sub_le_sub_right (le_sub_iff_add_le'.mpr ineq1)

theorem subgrad_of_grad' (hx : x ∈ interior s) (hf : ConvexOn ℝ s f) (h : HasFDerivAt f (f' x) x) :
  SubderivAt hf x = {grad (f' x)} := by
    obtain h' := HasFDeriv_HasGradn h
    exact subgrad_of_grad hx hf h'


-- 次梯度的单调性
theorem subgrad_mono {u v : EuclideanSpace ℝ n} (hf : ConvexOn ℝ s f) (xs : x ∈ s) (ys : y ∈ s)
  (hu : u ∈ SubderivAt hf x) (hv : v ∈ SubderivAt hf y) :
  ⟪u - v, x - y⟫ ≥ (0 : ℝ):= by
    specialize hu y ys
    specialize hv x xs
    have ineq1 : ⟪u, x - y⟫ ≥ f x - f y := by
      rw [congrArg (inner u) (Eq.symm (neg_sub y x)), inner_neg_right]; linarith
    have ineq2 := Iff.mpr le_sub_iff_add_le' hv
    rw [inner_sub_left]; linarith

/- 次梯度的计算 -/

variable (xs : x ∈ s)

variable [SMul ℝ EReal]

/- 函数之和的次梯度 -/

open Pointwise

theorem subgrad_of_add {s t : Set (EuclideanSpace ℝ n)} {f₁ f₂ : EuclideanSpace ℝ n → ℝ}
  (hf₁ : ConvexOn ℝ s f₁) (hf₂ : ConvexOn ℝ t f₂) (hadd : ConvexOn ℝ (s ∩ t) (f₁ + f₂)):
    ∀ (x : EuclideanSpace ℝ n), SubderivAt hf₁ x + SubderivAt hf₂ x ⊆ SubderivAt hadd x := by
      intro x y ymem; intro y' hy'
      obtain ⟨y₁, y₂, hy₁, hy₂, eq⟩ := Set.mem_add.mpr ymem
      have eq' : y₁ + y₂ = y := eq
      have : (f₁ + f₂) y' ≥ (f₁ x + ⟪y₁, y' - x⟫) + (f₂ x + ⟪y₂, y' - x⟫ ):= add_le_add (hy₁ y' hy'.1) (hy₂ y' hy'.2)
      rwa [add_add_add_comm, ← inner_add_left, eq'] at this

-- 函数族的上确界


/- 无约束不可微问题的最优性理论 -/

theorem zero_mem (hf : ConvexOn ℝ s f) (h : x ∈ {x | ∀ y ∈ s, f x ≤ f y}) :
  (0 : EuclideanSpace ℝ n) ∈ SubderivAt hf x :=
    fun y ys => le_of_le_of_eq' (h y ys) (by rw [inner_zero_left, add_zero])

theorem isGlobalmin (hf : ConvexOn ℝ s f) (h : (0 : EuclideanSpace ℝ n) ∈ SubderivAt hf x ) :
  x ∈ {x | ∀ y ∈ s, f x ≤ f y} := by
    intro y ys; specialize h y ys
    rwa [inner_zero_left, add_zero] at h

theorem zero_mem_iff_isGlobalmin (hf : ConvexOn ℝ s f) :
  (0 : EuclideanSpace ℝ n) ∈ SubderivAt hf x ↔ x ∈ {x | ∀ y ∈ s, f x ≤ f y} :=
    ⟨fun h => isGlobalmin hf h, fun h => zero_mem hf h⟩
