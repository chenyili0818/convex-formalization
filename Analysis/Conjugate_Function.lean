/-
Copyright (c) 2023 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Tactic
import Mathlib.Order.Bounds.Basic
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
  the defition of the conjugate function and the Fenchel inequality
  need to solve the sorry
-/
open LinearMap Set BigOperators Classical Convex Pointwise

variable {𝕜 E F α β ι : Type _}

section OrderedSemiring

variable [OrderedSemiring 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid α] [CompleteLinearOrder β]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 α] [SMul 𝕜 EReal] (s : Set E) (f : E → EReal) {g : EReal → α}

noncomputable section

def exist_fun_lt_top  : Prop :=
  ∃ x ∈ s, f x < ⊤

def forall_fun_gt_top : Prop :=
  ∀ x ∈ s, f x > ⊥

def properfun : Prop :=
  exist_fun_lt_top s f ∧ forall_fun_gt_top s f

def isSup (s : Set ℝ ) (x : ℝ) : Prop :=
  upperBounds s x ∧ ∀ y, upperBounds s y → x ≤ y

def conjugate_function (f : ℝ → ℝ) (y : ℝ) : (Set ℝ) :=
  upperBounds {y * x - f x | x : ℝ}

def conjugate_function1 (f : ℝ → ℝ) (y : ℝ) :  ℝ :=
  sSup {y * x - f x | x : ℝ}  --sSup只有在有上确界的时候能够实现

--将定义拓展到EReal
def conjugate_function2 (f : ℝ → EReal) (y : ℝ) :  ℝ :=
  sSup {y * x - f x | x : ℝ}  --sSup只有在有上确界的时候能够实现

--将定义扩展到R^n上
noncomputable section

open InnerProductSpace
noncomputable section

variable {n : Type _}[Fintype n]
variable {f: (EuclideanSpace ℝ n) → ℝ} {f' : ((EuclideanSpace ℝ n)) → ((EuclideanSpace ℝ n) →L[ℝ] ℝ)}
variable {l : ℝ} {a : ℝ}

def conjugate_function3 (f : (EuclideanSpace ℝ n) → ℝ) (y : (EuclideanSpace ℝ n)) : ℝ :=
  sSup { @inner ℝ _ _ y x - f x | x : (EuclideanSpace ℝ n)}

--Fenchel 不等式
theorem Fenchel (f : (EuclideanSpace ℝ n) → ℝ) (y x: (EuclideanSpace ℝ n)) : f x + conjugate_function3 f y  ≥  @inner ℝ _ _ y x
:= by
  have h : f x + conjugate_function3 f y = f x + sSup { @inner ℝ _ _ y x - f x | x : (EuclideanSpace ℝ n)} := by
    rfl
  rw[h]
  have h1 : sSup {x | ∃ x_1, inner y x_1 - f x_1 = x} ≥ inner y x - f x := by
    sorry
  have h2 : f x + sSup {x | ∃ x_1, inner y x_1 - f x_1 = x} ≥ inner y x := by
    exact Iff.mp tsub_le_iff_left h1
  apply h2