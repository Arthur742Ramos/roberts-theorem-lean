import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Function.Basic

namespace Roberts

abbrev Valuation (N A : Type*) := N → A → Real

structure Mechanism (N A : Type*) where
  choiceFn : Valuation N A → A
  pay : Valuation N A → N → Real

def IsDSIC {N A : Type*} [Fintype N] [Fintype A]
    (M : Mechanism N A) : Prop := by
  classical
  exact ∀ i (v : Valuation N A) (vi2 : A → Real),
    (v i) (M.choiceFn v) - M.pay v i ≥
      (v i) (M.choiceFn (Function.update v i vi2)) -
        M.pay (Function.update v i vi2) i

lemma onto_exists {V A : Type*} {f : V → A}
    (hf : Function.Surjective f) (a : A) : ∃ v, f v = a :=
  hf a

def affineScore {N A : Type*} [Fintype N]
    (weights : N → Real) (k : A → Real) (v : Valuation N A) (a : A) : Real :=
  (Finset.univ.sum fun i => weights i * v i a) + k a

lemma update_self {N A : Type*} [DecidableEq N] (v : N → A) (i : N) :
    Function.update v i (v i) = v := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

lemma affineScore_congr {N A : Type*} [Fintype N]
    (weights : N → Real) (k : A → Real) (v vOther : Valuation N A) (a : A)
    (h : ∀ i, v i a = vOther i a) :
    affineScore weights k v a = affineScore weights k vOther a := by
  simp [affineScore, h]

def IsAffineMaximizer {N A : Type*} [Fintype N] [Fintype A]
    (f : Valuation N A → A) : Prop :=
  ∃ weights : N → Real, ∃ k : A → Real,
    (∀ i, 0 ≤ weights i) ∧
      (∃ i, weights i ≠ 0) ∧
        ∀ v a, affineScore weights k v (f v) ≥ affineScore weights k v a

-- M6 target theorem: proof deferred to a later milestone.
theorem roberts_theorem {N A : Type*} [Fintype N] [Nonempty N]
    [Fintype A] [Nonempty A] (hA : 3 ≤ Fintype.card A)
    (M : Mechanism N A) (hdsic : IsDSIC M)
    (honto : Function.Surjective M.choiceFn) :
    IsAffineMaximizer M.choiceFn := by
  sorry

end Roberts
