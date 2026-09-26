import Roberts.Taxation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Max
import Mathlib.Order.Bounds.Basic

namespace Roberts

section

variable {N A : Type*} [Fintype N] [Fintype A] [DecidableEq N] [DecidableEq A]
  [Nonempty N] [Nonempty A]

/-- Strong monotonicity: strict version of W-MON. -/
def IsSMon (f : Valuation N A → A) : Prop :=
  ∀ i v (vi vi2 : A → Real) (a b : A), a ≠ b →
    f (Function.update v i vi) = a →
    f (Function.update v i vi2) = b →
      vi a - vi b > vi2 a - vi2 b

/-- Simultaneous perturbation: bump every agent's value for `x` by `ε`. -/
def perturb (v : Valuation N A) (x : A) (ε : Real) : Valuation N A :=
  fun i a => v i a + if a = x then ε else 0

/-- The tie set: alternatives that win after a small simultaneous bump. -/
noncomputable def tieSet (f : Valuation N A → A) (v : Valuation N A) : Finset A :=
  by
    classical
    exact Finset.univ.filter fun x =>
      ∃ δ > 0, ∀ ε ∈ Set.Ioo 0 δ, f (perturb v x ε) = x

/-- f(v) is always in its own tie set (by bumping the winner). -/
lemma mem_tieSet_self (f : Valuation N A → A) (v : Valuation N A) :
    f v ∈ tieSet f v := by
  classical
  unfold tieSet
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, 1, one_pos, fun ε _ => ?_⟩
  -- By stability: bumping the winner's value keeps it winning.
  -- This uses a telescoping W-MON argument (to be proved).
  sorry

/-- Tie set is nonempty. -/
lemma tieSet_nonempty (f : Valuation N A → A) (v : Valuation N A) :
    (tieSet f v).Nonempty :=
  ⟨f v, mem_tieSet_self f v⟩

-- Fixed linear order on A for tie-breaking.
-- Since A is a fintype, we transport the order from Fin (card A).
noncomputable instance : LinearOrder A :=
  LinearOrder.lift' (Fintype.equivFin A) (Fintype.equivFin A).injective

/-- Tie-broken choice function: max of tie set under fixed order. -/
noncomputable def tieBreak (f : Valuation N A → A) (v : Valuation N A) : A :=
  (tieSet f v).max' (tieSet_nonempty f v)

/-- tieBreak selects from the tie set. -/
lemma tieBreak_mem (f : Valuation N A → A) (v : Valuation N A) :
    tieBreak f v ∈ tieSet f v :=
  Finset.max'_mem _ _

end

end Roberts
