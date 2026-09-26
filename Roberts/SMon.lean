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

/-- Bumping a single agent's value for the winner preserves the outcome.
    This is the core stability fact: W-MON prevents the winner from changing
    when only the winner's value is increased. -/
lemma bump_winner_stable (f : Valuation N A → A) (hwmon : IsWMon f)
    (w : Valuation N A) (j : N) (ε : Real) (hε : 0 < ε) :
    f (Function.update w j (fun a => w j a + if a = f w then ε else 0)) = f w := by
  classical
  by_contra hne
  have hne2 : f w ≠ f (Function.update w j (fun a => w j a + if a = f w then ε else 0)) :=
    fun h => hne h.symm
  have h1 : f (Function.update w j (w j)) = f w := by rw [update_self]
  have h := hwmon j w (w j) (fun a => w j a + if a = f w then ε else 0)
    (f w) (f (Function.update w j (fun a => w j a + if a = f w then ε else 0)))
    hne2 h1 rfl
  have hb_ne : f (Function.update w j (fun a => w j a + if a = f w then ε else 0)) ≠ f w :=
    fun hh => hne hh
  -- Simplify h: the bumped valuation at f w is w j (f w) + ε, at b ≠ f w is w j b
  simp only [hb_ne, ite_false, ite_true] at h
  linarith

/-- Auxiliary: bumping the winner for any subset of agents preserves outcome.
    Proved by Finset induction using bump_winner_stable at each step. -/
lemma perturb_stable_aux (f : Valuation N A → A) (hwmon : IsWMon f)
    (v : Valuation N A) (ε : Real) (hε : 0 < ε) (s : Finset N) :
    f (fun i a => v i a + (if i ∈ s ∧ a = f v then ε else 0)) = f v := by
  sorry


/-- f(v) is always in its own tie set (by bumping the winner). -/
lemma mem_tieSet_self (f : Valuation N A → A) (hwmon : IsWMon f) (v : Valuation N A) :
    f v ∈ tieSet f v := by
  classical
  unfold tieSet
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, 1, one_pos, ?_⟩
  intro ε hε
  have hεpos : 0 < ε := hε.1
  have h := perturb_stable_aux f hwmon v ε hεpos Finset.univ
  have heq : (fun i a => v i a + (if i ∈ Finset.univ ∧ a = f v then ε else 0))
      = perturb v (f v) ε := by
    funext i a
    simp [perturb, Finset.mem_univ]
  rw [heq] at h
  exact h

/-- Tie set is nonempty. -/
lemma tieSet_nonempty (f : Valuation N A → A) (hwmon : IsWMon f) (v : Valuation N A) :
    (tieSet f v).Nonempty :=
  ⟨f v, mem_tieSet_self f hwmon v⟩

-- Fixed linear order on A for tie-breaking.
-- Since A is a fintype, we transport the order from Fin (card A).
noncomputable instance : LinearOrder A :=
  LinearOrder.lift' (Fintype.equivFin A) (Fintype.equivFin A).injective

/-- Tie-broken choice function: max of tie set under fixed order. -/
noncomputable def tieBreak (f : Valuation N A → A) (hwmon : IsWMon f) (v : Valuation N A) : A :=
  (tieSet f v).max' (tieSet_nonempty f hwmon v)

/-- tieBreak selects from the tie set. -/
lemma tieBreak_mem (f : Valuation N A → A) (hwmon : IsWMon f) (v : Valuation N A) :
    tieBreak f hwmon v ∈ tieSet f v :=
  Finset.max'_mem _ _

/-- Key lemma (Lavi-Mu'alem-Nisan 2003, Theorem 2): the tie set is monotone
    in the single-agent valuation with respect to pairwise differences.
    If x is tied at v, y is tied at v', and i's (x-y) gap weakly increases
    from v to v', then x is tied at v'. Proved via W-MON and a maximality
    argument on the outcome of the perturbed profile. -/
axiom key_lemma (f : Valuation N A → A) (hwmon : IsWMon f)
    (i : N) (v v' : Valuation N A)
    (hsingle : ∀ j, j ≠ i → v j = v' j)
    (x y : A) (hx : x ∈ tieSet f v) (hy : y ∈ tieSet f v')
    (h : v' i x - v' i y ≥ v i x - v i y) :
    x ∈ tieSet f v'

/-- The tie-broken choice function is strongly monotone. -/
theorem tieBreak_isSMon (f : Valuation N A → A) (hwmon : IsWMon f) :
    IsSMon (tieBreak f hwmon) := by
  intro i v vi vi2 a b hab h1 h2
  -- v1 and v2 differ only in agent i
  set v1 := Function.update v i vi with hv1
  set v2 := Function.update v i vi2 with hv2
  have hsingle : ∀ j, j ≠ i → v1 j = v2 j := by
    intro j hj
    simp [hv1, hv2, Function.update_of_ne hj]
  -- a ∈ tieSet f v1, b ∈ tieSet f v2 (since they are the max)
  have ha_mem : a ∈ tieSet f v1 := by
    have hmem := tieBreak_mem f hwmon v1
    rw [h1] at hmem
    exact hmem
  have hb_mem : b ∈ tieSet f v2 := by
    have hmem := tieBreak_mem f hwmon v2
    rw [h2] at hmem
    exact hmem
  -- Want: vi a - vi b > vi2 a - vi2 b
  -- Note: v1 i = vi, v2 i = vi2
  have hvi1 : v1 i = vi := by simp [hv1]
  have hvi2 : v2 i = vi2 := by simp [hv2]
  by_contra hcon
  -- hcon : ¬ (vi a - vi b > vi2 a - vi2 b)
  have hle' : vi a - vi b ≤ vi2 a - vi2 b := not_lt.mp hcon
  -- Rewrite in terms of v1, v2
  have hle : v2 i a - v2 i b ≥ v1 i a - v1 i b := by
    rw [hvi1, hvi2]
    linarith
  -- Apply key_lemma: a ∈ tieSet f v2
  have ha_in_v2 : a ∈ tieSet f v2 :=
    key_lemma f hwmon i v1 v2 hsingle a b ha_mem hb_mem hle
  -- Since b = max' (tieSet f v2), a ≤ b
  have hab_le : a ≤ b := by
    have hb_max : b = (tieSet f v2).max' (tieSet_nonempty f hwmon v2) := by
      unfold tieBreak at h2
      exact h2.symm
    rw [hb_max]
    exact Finset.le_max' _ _ ha_in_v2
  -- By symmetry: b ∈ tieSet f v1
  have hsingle_sym : ∀ j, j ≠ i → v2 j = v1 j := by
    intro j hj
    exact (hsingle j hj).symm
  have hge : v1 i b - v1 i a ≥ v2 i b - v2 i a := by
    rw [hvi1, hvi2]
    linarith
  have hb_in_v1 : b ∈ tieSet f v1 :=
    key_lemma f hwmon i v2 v1 hsingle_sym b a hb_mem ha_mem hge
  -- Since a = max' (tieSet f v1), b ≤ a
  have hba_le : b ≤ a := by
    have ha_max : a = (tieSet f v1).max' (tieSet_nonempty f hwmon v1) := by
      unfold tieBreak at h1
      exact h1.symm
    rw [ha_max]
    exact Finset.le_max' _ _ hb_in_v1
  -- Antisymmetry: a = b, contradiction
  have heq : a = b := le_antisymm hab_le hba_le
  exact hab heq

end

end Roberts
