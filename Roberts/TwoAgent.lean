import Roberts.NoVeto

namespace Roberts

section

variable {N A : Type*} [Fintype N] [Fintype A] [DecidableEq N] [DecidableEq A]
  [Nonempty N] [Nonempty A]

/-- Affine price structure for agent i: payments take the form
    price M i v a = h v - alpha * v i a - beta a with 0 ≤ alpha.
    This is the price representation of Lemma 8 in the modular proof. -/
def HasAffinePrices (M : Mechanism N A) (i : N) : Prop :=
  Exists fun alpha : Real => 0 ≤ alpha ∧ Exists fun h : Valuation N A → Real =>
    Exists fun beta : A → Real => ∀ v a, price M i v a = h v - alpha * v i a - beta a

/-- Lemma 8 price representation: in the two-agent case, if the mechanism is
    DSIC, the choice function is S-MON and onto, and agent i1 has no veto power
    (equivalently agent i2 is decisive), then i1's prices are affine in i1's values. -/
lemma price_affine_form (M : Mechanism N A) (hdsic : IsDSIC M)
    (hsmon : IsSMon M.choiceFn) (honto : Function.Surjective M.choiceFn)
    (h2 : Fintype.card N = 2) (i1 i2 : N) (h12 : i1 ≠ i2)
    (hall : ∀ i, i = i1 ∨ i = i2)
    (hdec : HasNoVetoPower M.choiceFn i1) :
    HasAffinePrices M i1 := by
  sorry

/-- Lemma 8 of Dobzinski-Nisan: in the two-agent case, DSIC plus S-MON plus
    onto plus decisiveness of the second agent implies the choice function
    is an affine maximizer. -/
theorem two_agent_affine_maximizer (M : Mechanism N A) (hdsic : IsDSIC M)
    (hsmon : IsSMon M.choiceFn) (honto : Function.Surjective M.choiceFn)
    (h2 : Fintype.card N = 2) (i1 i2 : N) (h12 : i1 ≠ i2)
    (hall : ∀ i, i = i1 ∨ i = i2)
    (hdec : HasNoVetoPower M.choiceFn i1) :
    IsAffineMaximizer M.choiceFn := by
  sorry

end

end Roberts
