import Roberts.TwoAgent

namespace Roberts

section

variable {N A : Type*} [Fintype N] [Fintype A] [DecidableEq N] [DecidableEq A]
  [Nonempty N] [Nonempty A]

/-- The choice function with agent i₀'s valuation fixed at vi₀. Used to state
    the per-slice affine representations in the n ≥ 3 induction step. -/
def slice (f : Valuation N A → A) (i₀ : N) (vi₀ : A → Real) : Valuation N A → A :=
  fun v => f (Function.update v i₀ vi₀)

/-- Lemma 9 (Dobzinski-Nisan, weight independence): in the induction step for n ≥ 3,
    the affine weights of the sliced (n-1)-agent problems do not depend on the fixed
    agent's valuation. If all agents other than i₀ have no veto power and f is S-MON,
    then for any choice of per-slice affine representations, the weights of agents
    i ≠ i₀ are independent of i₀'s fixed valuation. -/
lemma weights_independent_of_fixed_agent
    (f : Valuation N A → A) (hsmon : IsSMon f)
    (i₀ : N) (hveto : ∀ i, i ≠ i₀ → HasNoVetoPower f i)
    (w : (A → Real) → N → Real) (k : (A → Real) → A → Real)
    (hrep : ∀ vi₀ : A → Real,
      (∀ i, 0 ≤ w vi₀ i) ∧
      (∀ v a, affineScore (w vi₀) (k vi₀) v (slice f i₀ vi₀ v) ≥
        affineScore (w vi₀) (k vi₀) v a)) :
    ∀ vi₀ vi₀' i, i ≠ i₀ → w vi₀ i = w vi₀' i := by
  sorry

/-- Lemma 10 (Dobzinski-Nisan, offset consistency): in the induction step for n ≥ 3,
    once weights are independent of the fixed agent's valuation, the offsets are
    consistent up to a common additive constant: k(vi₀) a - k(vi₀) b does not depend
    on vi₀. Uses S-MON and no-veto to transfer the affine representation across
    different fixed valuations of i₀. -/
lemma offsets_consistent_of_fixed_agent
    (f : Valuation N A → A) (hsmon : IsSMon f)
    (i₀ : N) (hveto : ∀ i, i ≠ i₀ → HasNoVetoPower f i)
    (w : (A → Real) → N → Real) (k : (A → Real) → A → Real)
    (hrep : ∀ vi₀ : A → Real,
      (∀ i, 0 ≤ w vi₀ i) ∧
      (∀ v a, affineScore (w vi₀) (k vi₀) v (slice f i₀ vi₀ v) ≥
        affineScore (w vi₀) (k vi₀) v a))
    (hwind : ∀ vi₀ vi₀' i, i ≠ i₀ → w vi₀ i = w vi₀' i) :
    ∀ vi₀ vi₀' a b, k vi₀ a - k vi₀ b = k vi₀' a - k vi₀' b := by
  sorry

/-- Single-agent case (n = 1): DSIC + S-MON + onto implies affine maximizer.
    With a single agent, DSIC forces the choice function to maximize the agent's
    valuation (up to an irrelevant additive constant), i.e., an affine maximizer
    with positive weight on the sole agent. -/
lemma single_agent_affine_maximizer (M : Mechanism N A) (hdsic : IsDSIC M)
    (hsmon : IsSMon M.choiceFn) (honto : Function.Surjective M.choiceFn)
    (h1 : Fintype.card N = 1) :
    IsAffineMaximizer M.choiceFn := by
  sorry

/-- Induction auxiliary: strong induction on the number of agents.
    Every mechanism with at most n agents that is DSIC, S-MON, and onto
    (with |A| ≥ 3) has an affine-maximizer choice function.
    - n = 0 is vacuous (agents are nonempty).
    - n = 1 is the single-agent lemma.
    - n = 2 is Lemma 8 (via Lemma 4 to find the no-veto agent).
    - n ≥ 3 is the induction step: fix the possibly-veto agent's valuation,
      apply the IH to the slices, and assemble with Lemmas 9 and 10. -/
theorem dsic_smon_affine_aux (n : ℕ) :
    ∀ (N : Type*) [Fintype N] [Nonempty N] [DecidableEq N] (M : Mechanism N A),
    IsDSIC M → IsSMon M.choiceFn → Function.Surjective M.choiceFn →
    3 ≤ Fintype.card A → Fintype.card N ≤ n → IsAffineMaximizer M.choiceFn := by
  induction n with
  | zero =>
    intro N _ _ _ M hdsic hsmon honto hA hle
    have h1 : 1 ≤ Fintype.card N := Fintype.card_pos
    omega
  | succ k ih =>
    intro N _ _ _ M hdsic hsmon honto hA hle
    by_cases h1 : Fintype.card N = 1
    · exact single_agent_affine_maximizer M hdsic hsmon honto h1
    · by_cases h2 : Fintype.card N = 2
      · -- Two-agent case: Lemma 4 gives the no-veto agent; Lemma 8 concludes.
        classical
        obtain ⟨i₀, hnv⟩ := all_but_one_no_veto M.choiceFn hsmon honto hA
        have hex : ∃ i1 : N, i1 ≠ i₀ := by
          by_contra hcon
          have hall_eq : ∀ x : N, x = i₀ := by
            intro x
            by_contra hne
            exact hcon ⟨x, hne⟩
          have hcard1 : Fintype.card N = 1 := by
            rw [Fintype.card_eq_one_iff]
            exact ⟨i₀, hall_eq⟩
          omega
        obtain ⟨i1, hi1⟩ := hex
        have hnv1 : HasNoVetoPower M.choiceFn i1 := hnv i1 hi1
        have hall : ∀ i : N, i = i1 ∨ i = i₀ := by
          intro i
          by_cases hi : i = i1
          · exact Or.inl hi
          · right
            by_contra hne
            have h1ne : i1 ∉ ({i₀} : Finset N) := by
              simp only [Finset.mem_singleton]
              exact hi1
            have hine : i ∉ insert i1 ({i₀} : Finset N) := by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hi, hne⟩
            have h3 : ({i, i1, i₀} : Finset N).card = 3 := by
              rw [show ({i, i1, i₀} : Finset N) = insert i (insert i1 ({i₀} : Finset N))
                from rfl,
                Finset.card_insert_of_notMem hine,
                Finset.card_insert_of_notMem h1ne,
                Finset.card_singleton]
            have hle' : ({i, i1, i₀} : Finset N).card ≤ Fintype.card N :=
              Finset.card_le_univ _
            rw [h3, h2] at hle'
            omega
        exact two_agent_affine_maximizer M hdsic hsmon honto h2 i1 i₀ hi1 hall hnv1
      · -- n ≥ 3: fix the possibly-veto agent's valuation, apply the IH to the
        -- (n-1)-agent slices, then use Lemma 9 (weight independence) and
        -- Lemma 10 (offset consistency) to assemble an n-agent affine maximizer.
        sorry

/-- Main induction theorem (Dobzinski-Nisan, Lemmas 8-10): a DSIC mechanism whose
    choice function is S-MON and onto, with |A| ≥ 3, is an affine maximizer. -/
theorem dsic_smon_affine_maximizer (M : Mechanism N A) (hdsic : IsDSIC M)
    (hsmon : IsSMon M.choiceFn) (honto : Function.Surjective M.choiceFn)
    (hA : 3 ≤ Fintype.card A) :
    IsAffineMaximizer M.choiceFn :=
  dsic_smon_affine_aux (Fintype.card N) N M hdsic hsmon honto hA le_rfl

/-- Transfer (Lavi-Mu'alem-Nisan 2003): if the tie-broken choice function is an
    affine maximizer, so is the original choice function. Both f v and
    tieBreak f hwmon v lie in tieSet f v; the affine-maximizer property is about
    argmax membership, and tie-breaking does not move the outcome out of the
    affine-score argmax. -/
lemma affine_maximizer_transfer (f : Valuation N A → A) (hwmon : IsWMon f)
    (h : IsAffineMaximizer (tieBreak f hwmon)) : IsAffineMaximizer f := by
  sorry

/-- The tie-broken mechanism: tie-broken choice function with the original payments. -/
noncomputable def tieBreakMechanism (M : Mechanism N A) (hwmon : IsWMon M.choiceFn) :
    Mechanism N A :=
  { choiceFn := tieBreak M.choiceFn hwmon, pay := M.pay }

/-- Implementability preservation: tie-breaking a DSIC mechanism's choice function
    (via the simultaneous-perturbation tie-breaking) preserves DSIC. The payments
    are kept; truthfulness is unaffected because tie-breaking only re-selects among
    alternatives that the original rule treats as tied. -/
lemma tieBreakMechanism_dsic (M : Mechanism N A) (hdsic : IsDSIC M)
    (hwmon : IsWMon M.choiceFn) :
    IsDSIC (tieBreakMechanism M hwmon) := by
  sorry

/-- Onto preservation: tie-breaking an onto choice function keeps it onto.
    Every alternative in the range of f remains achievable after tie-breaking. -/
lemma tieBreakMechanism_onto (M : Mechanism N A) (hwmon : IsWMon M.choiceFn)
    (honto : Function.Surjective M.choiceFn) :
    Function.Surjective (tieBreakMechanism M hwmon).choiceFn := by
  sorry

/-- Roberts' theorem (M6 assembly): DSIC + onto implies affine maximizer.
    By the taxation principle DSIC gives W-MON; the S-MON reduction gives a
    strongly monotone tie-broken rule; the induction (Lemmas 8-10) shows the
    tie-broken rule is an affine maximizer; transfer gives it for the original. -/
theorem roberts_theorem (hA : 3 ≤ Fintype.card A)
    (M : Mechanism N A)
    (hdsic : IsDSIC M)
    (honto : Function.Surjective M.choiceFn) :
    IsAffineMaximizer M.choiceFn := by
  -- (a) DSIC gives W-MON (taxation principle).
  have hwmon : IsWMon M.choiceFn := wmon_of_dsic M hdsic
  -- (b) S-MON reduction: the tie-broken rule is S-MON.
  have hsmon : IsSMon (tieBreakMechanism M hwmon).choiceFn :=
    tieBreak_isSMon M.choiceFn hwmon
  -- (c) Induction (Lemmas 8-10): the tie-broken rule is an affine maximizer.
  have htb_dsic : IsDSIC (tieBreakMechanism M hwmon) :=
    tieBreakMechanism_dsic M hdsic hwmon
  have htb_onto : Function.Surjective (tieBreakMechanism M hwmon).choiceFn :=
    tieBreakMechanism_onto M hwmon honto
  have htb_am : IsAffineMaximizer (tieBreakMechanism M hwmon).choiceFn :=
    dsic_smon_affine_maximizer (tieBreakMechanism M hwmon) htb_dsic hsmon htb_onto hA
  -- (d) Transfer back to the original choice function.
  have h_eq : (tieBreakMechanism M hwmon).choiceFn = tieBreak M.choiceFn hwmon := rfl
  rw [h_eq] at htb_am
  exact affine_maximizer_transfer M.choiceFn hwmon htb_am

end

end Roberts
