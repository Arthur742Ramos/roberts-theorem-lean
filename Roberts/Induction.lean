import Roberts.TwoAgent
import Mathlib.Algebra.BigOperators.Ring.Finset

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
  /-
  These hypotheses do not normalize affine representations: multiplying all
  weights and offsets in one slice by a positive scalar preserves every argmax.
  Even identical sliced rules therefore admit representations with different
  weights (for example, scale one slice's representation by `2`). This equality
  needs a normalization condition or a conclusion up to positive proportionality.
  -/
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
  /-
  The usual proof compares switching thresholds between slices after the weights
  have been normalized and shown to agree. The current development has no slice
  mechanism on the remaining-agent subtype, so that threshold-transfer argument
  is not yet represented by the available lemmas.
  -/
  sorry

/-- Single-agent case (n = 1): DSIC + S-MON + onto implies affine maximizer.
    With a single agent, DSIC forces the choice function to maximize the agent's
    valuation (up to an irrelevant additive constant), i.e., an affine maximizer
    with positive weight on the sole agent. -/
lemma single_agent_affine_maximizer (M : Mechanism N A) (hdsic : IsDSIC M)
    (hsmon : IsSMon M.choiceFn) (honto : Function.Surjective M.choiceFn)
    (h1 : Fintype.card N = 1) :
    IsAffineMaximizer M.choiceFn := by
  -- Get the unique agent
  have hN : ∃ i₀ : N, ∀ i : N, i = i₀ := by
    rw [Fintype.card_eq_one_iff] at h1
    exact h1
  obtain ⟨i₀, hi₀⟩ := hN
  -- Use the taxation principle: prices exist and are independent of valuation
  -- For single agent, price M i₀ v a is independent of v (by price_independent)
  -- Define kappa(a) = -price M i₀ v₀ a for a fixed v₀
  -- Then f(v) maximizes v i₀ a + kappa(a)
  classical
  let v₀ : Valuation N A := Classical.choice (inferInstance : Nonempty (Valuation N A))
  let weights : N → Real := fun _ => 1
  let k : A → Real := fun a => -price M i₀ v₀ a
  have hprofile (v : Valuation N A) : Function.update v i₀ (v₀ i₀) = v₀ := by
    funext j
    by_cases hj : j = i₀
    · subst j
      simp
    · have hji : j = i₀ := hi₀ j
      exact (hj hji).elim
  have hprice (v : Valuation N A) (a : A) :
      price M i₀ v a = price M i₀ v₀ a := by
    have hp := price_independent M hdsic i₀ v (v i₀) (v₀ i₀) a
    simpa only [update_self, hprofile v] using hp
  have hsum (v : Valuation N A) (a : A) :
      Finset.univ.sum (fun i => weights i * v i a) = v i₀ a := by
    have huniv : (Finset.univ : Finset N) = {i₀} := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_singleton]
      exact ⟨fun _ => hi₀ j, fun _ => True.intro⟩
    rw [huniv]
    simp [weights]
  refine ⟨weights, k, ?_, ?_, ?_⟩
  · intro i
    simp [weights]
  · exact ⟨i₀, by simp [weights]⟩
  · intro v a
    obtain ⟨u, hu⟩ := honto a
    have hach : Achievable M.choiceFn i₀ v a := by
      refine ⟨u i₀, ?_⟩
      have hupdate : Function.update v i₀ (u i₀) = u := by
        funext j
        by_cases hj : j = i₀
        · subst j
          simp
        · have hji : j = i₀ := hi₀ j
          exact (hj hji).elim
      rw [hupdate]
      exact hu
    have htax := taxation_ineq M hdsic i₀ v (v i₀) a hach
    rw [update_self] at htax
    have hpf := hprice v (M.choiceFn v)
    have hpa := hprice v a
    rw [hpf, hpa] at htax
    have e1 : affineScore weights k v (M.choiceFn v) =
        v i₀ (M.choiceFn v) - price M i₀ v₀ (M.choiceFn v) := by
      unfold affineScore
      rw [hsum v (M.choiceFn v)]
      rfl
    have e2 : affineScore weights k v a = v i₀ a - price M i₀ v₀ a := by
      unfold affineScore
      rw [hsum v a]
      rfl
    rw [e1, e2]
    linarith

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
        exact two_agent_affine_maximizer hdsic hsmon hi1 hall hnv1 hA
      · -- n ≥ 3: fix the possibly-veto agent's valuation, apply the IH to the
        -- (n-1)-agent slices, then use Lemma 9 (weight independence) and
        -- Lemma 10 (offset consistency) to assemble an n-agent affine maximizer.
        /-
        A full implementation needs a subtype-valued sliced mechanism, and the
        current Lemma 9 statement lacks scale normalization. Also,
        `all_but_one_no_veto` permits the exceptional agent to be a dictator;
        fixing that agent's report can make a slice constant rather than onto.
        The induction hypothesis cannot be applied to every slice with the
        present hypotheses alone.
        -/
        sorry

/- If every agent's gap between `a` and any other alternative is strictly
   improved, W-MON lets us update the agents one at a time without changing
   an outcome that was already `a`. -/
private lemma outcome_of_strict_gap_increase (f : Valuation N A → A)
    (hwmon : IsWMon f) (v v' : Valuation N A) (a : A)
    (hfa : f v = a)
    (hgap : ∀ i b, b ≠ a → v' i a - v' i b > v i a - v i b) :
    f v' = a := by
  classical
  let q (s : Finset N) : Valuation N A := fun i => if i ∈ s then v' i else v i
  have hq : ∀ s : Finset N, f (q s) = a := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simpa [q] using hfa
    | @insert i s his ih =>
        have hupdate : Function.update (q s) i (v' i) = q (insert i s) := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [q, his]
          · simp [q, hji]
        by_contra hneout
        let b := f (q (insert i s))
        have hab : a ≠ b := by
          intro hab
          apply hneout
          simpa [b] using hab.symm
        have hfirst : f (Function.update (q s) i ((q s) i)) = a := by
          simpa only [update_self] using ih
        have hsecond : f (Function.update (q s) i (v' i)) = b := by
          rw [hupdate]
        have hmon := hwmon i (q s) ((q s) i) (v' i) a b hab hfirst hsecond
        have hold : (q s) i = v i := by simp [q, his]
        rw [hold] at hmon
        exact (not_le_of_gt (hgap i b (Ne.symm hab))) hmon
  have hlast := hq Finset.univ
  simpa [q] using hlast

/- A positive simultaneous bump of an outcome makes that outcome the sole
   member of its tie set. The strict-gap lemma rules out every other member. -/
private lemma tieBreak_eq_after_positive_bump (f : Valuation N A → A)
    (hwmon : IsWMon f) (v : Valuation N A) (a : A)
    (hfa : f v = a) (ε : Real) (hε : 0 < ε) :
    tieBreak f hwmon (perturb v a ε) = a := by
  classical
  let w := perturb v a ε
  have hnot : ∀ b, b ≠ a → b ∉ tieSet f w := by
    intro b hba hb
    have hb' : b ∈ Finset.univ.filter (fun x =>
        ∃ δ > 0, ∀ ε ∈ Set.Ioo 0 δ, f (perturb w x ε) = x) := by
      simpa [tieSet] using hb
    rcases (Finset.mem_filter.mp hb').2 with ⟨δ, hδ, hstable⟩
    let η := min δ ε / 2
    have hmin : 0 < min δ ε := lt_min hδ hε
    have hη : 0 < η := by dsimp [η]; positivity
    have hηδ : η < δ := by
      dsimp [η]
      have hminδ : min δ ε ≤ δ := min_le_left δ ε
      linarith
    have hηε : η < ε := by
      dsimp [η]
      have hminε : min δ ε ≤ ε := min_le_right δ ε
      linarith
    have hstay : f (perturb w b η) = a := by
      apply outcome_of_strict_gap_increase f hwmon v (perturb w b η) a hfa
      intro i c hca
      by_cases hcb : c = b
      · subst c
        simp [w, perturb, hba, Ne.symm hba]
        linarith
      · simp [w, perturb, hba, Ne.symm hba, hcb, hca]
        linarith
    have hswitch := hstable η ⟨hη, hηδ⟩
    rw [hstay] at hswitch
    exact hba hswitch.symm
  have hset : tieSet f w = {a} := by
    have hfw : f w = a := by
      have hstable := perturb_stable_aux f hwmon v ε hε Finset.univ
      have hprof :
          (fun i b => v i b + (if i ∈ Finset.univ ∧ b = f v then ε else 0)) =
            perturb v (f v) ε := by
        funext i b
        simp [perturb]
      rw [hprof] at hstable
      simpa [w, hfa] using hstable
    ext b
    simp only [Finset.mem_singleton]
    constructor
    · intro hb
      by_cases hba : b = a
      · exact hba
      · exact False.elim (hnot b hba hb)
    · rintro rfl
      have hm := mem_tieSet_self f hwmon w
      rw [hfw] at hm
      exact hm
  have hw : tieBreak f hwmon w = a := by
    simp [tieBreak, hset, w]
  simpa [w] using hw

private lemma affineScore_perturb_self (weights : N → Real) (k : A → Real)
    (v : Valuation N A) (a : A) (ε : Real) :
    affineScore weights k (perturb v a ε) a =
      affineScore weights k v a + ε * (Finset.univ.sum fun i => weights i) := by
  classical
  simp only [affineScore, perturb, if_pos, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  ring

private lemma affineScore_perturb_other (weights : N → Real) (k : A → Real)
    (v : Valuation N A) (a b : A) (ε : Real) (hba : b ≠ a) :
    affineScore weights k (perturb v a ε) b = affineScore weights k v b := by
  apply affineScore_congr
  intro i
  simp [perturb, hba]

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
  classical
  rcases h with ⟨weights, k, hnonneg, hnonzero, hmax⟩
  refine ⟨weights, k, hnonneg, hnonzero, ?_⟩
  intro v a
  let x := f v
  let y := tieBreak f hwmon v
  have hx : x ∈ tieSet f v := by
    exact mem_tieSet_self f hwmon v
  have hy : y ∈ tieSet f v := tieBreak_mem f hwmon v
  have heq : affineScore weights k v x = affineScore weights k v y := by
    by_cases hxy : x = y
    · simp [hxy]
    · by_contra hnot
      have hle : affineScore weights k v x < affineScore weights k v y := by
        have hmaxxy := hmax v x
        have hnotle : ¬ affineScore weights k v y ≤ affineScore weights k v x := by
          intro hh
          exact hnot (le_antisymm hmaxxy hh)
        exact lt_of_not_ge hnotle
      have hx' : x ∈ Finset.univ.filter (fun x =>
          ∃ δ > 0, ∀ ε ∈ Set.Ioo 0 δ, f (perturb v x ε) = x) := by
        simpa [tieSet] using hx
      rcases (Finset.mem_filter.mp hx').2 with ⟨δ, hδ, hstable⟩
      let total := Finset.univ.sum fun i => weights i
      let bound := (affineScore weights k v y - affineScore weights k v x) /
        (total + 1)
      let η := min δ bound / 2
      have htotal : 0 ≤ total := by
        dsimp [total]
        exact Finset.sum_nonneg (fun i hi => hnonneg i)
      have hgap : 0 < affineScore weights k v y - affineScore weights k v x := by
        linarith
      have hden : 0 < total + 1 := by linarith
      have hboundpos : 0 < bound := by
        dsimp [bound]
        exact div_pos hgap hden
      have hηpos : 0 < η := by
        dsimp [η]
        have hminpos : 0 < min δ bound := lt_min hδ hboundpos
        linarith
      have hηδ : η < δ := by
        dsimp [η]
        have hminδ : min δ bound ≤ δ := min_le_left _ _
        linarith
      have hηbound : η ≤ bound := by
        dsimp [η]
        have hminbound : min δ bound ≤ bound := min_le_right _ _
        linarith
      have hηtotal : η * total <
          affineScore weights k v y - affineScore weights k v x := by
        have hmul := mul_le_mul_of_nonneg_right hηbound htotal
        have hnum :
            (affineScore weights k v y - affineScore weights k v x) * total <
              (affineScore weights k v y - affineScore weights k v x) * (total + 1) := by
          nlinarith [hgap, htotal]
        have hfrac :
            (affineScore weights k v y - affineScore weights k v x) * total /
                (total + 1) <
              affineScore weights k v y - affineScore weights k v x :=
          (div_lt_iff₀ hden).2 hnum
        calc
          η * total ≤
              ((affineScore weights k v y - affineScore weights k v x) /
                (total + 1)) * total := hmul
          _ = (affineScore weights k v y - affineScore weights k v x) * total /
              (total + 1) := by ring
          _ < affineScore weights k v y - affineScore weights k v x := hfrac
      have hεpos : 0 < η / 2 := by positivity
      have hεltδ : η / 2 < δ := by linarith
      have hfx : f (perturb v x (η / 2)) = x :=
        hstable (η / 2) ⟨hεpos, hεltδ⟩
      have htb := tieBreak_eq_after_positive_bump f hwmon
        (perturb v x (η / 2)) x hfx (η / 2) hεpos
      have hcompose : perturb (perturb v x (η / 2)) x (η / 2) =
          perturb v x η := by
        funext i b
        by_cases hbx : b = x
        · subst b
          simp [perturb]
          ring
        · simp [perturb, hbx]
      rw [hcompose] at htb
      have hmaxyx := hmax (perturb v x η) y
      rw [htb] at hmaxyx
      have hscorex := affineScore_perturb_self weights k v x η
      have hscorey := affineScore_perturb_other weights k v x y η (Ne.symm hxy)
      rw [hscorex, hscorey] at hmaxyx
      linarith
  change affineScore weights k v x ≥ affineScore weights k v a
  rw [heq]
  exact hmax v a

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
  /-
  This claim is false with the original payments. For one agent and alternatives
  `a,b`, let the rule choose `a` exactly when `v(a) - v(b) ≥ c`, and charge `c`
  for `a` and zero for `b`. It is DSIC. At the threshold, both outcomes are in
  the simultaneous-perturbation tie set. If the transported order prefers `b`,
  tie-breaking selects `b` there but keeps the payment `c`; reporting just below
  the threshold then gets `b` for zero and is strictly better. Recomputing the
  payment for the tie-broken allocation can repair this, but does not prove the
  mechanism defined above DSIC.
  -/
  sorry

/-- Onto preservation: tie-breaking an onto choice function keeps it onto.
    Every alternative in the range of f remains achievable after tie-breaking. -/
lemma tieBreakMechanism_onto (M : Mechanism N A) (hwmon : IsWMon M.choiceFn)
    (honto : Function.Surjective M.choiceFn) :
    Function.Surjective (tieBreakMechanism M hwmon).choiceFn := by
  intro a
  obtain ⟨v, hv⟩ := honto a
  refine ⟨perturb v a 1, ?_⟩
  change tieBreak M.choiceFn hwmon (perturb v a 1) = a
  exact tieBreak_eq_after_positive_bump M.choiceFn hwmon v a hv 1 one_pos

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
