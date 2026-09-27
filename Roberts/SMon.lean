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

/-- S-MON implies W-MON: the strict gap inequality gives the weak one. -/
lemma smon_implies_wmon (f : Valuation N A → A) (hsmon : IsSMon f) :
    IsWMon f := by
  intro i v vi vi2 a b hab h1 h2
  have h := hsmon i v vi vi2 a b hab h1 h2
  linarith

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
  classical
  induction s using Finset.induction with
  | empty =>
    have heq : (fun i a => v i a + (if i ∈ (∅ : Finset N) ∧ a = f v then ε else 0)) = v := by
      funext i a
      simp
    rw [heq]
  | insert x t hx ih =>
    -- Define w_t as the t-bumped valuation
    set w_t := fun i a => v i a + (if i ∈ t ∧ a = f v then ε else 0) with hw_t
    -- The (insert x t)-bumped valuation equals Function.update w_t x (bumped x-valuation)
    have heq : (fun i a => v i a + (if i ∈ insert x t ∧ a = f v then ε else 0))
        = Function.update w_t x (fun a => w_t x a + if a = f w_t then ε else 0) := by
      funext i a
      by_cases hi : i = x
      · -- Case i = x: use hi to rewrite, avoid subst
        rw [hi, Function.update_self]
        -- x ∉ t, so w_t x a = v x a
        have hwtx : w_t x a = v x a := by
          simp [hw_t, hx]
        rw [hwtx, ih]
        by_cases ha : a = f v
        · simp [ha, Finset.mem_insert_self, hi]
        · simp [ha, hi]
      · rw [Function.update_of_ne hi]
        simp [hw_t]
        by_cases hit : i ∈ t
        · by_cases ha : a = f v
          · simp [hit, ha, Finset.mem_insert_of_mem hit, hi]
          · simp [hit, ha, hi]
        · by_cases ha : a = f v
          · simp [Finset.mem_insert, hi, hit, ha] at *
          · simp [hit, ha, hi]
    rw [heq]
    -- Apply bump_winner_stable: f (update w_t x (bumped)) = f w_t = f v (by ih)
    have h_bump := bump_winner_stable f hwmon w_t x ε hε
    rw [h_bump, ih]


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

/-- Bump-interpolation chain: y-bump on S, x-bump off S, base valuation `base`.
    Used in the proof of `key_lemma` to interpolate between an x-perturbation
    (S = empty) and a y-perturbation (S = univ) one agent at a time. -/
private def bumpChain (base : Valuation N A) (x y : A) (ε : Real) (S : Finset N) :
    Valuation N A :=
  fun j a => base j a + if (j ∈ S ∧ a = y) ∨ (j ∉ S ∧ a = x) then ε else 0

omit [Fintype N] [Fintype A] [Nonempty N] [Nonempty A] in
/-- The chain at S ∪ {j} agrees with the chain at S off of j. -/
private lemma bumpChain_update (base : Valuation N A) (x y : A) (ε : Real)
    (S : Finset N) (j : N) (hj : j ∉ S) :
    bumpChain base x y ε (insert j S)
      = Function.update (bumpChain base x y ε S) j
        ((bumpChain base x y ε (insert j S)) j) := by
  funext k
  by_cases hkj : k = j
  · subst hkj; simp
  · rw [Function.update_of_ne hkj]
    funext a
    simp only [bumpChain]
    have hiff : ((k ∈ insert j S ∧ a = y) ∨ (k ∉ insert j S ∧ a = x)) ↔
        ((k ∈ S ∧ a = y) ∨ (k ∉ S ∧ a = x)) := by
      have hmem : (k ∈ insert j S) ↔ (k ∈ S) := by simp [hkj]
      have hnmem : (k ∉ insert j S) ↔ (k ∉ S) := by simp [hkj]
      tauto
    simp only [hiff]

omit [Fintype N] [Fintype A] [Nonempty N] [Nonempty A] in
/-- y is a sink along the chain: once y wins, it keeps winning.
    Proof: W-MON at the transitioning agent; the y-bump strictly increases
    y's advantage, giving a clean contradiction from `0 < ε`. -/
private lemma chain_y_sink (f : Valuation N A → A) (hwmon : IsWMon f)
    (base : Valuation N A) (x y : A) (hxy : x ≠ y) (ε : Real) (hε : 0 < ε)
    (S : Finset N) (j : N) (hj : j ∉ S)
    (hwin : f (bumpChain base x y ε S) = y) :
    f (bumpChain base x y ε (insert j S)) = y := by
  classical
  by_contra hne
  have hupd := bumpChain_update base x y ε S j hj
  generalize hb : f (bumpChain base x y ε (insert j S)) = b
  have hby : y ≠ b := by rw [← hb]; exact fun h => hne h.symm
  have hfirst : f (Function.update (bumpChain base x y ε S) j
      ((bumpChain base x y ε S) j)) = y := by
    have hself : Function.update (bumpChain base x y ε S) j
        ((bumpChain base x y ε S) j) = bumpChain base x y ε S := by
      funext k a
      by_cases hkj : k = j
      · subst hkj; simp
      · rw [Function.update_of_ne hkj]
    rw [hself]; exact hwin
  have hsecond : f (Function.update (bumpChain base x y ε S) j
      ((bumpChain base x y ε (insert j S)) j)) = b := by
    rw [← hupd, hb]
  have hmon := hwmon j (bumpChain base x y ε S)
    ((bumpChain base x y ε S) j)
    ((bumpChain base x y ε (insert j S)) j) y b hby hfirst hsecond
  have e1 : ((bumpChain base x y ε S) j) y = base j y := by
    show base j y + (if (j ∈ S ∧ y = y) ∨ (j ∉ S ∧ y = x) then ε else 0) = _
    have hneg : ¬ ((j ∈ S ∧ y = y) ∨ (j ∉ S ∧ y = x)) := by
      rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · exact hj h1
      · exact hxy h2.symm
    rw [if_neg hneg, add_zero]
  have e2 : ((bumpChain base x y ε S) j) b = base j b + if b = x then ε else 0 := by
    show base j b + (if (j ∈ S ∧ b = y) ∨ (j ∉ S ∧ b = x) then ε else 0) = _
    have hiff : ((j ∈ S ∧ b = y) ∨ (j ∉ S ∧ b = x)) ↔ (b = x) := by
      simp [hj]
    simp only [hiff]
  have e3 : ((bumpChain base x y ε (insert j S)) j) y = base j y + ε := by
    show base j y + (if (j ∈ insert j S ∧ y = y) ∨ (j ∉ insert j S ∧ y = x) then ε else 0) = _
    have htrue : ((j ∈ insert j S ∧ y = y) ∨ (j ∉ insert j S ∧ y = x)) :=
      Or.inl ⟨by simp, rfl⟩
    rw [if_pos htrue]
  have e4 : ((bumpChain base x y ε (insert j S)) j) b
      = base j b + if b = y then ε else 0 := by
    show base j b + (if (j ∈ insert j S ∧ b = y) ∨ (j ∉ insert j S ∧ b = x) then ε else 0) = _
    have hiff : ((j ∈ insert j S ∧ b = y) ∨ (j ∉ insert j S ∧ b = x)) ↔ (b = y) := by
      constructor
      · rintro (⟨_, h2⟩ | ⟨h1, _⟩)
        · exact h2
        · exact absurd (Finset.mem_insert_self j S) h1
      · intro h
        exact Or.inl ⟨Finset.mem_insert_self j S, h⟩
    simp only [hiff]
  rw [e1, e2, e3, e4] at hmon
  by_cases hbx : b = x
  · have hbny : b ≠ y := by rw [hbx]; exact hxy
    have e5 : (if b = x then (ε : Real) else 0) = ε := by simp [hbx]
    have e6 : (if b = y then (ε : Real) else 0) = 0 := by simp [hbny]
    rw [e5, e6] at hmon
    linarith [hε]
  · have hbny : b ≠ y := Ne.symm hby
    have e5 : (if b = x then (ε : Real) else 0) = 0 := by simp [hbx]
    have e6 : (if b = y then (ε : Real) else 0) = 0 := by simp [hbny]
    rw [e5, e6] at hmon
    linarith [hε]

omit [Fintype N] [Fintype A] [Nonempty N] [Nonempty A] in
/-- x is a source along the chain: x cannot be entered.
    Proof: W-MON at the transitioning agent; entering x would require
    overcoming the strictly positive bump disadvantage. -/
private lemma chain_x_source (f : Valuation N A → A) (hwmon : IsWMon f)
    (base : Valuation N A) (x y : A) (hxy : x ≠ y) (ε : Real) (hε : 0 < ε)
    (S : Finset N) (j : N) (hj : j ∉ S)
    (hwin : f (bumpChain base x y ε (insert j S)) = x) :
    f (bumpChain base x y ε S) = x := by
  classical
  by_contra hne
  have hupd := bumpChain_update base x y ε S j hj
  generalize hb : f (bumpChain base x y ε S) = b
  have hbx : b ≠ x := by rw [← hb]; exact hne
  -- W-MON with a := x at the insert profile, b := b at the S profile.
  have hfirst : f (Function.update (bumpChain base x y ε S) j
      ((bumpChain base x y ε (insert j S)) j)) = x := by
    rw [← hupd]; exact hwin
  have hsecond : f (Function.update (bumpChain base x y ε S) j
      ((bumpChain base x y ε S) j)) = b := by
    have hself : Function.update (bumpChain base x y ε S) j
        ((bumpChain base x y ε S) j) = bumpChain base x y ε S := by
      funext k a
      by_cases hkj : k = j
      · subst hkj; simp
      · rw [Function.update_of_ne hkj]
    rw [hself, hb]
  have hmon := hwmon j (bumpChain base x y ε S)
    ((bumpChain base x y ε (insert j S)) j)
    ((bumpChain base x y ε S) j) x b (Ne.symm hbx) hfirst hsecond
  have e1 : ((bumpChain base x y ε (insert j S)) j) x = base j x := by
    show base j x + (if (j ∈ insert j S ∧ x = y) ∨ (j ∉ insert j S ∧ x = x) then ε else 0) = _
    have hneg : ¬ ((j ∈ insert j S ∧ x = y) ∨ (j ∉ insert j S ∧ x = x)) := by
      rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
      · exact hxy h2
      · simp at h1
    rw [if_neg hneg, add_zero]
  have e2 : ((bumpChain base x y ε (insert j S)) j) b
      = base j b + if b = y then ε else 0 := by
    show base j b + (if (j ∈ insert j S ∧ b = y) ∨ (j ∉ insert j S ∧ b = x) then ε else 0) = _
    have hiff : ((j ∈ insert j S ∧ b = y) ∨ (j ∉ insert j S ∧ b = x)) ↔ (b = y) := by
      constructor
      · rintro (⟨_, h2⟩ | ⟨h1, _⟩)
        · exact h2
        · exact absurd (Finset.mem_insert_self j S) h1
      · intro h
        exact Or.inl ⟨Finset.mem_insert_self j S, h⟩
    simp only [hiff]
  have e3 : ((bumpChain base x y ε S) j) x = base j x + ε := by
    show base j x + (if (j ∈ S ∧ x = y) ∨ (j ∉ S ∧ x = x) then ε else 0) = _
    have htrue : ((j ∈ S ∧ x = y) ∨ (j ∉ S ∧ x = x)) := Or.inr ⟨hj, rfl⟩
    rw [if_pos htrue]
  have e4 : ((bumpChain base x y ε S) j) b = base j b + if b = x then ε else 0 := by
    show base j b + (if (j ∈ S ∧ b = y) ∨ (j ∉ S ∧ b = x) then ε else 0) = _
    have hiff : ((j ∈ S ∧ b = y) ∨ (j ∉ S ∧ b = x)) ↔ (b = x) := by
      simp [hj]
    simp only [hiff]
  rw [e1, e2, e3, e4] at hmon
  -- hmon : (base j x - (base j b + (if b=y then ε else 0))) ≥
  --        ((base j x + ε) - (base j b + (if b=x then ε else 0)))
  -- i.e., (if b=x then ε else 0) - (if b=y then ε else 0) ≥ ε.
  have key : (if b = x then (ε : Real) else 0) - (if b = y then (ε : Real) else 0) ≥ ε := by
    linarith
  by_cases hby : b = y
  · have e5 : (if b = x then (ε : Real) else 0) = 0 := by simp [hbx]
    have e6 : (if b = y then (ε : Real) else 0) = ε := by simp [hby]
    rw [e5, e6] at key
    linarith [hε]
  · have e5 : (if b = x then (ε : Real) else 0) = 0 := by simp [hbx]
    have e6 : (if b = y then (ε : Real) else 0) = 0 := by simp [hby]
    rw [e5, e6] at key
    linarith [hε]

omit [Fintype A] [DecidableEq A] [Nonempty N] [Nonempty A] in
private lemma outcome_mem_of_gap_increase
    (f : Valuation N A → A) (hwmon : IsWMon f)
    (v w : Valuation N A) (P : A → Prop)
    (hstart : P (f v))
    (hgap : ∀ j, v j = w j ∨
      ∀ a b, P a → ¬ P b → v j a - v j b < w j a - w j b) :
    P (f w) := by
  classical
  let D : Finset N := Finset.univ.filter fun j => v j ≠ w j
  let mid : Finset N → Valuation N A := fun s j => if j ∈ s then w j else v j
  have hsmall : ∀ s : Finset N, s ⊆ D → P (f (mid s)) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro _
        simpa [mid] using hstart
    | @insert j s hj ih =>
        intro hs
        have hjD : j ∈ D := hs (by simp)
        have hsD : s ⊆ D := by
          intro k hk
          exact hs (by simp [hk])
        have htrans : mid (insert j s) = Function.update (mid s) j (w j) := by
          funext k a
          by_cases hkj : k = j
          · subst k
            simp [mid]
          · simp [mid, hkj]
        have hself : Function.update (mid s) j (mid s j) = mid s := by
          funext k a
          by_cases hkj : k = j
          · subst k
            simp
          · simp [hkj]
        let a := f (mid s)
        let b := f (mid (insert j s))
        have ha : P a := ih hsD
        by_cases hb : P b
        · exact hb
        · have hab : a ≠ b := by
            intro heq
            apply hb
            rw [← heq]
            exact ha
          have hfirst : f (Function.update (mid s) j (mid s j)) = a := by
            rw [hself]
          have hsecond : f (Function.update (mid s) j (w j)) = b := by
            rw [← htrans]
          have hmon := hwmon j (mid s) (mid s j) (w j) a b hab hfirst hsecond
          have hjne : v j ≠ w j := by
            simpa [D] using hjD
          have hgapj := hgap j
          rcases hgapj with heq | hgapj
          · exact (hjne heq).elim
          · have hmidj : mid s j = v j := by simp [mid, hj]
            have hstrict := hgapj a b ha hb
            rw [hmidj] at hmon
            linarith
  have hres := hsmall D (by intro j hj; exact hj)
  have hmidD : mid D = w := by
    funext j a
    by_cases hj : j ∈ D
    · simp [mid, hj]
    · have hEq : v j = w j := by
        by_contra hne
        apply hj
        simp [D, hne]
      simp [mid, hj, hEq]
  simpa [hmidD] using hres

/-- Key lemma (Lavi-Mu'alem-Nisan 2003, Theorem 2): the tie set is monotone
    in the single-agent valuation with respect to pairwise differences.
    If x is tied at v, y is tied at v', and i's (x-y) gap weakly increases
    from v to v', then x is tied at v'. -/
lemma key_lemma (f : Valuation N A → A) (hwmon : IsWMon f)
    (i : N) (v v' : Valuation N A)
    (hsingle : ∀ j, j ≠ i → v j = v' j)
    (x y : A) (hx : x ∈ tieSet f v) (hy : y ∈ tieSet f v')
    (h : v' i x - v' i y ≥ v i x - v i y) :
    x ∈ tieSet f v' := by
  classical
  by_cases hxy : x = y
  · subst y
    exact hy
  have hx' : ∃ δ > 0, ∀ ε ∈ Set.Ioo (0 : Real) δ,
      f (perturb v x ε) = x := by
    simpa [tieSet] using hx
  have hy' : ∃ δ > 0, ∀ ε ∈ Set.Ioo (0 : Real) δ,
      f (perturb v' y ε) = y := by
    simpa [tieSet] using hy
  obtain ⟨δx, hδx, hxprop⟩ := hx'
  obtain ⟨δy, hδy, hyprop⟩ := hy'
  let δ := min δx δy
  change x ∈ Finset.univ.filter (fun a =>
    ∃ d > 0, ∀ ε ∈ Set.Ioo (0 : Real) d, f (perturb v' a ε) = a)
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  refine ⟨δ, ?_, ?_⟩
  · dsimp [δ]
    exact lt_min hδx hδy
  · intro ε hε
    let t : Real := ε / 5
    have hεpos : 0 < ε := hε.1
    have ht : 0 < t := by
      dsimp [t]
      positivity
    have hεx : ε < δx := lt_of_lt_of_le hε.2 (min_le_left δx δy)
    have hεy : ε < δy := lt_of_lt_of_le hε.2 (min_le_right δx δy)
    have htx : t ∈ Set.Ioo (0 : Real) δx := by
      simp only [Set.mem_Ioo]
      constructor
      · exact ht
      · dsimp [t]
        linarith
    have hty : t ∈ Set.Ioo (0 : Real) δy := by
      simp only [Set.mem_Ioo]
      constructor
      · exact ht
      · dsimp [t]
        linarith
    have hpwin : f (perturb v x t) = x := hxprop t htx
    have hywin : f (perturb v' y t) = y := hyprop t hty
    have hyx : y ≠ x := by
      intro hEq
      exact hxy hEq.symm
    let p : Valuation N A := perturb v x t
    let q : Valuation N A := fun j a =>
      v' j a + (if a = x then 4 * t else 0) + (if a = y then 2 * t else 0)
    let r : Valuation N A := Function.update q i (p i)
    let s : Valuation N A := perturb v' y t
    let final : Valuation N A := perturb v' x (5 * t)
    have hgap1 : ∀ j, p j = r j ∨
        ∀ a b, a = x → ¬ b = x → p j a - p j b < r j a - r j b := by
      intro j
      by_cases hji : j = i
      · left
        simp [r, hji]
      · right
        intro a b ha hb
        subst a
        have hbase := hsingle j hji
        by_cases hby : b = y
        · subst b
          simp [p, q, r, perturb, hji, hbase, hxy, hyx]
          linarith
        · have hbx : b ≠ x := by
            intro heq
            exact hb heq
          simp [p, q, r, perturb, hji, hbase, hxy, hby, hbx]
          linarith
    have hrmem := outcome_mem_of_gap_increase f hwmon p r (fun a => a = x)
      (by simpa [hpwin]) hgap1
    have hrwin : f r = x := by simpa using hrmem
    have hgap2 : ∀ j, s j = q j ∨
        ∀ a b, (a = x ∨ a = y) → ¬ (b = x ∨ b = y) →
          s j a - s j b < q j a - q j b := by
      intro j
      right
      intro a b ha hb
      rcases ha with hax | hay
      · subst a
        have hbx : b ≠ x := by
          intro heq
          exact hb (Or.inl heq)
        have hby : b ≠ y := by
          intro heq
          exact hb (Or.inr heq)
        simp [s, q, perturb, hxy, hbx, hby]
        linarith
      · subst a
        have hbx : b ≠ x := by
          intro heq
          exact hb (Or.inl heq)
        have hby : b ≠ y := by
          intro heq
          exact hb (Or.inr heq)
        simp [s, q, perturb, hyx, hbx, hby]
        linarith
    have hqmem := outcome_mem_of_gap_increase f hwmon s q
      (fun a => a = x ∨ a = y) (by simp [s, hywin, hyx]) hgap2
    have hqcases : f q = x ∨ f q = y := by simpa using hqmem
    have hqwin : f q = x := by
      rcases hqcases with hqx | hqy
      · exact hqx
      · have hri : r i = p i := by simp [r]
        have hrform : Function.update q i (r i) = r := by
          rw [hri]
        have hqself : Function.update q i (q i) = q := by
          funext j a
          by_cases hji : j = i
          · subst j
            simp
          · simp [hji]
        have hfirst : f (Function.update q i (r i)) = x := by
          rw [hrform]
          exact hrwin
        have hsecond : f (Function.update q i (q i)) = y := by
          rw [hqself]
          exact hqy
        have hmon := hwmon i q (r i) (q i) x y hxy hfirst hsecond
        have hpGap : p i x - p i y =
            (v i x - v i y) + t := by
          simp [p, perturb, hyx]
          linarith
        have hqGap : q i x - q i y =
            (v' i x - v' i y) + 2 * t := by
          simp [q, hxy, hyx]
          linarith
        rw [hri, hpGap, hqGap] at hmon
        linarith
    have hgap4 : ∀ j, q j = final j ∨
        ∀ a b, a = x → ¬ b = x → q j a - q j b < final j a - final j b := by
      intro j
      right
      intro a b ha hb
      subst a
      have hbx : b ≠ x := by
        intro heq
        exact hb heq
      by_cases hby : b = y
      · subst b
        simp [q, final, perturb, hxy, hyx]
        linarith
      · simp [q, final, perturb, hxy, hbx, hby]
        linarith
    have hfinalmem := outcome_mem_of_gap_increase f hwmon q final
      (fun a => a = x) (by simp [hqwin]) hgap4
    have hfinalwin : f final = x := by simpa using hfinalmem
    have hfinaleq : final = perturb v' x ε := by
      funext j a
      simp [final, perturb, t]
      by_cases hax : a = x
      · simp [hax]
        linarith
      · simp [hax]
    rw [← hfinaleq]
    exact hfinalwin


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
