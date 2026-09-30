module

public import Roberts.SMon
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Roberts

section

variable {N A : Type*} [Fintype N] [Fintype A] [DecidableEq N] [DecidableEq A]
  [Nonempty N] [Nonempty A]

@[expose] public noncomputable def range (f : Valuation N A → A) (i : N) (vi : A → Real) : Finset A := by
  classical
  exact Finset.univ.filter (fun a => ∃ v : Valuation N A, f (Function.update v i vi) = a)

@[expose] public def HasNoVetoPower (f : Valuation N A → A) (i : N) : Prop :=
  ∀ vi : A → Real, range f i vi = Finset.univ

@[expose] public def IsDictatable (R : (A → Real) → Finset A) (a : A) : Prop :=
  ∃ vi : A → Real, R vi = {a}

public lemma range_nonempty (f : Valuation N A → A) (i : N) (vi : A → Real) :
    (range f i vi).Nonempty := by
  classical
  let v : Valuation N A := fun _ _ => 0
  let a : A := f (Function.update v i vi)
  refine ⟨a, ?_⟩
  unfold range
  simp only [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, ⟨v, rfl⟩⟩

public lemma range_monotone (f : Valuation N A → A) (hsmon : IsSMon f) (i : N)
    (vi vi2 : A → Real) (a : A) (ha : a ∈ range f i vi)
    (h : ∀ b, vi2 a - vi2 b ≥ vi a - vi b) : a ∈ range f i vi2 := by
  classical
  rcases (Finset.mem_filter.mp ha).2 with ⟨v, hv⟩
  by_contra hmem
  let b := f (Function.update v i vi2)
  have hbmem : b ∈ range f i vi2 := by
    unfold range
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨v, rfl⟩⟩
  have hab : a ≠ b := by
    intro heq
    apply hmem
    rw [heq]
    exact hbmem
  have hstrict := hsmon i v vi vi2 a b hab hv rfl
  have hweak := h b
  linarith

public lemma range_iia (f : Valuation N A → A) (hsmon : IsSMon f) (i : N)
    (vi vi2 : A → Real) (a : A) (h : ∀ b, vi a - vi b = vi2 a - vi2 b) :
    (a ∈ range f i vi ↔ a ∈ range f i vi2) := by
  constructor
  · intro ha
    exact range_monotone f hsmon i vi vi2 a ha (fun b => le_of_eq (h b))
  · intro ha
    exact range_monotone f hsmon i vi2 vi a ha (fun b => le_of_eq (h b).symm)

@[expose] public def boost (vi : A → Real) (a : A) (d : Real) : A → Real :=
  fun b => vi b + (if b = a then d else 0)

public lemma range_boost_subset (f : Valuation N A → A) (hsmon : IsSMon f) (i : N)
    (vi : A → Real) (a : A) (d : Real) (hd : 0 < d) :
    range f i (boost vi a d) ⊆ range f i vi ∪ {a} := by
  classical
  intro x hx
  by_cases hxa : x = a
  · simp [hxa]
  rcases (Finset.mem_filter.mp hx).2 with ⟨w, hw⟩
  let y := f (Function.update w i vi)
  by_cases hyx : y = x
  · simp only [Finset.mem_union]
    left
    unfold range
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨w, hyx⟩⟩
  · have hxy : x ≠ y := fun h => hyx h.symm
    have hs := hsmon i w (boost vi a d) vi x y hxy hw rfl
    by_cases hya : y = a
    · have hs' : vi x - (vi a + d) > vi x - vi a := by
        simpa [boost, hxa, hya] using hs
      linarith [hd]
    · have hs' : vi x - vi y > vi x - vi y := by
        simpa [boost, hxa, hya] using hs
      linarith
public lemma range_boost_subset_of_mem (f : Valuation N A → A) (hsmon : IsSMon f)
    (i : N) (vi : A → Real) (a : A) (ha : a ∈ range f i vi)
    (d : Real) (hd : 0 < d) :
    range f i (boost vi a d) ⊆ range f i vi := by
  intro x hx
  have h := range_boost_subset f hsmon i vi a d hd hx
  simp only [Finset.mem_union, Finset.mem_singleton] at h
  rcases h with h | h
  · exact h
  · subst x
    exact ha

public lemma mem_range_boost (f : Valuation N A → A) (hsmon : IsSMon f)
    (honto : Function.Surjective f) (i : N) (vi : A → Real) (a : A) :
    ∃ D : Real, ∀ d : Real, D < d → a ∈ range f i (boost vi a d) := by
  classical
  obtain ⟨u, hu⟩ := honto a
  let D : Real := 1 + ∑ b : A,
    |((u i) a - (u i) b) - (vi a - vi b)|
  have ha : a ∈ range f i (u i) := by
    unfold range
    simp only [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ⟨u, ?_⟩⟩
    rw [update_self]
    exact hu
  refine ⟨D, ?_⟩
  intro d hd
  apply range_monotone f hsmon i (u i) (boost vi a d) a ha
  intro b
  by_cases hba : b = a
  · subst b
    simp [boost]
  · have hsingle :
        |((u i) a - (u i) b) - (vi a - vi b)| ≤
          ∑ c : A, |((u i) a - (u i) c) - (vi a - vi c)| :=
      Finset.single_le_sum (f := fun c : A =>
        |((u i) a - (u i) c) - (vi a - vi c)|)
        (fun c _ => abs_nonneg _)
        (Finset.mem_univ b)
    have hgap := le_abs_self (((u i) a - (u i) b) - (vi a - vi b))
    simp [boost, hba, D]
    dsimp [D] at hd
    linarith

@[expose] public def replaceProfile (v w : Valuation N A) (s : Finset N) : Valuation N A :=
  fun j => if j ∈ s then w j else v j

public lemma replaceProfile_insert (v w : Valuation N A) (s : Finset N) (j : N)
    (hj : j ∉ s) :
    replaceProfile v w (insert j s) =
      Function.update (replaceProfile v w s) j (w j) := by
  funext k
  by_cases hkj : k = j
  · subst k
    simp [replaceProfile, hj]
  · rw [Function.update_of_ne hkj]
    simp [replaceProfile, hkj]

public lemma replaceProfile_erase (v w : Valuation N A) (i : N)
    (hvi : v i = w i) :
    replaceProfile v w (Finset.univ.erase i) = w := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [replaceProfile, hvi]
  · simp [replaceProfile, hji]

public lemma smon_update_preserves (f : Valuation N A → A) (hsmon : IsSMon f)
    (v : Valuation N A) (i : N) (vi2 : A → Real) (a : A)
    (ha : f v = a)
    (hgap : ∀ b, vi2 a - vi2 b ≥ (v i) a - (v i) b) :
    f (Function.update v i vi2) = a := by
  by_contra hne
  let b := f (Function.update v i vi2)
  have hab : a ≠ b := by
    intro heq
    apply hne
    exact heq.symm
  have hstart : f (Function.update v i (v i)) = a := by
    rw [update_self]
    exact ha
  have hstrict := hsmon i v (v i) vi2 a b hab hstart rfl
  have hweak := hgap b
  linarith

public lemma smon_update_preserves_avoiding (f : Valuation N A → A)
    (hsmon : IsSMon f) (v : Valuation N A) (i : N)
    (vi2 : A → Real) (winner excluded : A)
    (hwin : f v = winner)
    (hnot : f (Function.update v i vi2) ≠ excluded)
    (hgap : ∀ b, b ≠ excluded → vi2 winner - vi2 b ≥ (v i) winner - (v i) b) :
    f (Function.update v i vi2) = winner := by
  by_contra hne
  let b := f (Function.update v i vi2)
  have hbw : b ≠ winner := by
    intro heq
    apply hne
    exact heq
  have hbe : b ≠ excluded := by
    intro heq
    apply hnot
    exact heq
  have hstart : f (Function.update v i (v i)) = winner := by
    rw [update_self]
    exact hwin
  have hstrict := hsmon i v (v i) vi2 winner b hbw.symm hstart rfl
  have hweak := hgap b hbe
  linarith

public lemma smon_replace_preserves (f : Valuation N A → A)
    (hsmon : IsSMon f) (i : N) (v w : Valuation N A) (a : A)
    (hvi : v i = w i)
    (hgap : ∀ j, j ≠ i → ∀ b, w j a - w j b ≥ v j a - v j b)
    (hv : f v = a) : f w = a := by
  classical
  have hstep : ∀ s : Finset N, s ⊆ Finset.univ.erase i →
      f (replaceProfile v w s) = a := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro _
        have hrep : replaceProfile v w ∅ = v := by
          funext j
          simp [replaceProfile]
        rw [hrep]
        exact hv
    | @insert j s hj ih =>
        intro hsub
        have hsub' : s ⊆ Finset.univ.erase i :=
          Finset.Subset.trans (Finset.subset_insert _ _) hsub
        have hjmem : j ∈ Finset.univ.erase i := hsub (by simp)
        have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
        have hprev := ih hsub'
        have hgap' : ∀ b, w j a - w j b ≥
            (replaceProfile v w s j) a - (replaceProfile v w s j) b := by
          intro b
          simpa [replaceProfile, hj] using hgap j hji b
        have hnext := smon_update_preserves f hsmon
          (replaceProfile v w s) j (w j) a hprev hgap'
        rw [← replaceProfile_insert v w s j hj] at hnext
        exact hnext
  have hfinal := hstep (Finset.univ.erase i) (Finset.Subset.rfl)
  rw [replaceProfile_erase v w i hvi] at hfinal
  exact hfinal

public lemma smon_replace_preserves_avoiding (f : Valuation N A → A)
    (hsmon : IsSMon f) (i : N) (v w : Valuation N A) (winner excluded : A)
    (hvi : v i = w i)
    (hnever : ∀ p : Valuation N A, p i = v i → f p ≠ excluded)
    (hgap : ∀ j, j ≠ i → ∀ b, b ≠ excluded →
      w j winner - w j b ≥ v j winner - v j b)
    (hv : f v = winner) : f w = winner := by
  classical
  have hstep : ∀ s : Finset N, s ⊆ Finset.univ.erase i →
      f (replaceProfile v w s) = winner := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro _
        have hrep : replaceProfile v w ∅ = v := by
          funext j
          simp [replaceProfile]
        rw [hrep]
        exact hv
    | @insert j s hj ih =>
        intro hsub
        have hsub' : s ⊆ Finset.univ.erase i :=
          Finset.Subset.trans (Finset.subset_insert _ _) hsub
        have hjmem : j ∈ Finset.univ.erase i := hsub (by simp)
        have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
        have his : i ∉ s := by
          intro hi
          have : i ∈ Finset.univ.erase i := hsub' hi
          exact (Finset.mem_erase.mp this).1 rfl
        have hprev := ih hsub'
        have hgap' : ∀ b, b ≠ excluded → w j winner - w j b ≥
            (replaceProfile v w s j) winner - (replaceProfile v w s j) b := by
          intro b
          simpa [replaceProfile, hj] using hgap j hji b
        have hnextnot :
            f (Function.update (replaceProfile v w s) j (w j)) ≠ excluded := by
          apply hnever
          rw [Function.update_of_ne (Ne.symm hji)]
          simp [replaceProfile, his]
        have hnext := smon_update_preserves_avoiding f hsmon
          (replaceProfile v w s) j (w j)
          winner excluded hprev hnextnot hgap'
        rw [← replaceProfile_insert v w s j hj] at hnext
        exact hnext
  have hfinal := hstep (Finset.univ.erase i) (Finset.Subset.rfl)
  rw [replaceProfile_erase v w i hvi] at hfinal
  exact hfinal

public lemma range_pair_iia (f : Valuation N A → A) (hsmon : IsSMon f)
    (i : N) (vi vi2 : A → Real) (a b : A)
    (hgap : vi a - vi b = vi2 a - vi2 b)
    (hb : b ∈ range f i vi) (ha2 : a ∈ range f i vi2) :
    b ∈ range f i vi2 := by
  classical
  by_contra hb2
  have hba : b ≠ a := by
    intro he
    subst b
    exact hb2 ha2
  rcases (Finset.mem_filter.mp hb).2 with ⟨v, hv⟩
  rcases (Finset.mem_filter.mp ha2).2 with ⟨v2, hv2⟩
  let p := Function.update v i vi
  let q := Function.update v2 i vi2
  let B : Real := ∑ j : N, ∑ k : A,
      (|p j b - p j k| + |q j a - q j k|)
  let T : Real := B + 1
  let u : A → Real := fun k => if k = b then T else if k = a then 0 else -T
  have hinner (j : N) (k : A) :
      |p j b - p j k| + |q j a - q j k| ≤
        ∑ z : A, (|p j b - p j z| + |q j a - q j z|) :=
    Finset.single_le_sum (f := fun z : A =>
      |p j b - p j z| + |q j a - q j z|)
      (fun z _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ k)
  have houter (j : N) :
      (∑ k : A, (|p j b - p j k| + |q j a - q j k|)) ≤ B :=
    Finset.single_le_sum (f := fun z : N =>
      ∑ k : A, (|p z b - p z k| + |q z a - q z k|))
      (fun z _ => Finset.sum_nonneg fun k _ =>
        add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro k _
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    linarith
  have hpbound (j : N) (k : A) : p j b - p j k ≤ T := by
    dsimp [T]
    calc
      p j b - p j k ≤ |p j b - p j k| := le_abs_self _
      _ ≤ |p j b - p j k| + |q j a - q j k| :=
        le_add_of_nonneg_right (abs_nonneg _)
      _ ≤ ∑ z : A, (|p j b - p j z| + |q j a - q j z|) := hinner j k
      _ ≤ B := houter j
      _ ≤ B + 1 := by linarith
  have hqbound (j : N) (k : A) : q j a - q j k ≤ T := by
    dsimp [T]
    calc
      q j a - q j k ≤ |q j a - q j k| := le_abs_self _
      _ ≤ |p j b - p j k| + |q j a - q j k| :=
        le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ ∑ z : A, (|p j b - p j z| + |q j a - q j z|) := hinner j k
      _ ≤ B := houter j
      _ ≤ B + 1 := by linarith
  have hpGap (j : N) (hj : j ≠ i) (k : A) :
      u b - u k ≥ p j b - p j k := by
    by_cases hkb : k = b
    · subst k
      simp [u]
    · by_cases hka : k = a
      · subst k
        simpa [u, Ne.symm hba] using hpbound j a
      · simp [u, hkb, hka, Ne.symm hba]
        linarith [hpbound j k]
  have hqGap (j : N) (hj : j ≠ i) (k : A) (hk : k ≠ b) :
      u a - u k ≥ q j a - q j k := by
    by_cases hka : k = a
    · subst k
      simp [u, Ne.symm hba]
    · simpa [u, hk, hka, Ne.symm hba] using hqbound j k
  let w := Function.update (fun _ : N => u) i vi
  let w2 := Function.update (fun _ : N => u) i vi2
  have fwb : f w = b := by
    apply smon_replace_preserves f hsmon i p w b
    · simp [p, w, update_self]
    · intro j hj k
      simpa [w, p, hj] using hpGap j hj k
    · exact hv
  have fwa : f w2 = a := by
    apply smon_replace_preserves_avoiding f hsmon i q w2 a b
    · simp [q, w2, update_self]
    · intro r hr
      have hri : r i = vi2 := by simpa [q] using hr
      have hupd : Function.update r i vi2 = r := by
        rw [← hri]
        exact update_self r i
      intro heq
      apply hb2
      unfold range
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ⟨r, by rw [hupd]; exact heq⟩⟩
    · intro j hj k hk
      simpa [w2, q, hj] using hqGap j hj k hk
    · exact hv2
  have hstrict' := hsmon i (fun _ => u) vi vi2 b a hba fwb fwa
  linarith

public lemma range_boost_preserves_of_nondictatable (f : Valuation N A → A)
    (hsmon : IsSMon f) (i : N) (vi : A → Real) (a c : A)
    (hnd : ¬ IsDictatable (range f i) a) (hc : c ∈ range f i vi)
    (hca : c ≠ a) (d : Real)
    (ha2 : a ∈ range f i (boost vi a d)) :
    c ∈ range f i (boost vi a d) := by
  classical
  let vi2 := boost vi a d
  have hnotSingleton : range f i vi2 ≠ {a} := by
    intro heq
    exact hnd ⟨vi2, heq⟩
  have hother : ∃ b, b ≠ a ∧ b ∈ range f i vi2 := by
    by_contra h
    have hsub : range f i vi2 ⊆ {a} := by
      intro b hb
      by_contra hba
      have hba' : b ≠ a := by
        intro heq
        subst b
        exact hba (by simp)
      exact h ⟨b, hba', hb⟩
    have heq : range f i vi2 = {a} := by
      ext b
      simp only [Finset.mem_singleton]
      constructor
      · intro hb
        exact Finset.mem_singleton.mp (hsub hb)
      · intro hba
        subst b
        exact ha2
    exact hnotSingleton heq
  rcases hother with ⟨b, hba, hb2⟩
  by_cases hbc : b = c
  · simpa [hbc] using hb2
  · have hgap : vi b - vi c = vi2 b - vi2 c := by
      simp [vi2, boost, hba, hca]
    exact range_pair_iia f hsmon i vi vi2 b c hgap hc hb2

public lemma range_transfer_of_gap (f : Valuation N A → A) (hsmon : IsSMon f)
    (i : N) (a b : A) (hab : a ≠ b)
    (hnd : ¬ IsDictatable (range f i) a)
    (v w : A → Real) (ha : a ∈ range f i v) (hb : b ∈ range f i v)
    (haW : a ∈ range f i w)
    (hgap : v a - v b ≤ w a - w b) : b ∈ range f i w := by
  classical
  let d := w a - w b - (v a - v b)
  have hd : 0 ≤ d := by dsimp [d]; linarith
  let vd := boost v a d
  have haD : a ∈ range f i vd :=
    range_monotone f hsmon i v vd a ha (by
      intro x
      by_cases hxa : x = a
      · subst x
        simp [vd, boost]
      · simp [vd, boost, hxa]
        linarith)
  have hbD : b ∈ range f i vd :=
    range_boost_preserves_of_nondictatable f hsmon i v a b hnd hb (Ne.symm hab) d haD
  have hgapD : vd a - vd b = w a - w b := by
    have h1 : vd a = v a + d := by
      show (boost v a d) a = v a + d
      simp [boost]
    have h2 : vd b = v b := by
      show (boost v a d) b = v b
      simp [boost, Ne.symm hab]
    have hddef : d = w a - w b - (v a - v b) := rfl
    calc vd a - vd b = (v a + d) - v b := by rw [h1, h2]
      _ = w a - w b := by rw [hddef]; linarith
  exact range_pair_iia f hsmon i vd w a b hgapD hbD haW

public lemma range_boost_full_of_nondictatable (f : Valuation N A → A)
    (hsmon : IsSMon f) (honto : Function.Surjective f) (i : N)
    (a : A) (hnd : ¬ IsDictatable (range f i) a) (vi : A → Real) :
    ∃ d : Real, 0 < d ∧ range f i (boost vi a d) = Finset.univ := by
  classical
  obtain ⟨D, hD⟩ := mem_range_boost f hsmon honto i vi a
  let gamma := D + 1
  have hgamma : a ∈ range f i (boost vi a gamma) := by
    apply hD gamma
    dsimp [gamma]
    linarith
  have hsource : ∀ k : A, ∃ wk : A → Real,
      a ∈ range f i wk ∧ k ∈ range f i wk := by
    intro k
    obtain ⟨v, hv⟩ := honto k
    have hk : k ∈ range f i (v i) := by
      unfold range
      simp only [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ⟨v, ?_⟩⟩
      rw [update_self]
      exact hv
    obtain ⟨Dk, hDk⟩ := mem_range_boost f hsmon honto i (v i) a
    let dk := Dk + 1
    have ha : a ∈ range f i (boost (v i) a dk) := by
      apply hDk dk
      dsimp [dk]
      linarith
    have hkD : k ∈ range f i (boost (v i) a dk) := by
      by_cases hka : k = a
      · simpa [hka] using ha
      · exact range_boost_preserves_of_nondictatable f hsmon i (v i) a k
          hnd hk hka dk ha
    exact ⟨boost (v i) a dk, ha, hkD⟩
  choose wk hwka hwkk using hsource
  let gap (k : A) := wk k a - wk k k
  let delta := |gamma| + 1 + ∑ k : A, |gap k - (vi a - vi k)|
  have hdelta : gamma ≤ delta := by
    have hsum : 0 ≤ ∑ k : A, |gap k - (vi a - vi k)| :=
      Finset.sum_nonneg fun k hk => abs_nonneg _
    have habs : gamma ≤ |gamma| := le_abs_self _
    have hdd : delta = |gamma| + 1 + ∑ k : A, |gap k - (vi a - vi k)| := rfl
    rw [hdd]; linarith
  have hsum_bound (k : A) :
      |gap k - (vi a - vi k)| ≤ ∑ x : A, |gap x - (vi a - vi x)| :=
    Finset.single_le_sum (fun x _ => abs_nonneg (gap x - (vi a - vi x))) (Finset.mem_univ k)
  let viD := boost vi a delta
  have haD : a ∈ range f i viD :=
    range_monotone f hsmon i (boost vi a gamma) viD a hgamma (by
      intro k
      by_cases hka : k = a
      · subst k
        simp [viD, boost]
      · simp [viD, boost, hka]
        linarith)
  have hkD (k : A) : k ∈ range f i viD := by
    by_cases hka : k = a
    · simpa [hka] using haD
    · have hgap : wk k a - wk k k ≤ viD a - viD k := by
        have hviDa : viD a = vi a + delta := by simp [viD, boost]
        have hviDk : viD k = vi k := by simp [viD, boost, hka]
        have hbound := hsum_bound k
        have hle : gap k - (vi a - vi k) ≤
            |gap k - (vi a - vi k)| := le_abs_self _
        have hgapk : gap k = wk k a - wk k k := rfl
        have hdd : delta = |gamma| + 1 + ∑ x : A, |gap x - (vi a - vi x)| := rfl
        have habs_nn : 0 ≤ |gamma| := abs_nonneg _
        rw [hviDa, hviDk, ← hgapk, hdd]
        linarith [hbound, hle, habs_nn]
      exact range_transfer_of_gap f hsmon i a k (Ne.symm hka)
        hnd (wk k) viD (hwka k) (hwkk k) haD hgap
  have hfull : range f i viD = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro k
    exact hkD k
  have hdelta_pos : 0 < delta := by
    have hsum : 0 ≤ ∑ k : A, |gap k - (vi a - vi k)| :=
      Finset.sum_nonneg fun k hk => abs_nonneg _
    have habs_nn : 0 ≤ |gamma| := abs_nonneg _
    have hdd : delta = |gamma| + 1 + ∑ k : A, |gap k - (vi a - vi k)| := rfl
    rw [hdd]; linarith
  exact ⟨delta, hdelta_pos, hfull⟩

public lemma no_veto_of_nondictatable (f : Valuation N A → A) (hsmon : IsSMon f)
    (honto : Function.Surjective f) (i : N)
    (h : ∀ a : A, ¬ IsDictatable (range f i) a) : HasNoVetoPower f i := by
  classical
  intro vi
  obtain ⟨a, ha⟩ := range_nonempty f i vi
  obtain ⟨d, hd, hfull⟩ :=
    range_boost_full_of_nondictatable f hsmon honto i a (h a) vi
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  have hx : x ∈ range f i (boost vi a d) := by
    rw [hfull]
    simp
  have hsubset := range_boost_subset f hsmon i vi a d hd hx
  simp only [Finset.mem_union, Finset.mem_singleton] at hsubset
  rcases hsubset with hx | hxa
  · exact hx
  · subst x
    exact ha

public lemma at_most_one_all_dictatable (f : Valuation N A → A) (hsmon : IsSMon f)
    (honto : Function.Surjective f) (hA : 3 ≤ Fintype.card A)
    (i j : N) (hij : i ≠ j)
    (hi : ∀ a : A, IsDictatable (range f i) a)
    (hj : ∀ a : A, IsDictatable (range f j) a) : False := by
  classical
  have hcard_ne : Fintype.card A ≠ 1 := by omega
  have habs : ∃ a b : A, a ≠ b := by
    by_contra h
    push Not at h
    obtain ⟨a0⟩ := (inferInstance : Nonempty A)
    have hcard : Fintype.card A = 1 :=
      Fintype.card_eq_one_iff.mpr ⟨a0, fun a => h a a0⟩
    exact hcard_ne hcard
  obtain ⟨a, b, hab⟩ := habs
  obtain ⟨vi, hvi⟩ := hi a
  obtain ⟨vj, hvj⟩ := hj b
  let v0 : Valuation N A := fun _ _ => 0
  let w : Valuation N A := Function.update (Function.update v0 i vi) j vj
  have hcomm : Function.update (Function.update v0 j vj) i vi = w := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [w, hij]
    · by_cases hkj : k = j
      · subst k
        simp [w, hki]
      · simp [w, hki, hkj]
  have hmem_i : f w ∈ range f i vi := by
    unfold range
    simp only [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    refine ⟨Function.update v0 j vj, ?_⟩
    rw [← hcomm]
  have hmem_j : f w ∈ range f j vj := by
    unfold range
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨Function.update v0 i vi, rfl⟩⟩
  have hfa : f w = a := by
    rw [hvi] at hmem_i
    exact Finset.mem_singleton.mp hmem_i
  have hfb : f w = b := by
    rw [hvj] at hmem_j
    exact Finset.mem_singleton.mp hmem_j
  exact hab (hfa.symm.trans hfb)

public theorem all_but_one_no_veto (f : Valuation N A → A) (hsmon : IsSMon f)
    (honto : Function.Surjective f) (hA : 3 ≤ Fintype.card A) :
    ∃ i₀ : N, ∀ i, i ≠ i₀ → HasNoVetoPower f i := by
  classical
  by_contra h
  have htwo : ∀ i₀ : N, ∃ i : N, i ≠ i₀ ∧ ¬ HasNoVetoPower f i := by
    intro i₀
    by_contra hnone
    apply h
    refine ⟨i₀, ?_⟩
    intro i hne
    by_contra hnv
    exact hnone ⟨i, hne, hnv⟩
  obtain ⟨i₀⟩ := (inferInstance : Nonempty N)
  obtain ⟨j, _hji, hjbad⟩ := htwo i₀
  obtain ⟨i, hij, hibad⟩ := htwo j
  have hdict_i : ∃ a : A, IsDictatable (range f i) a := by
    by_contra hnot
    apply hibad
    apply no_veto_of_nondictatable f hsmon honto i
    intro a
    by_contra ha
    exact hnot ⟨a, ha⟩
  have hdict_j : ∃ b : A, IsDictatable (range f j) b := by
    by_contra hnot
    apply hjbad
    apply no_veto_of_nondictatable f hsmon honto j
    intro b
    by_contra hb
    exact hnot ⟨b, hb⟩
  obtain ⟨a, ⟨vi, hvi⟩⟩ := hdict_i
  obtain ⟨b, ⟨vj, hvj⟩⟩ := hdict_j
  let v0 : Valuation N A := fun _ _ => 0
  have update_comm (u v : A → Real) :
      Function.update (Function.update v0 j v) i u =
        Function.update (Function.update v0 i u) j v := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [hij]
    · by_cases hkj : k = j
      · subst k
        simp [hki]
      · simp [hki, hkj]
  by_cases hab : a = b
  · subst b
    have ha0_mem (u : A → Real) : a ∈ range f i u := by
      let p : Valuation N A := Function.update (Function.update v0 i u) j vj
      have hp : f p ∈ range f j vj := by
        unfold range
        simp only [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, ⟨Function.update v0 i u, rfl⟩⟩
      rw [hvj] at hp
      have hfp : f p = a := Finset.mem_singleton.mp hp
      have hcomm := update_comm u vj
      unfold range
      simp only [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ⟨Function.update v0 j vj, ?_⟩⟩
      rw [hcomm]
      exact hfp
    have hcard_ne_one : Fintype.card A ≠ 1 := by omega
    have hx : ∃ x : A, x ≠ a := by
      by_contra hno
      push Not at hno
      have hcard : Fintype.card A = 1 :=
        Fintype.card_eq_one_iff.mpr ⟨a, fun x => hno x⟩
      exact hcard_ne_one hcard
    obtain ⟨x, hxa⟩ := hx
    have hax : a ≠ x := Ne.symm hxa
    have hnd : ¬ IsDictatable (range f i) x := by
      intro hdict
      obtain ⟨u, hu⟩ := hdict
      have hm := ha0_mem u
      rw [hu] at hm
      exact hxa (Finset.mem_singleton.mp hm).symm
    have hpair : ({a, x} : Finset A).card = 2 := by simp [hax]
    have hthird : ∃ c : A, c ∉ ({a, x} : Finset A) := by
      by_contra hnone
      have hsub : Finset.univ ⊆ ({a, x} : Finset A) := by
        intro c hc
        by_contra hcin
        exact hnone ⟨c, hcin⟩
      have hle := Finset.card_le_card hsub
      simp [hpair] at hle
      omega
    obtain ⟨c, hc⟩ := hthird
    have hfull := range_boost_full_of_nondictatable f hsmon honto i x hnd vi
    obtain ⟨d, hd, hfull⟩ := hfull
    have hcfull : c ∈ range f i (boost vi x d) := by
      rw [hfull]
      simp
    have hsmall := range_boost_subset f hsmon i vi x d hd hcfull
    rw [hvi] at hsmall
    have hcin : c ∈ ({a, x} : Finset A) := by simpa using hsmall
    exact hc hcin
  · let w : Valuation N A := Function.update (Function.update v0 i vi) j vj
    have hmem_i : f w ∈ range f i vi := by
      unfold range
      simp only [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ⟨Function.update v0 j vj, ?_⟩⟩
      have heq : Function.update (Function.update v0 j vj) i vi = w :=
        update_comm vi vj
      rw [heq]
    have hmem_j : f w ∈ range f j vj := by
      unfold range
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ⟨Function.update v0 i vi, rfl⟩⟩
    rw [hvi] at hmem_i
    rw [hvj] at hmem_j
    have hfa : f w = a := Finset.mem_singleton.mp hmem_i
    have hfb : f w = b := Finset.mem_singleton.mp hmem_j
    exact hab (hfa.symm.trans hfb)

end

end Roberts
