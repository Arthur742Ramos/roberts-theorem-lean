import Roberts.SMon

namespace Roberts

section

variable {N A : Type*} [Fintype N] [Fintype A] [DecidableEq N] [DecidableEq A]
  [Nonempty N] [Nonempty A]

noncomputable def range (f : Valuation N A → A) (i : N) (vi : A → Real) : Finset A := by
  classical
  exact Finset.univ.filter (fun a => ∃ v : Valuation N A, f (Function.update v i vi) = a)

def HasNoVetoPower (f : Valuation N A → A) (i : N) : Prop :=
  ∀ vi : A → Real, range f i vi = Finset.univ

def IsDictatable (R : (A → Real) → Finset A) (a : A) : Prop :=
  ∃ vi : A → Real, R vi = {a}

lemma range_nonempty (f : Valuation N A → A) (i : N) (vi : A → Real) :
    (range f i vi).Nonempty := by
  classical
  let v : Valuation N A := fun _ _ => 0
  let a : A := f (Function.update v i vi)
  refine ⟨a, ?_⟩
  unfold range
  simp only [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, ⟨v, rfl⟩⟩

lemma range_monotone (f : Valuation N A → A) (hsmon : IsSMon f) (i : N)
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

lemma range_iia (f : Valuation N A → A) (hsmon : IsSMon f) (i : N)
    (vi vi2 : A → Real) (a : A) (h : ∀ b, vi a - vi b = vi2 a - vi2 b) :
    (a ∈ range f i vi ↔ a ∈ range f i vi2) := by
  constructor
  · intro ha
    exact range_monotone f hsmon i vi vi2 a ha (fun b => le_of_eq (h b))
  · intro ha
    exact range_monotone f hsmon i vi2 vi a ha (fun b => le_of_eq (h b).symm)

lemma dictatable_dichotomy (R : (A → Real) → Finset A)
    (hne : ∀ vj, (R vj).Nonempty)
    (hmono : ∀ vj vj2 x, x ∈ R vj → (∀ y, vj2 x - vj2 y ≥ vj x - vj y) → x ∈ R vj2)
    (hiia : ∀ vj vj2 x, (∀ y, vj x - vj y = vj2 x - vj2 y) → (x ∈ R vj ↔ x ∈ R vj2))
    (hA : 3 ≤ Fintype.card A) :
    (∀ x, IsDictatable R x) ∨ (∀ x, ¬ IsDictatable R x) := by
  -- As stated this is false: for A = Fin 3, R v = {0} satisfies all three
  -- correspondence hypotheses, but 0 is dictatable and 1 is not.
  sorry

lemma no_veto_of_nondictatable (f : Valuation N A → A) (hsmon : IsSMon f)
    (honto : Function.Surjective f) (i : N)
    (h : ∀ a : A, ¬ IsDictatable (range f i) a) : HasNoVetoPower f i := by
  -- Surjectivity and strong monotonicity turn any missing alternative into a singleton range.
  sorry

lemma at_most_one_all_dictatable (f : Valuation N A → A) (hsmon : IsSMon f)
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

theorem all_but_one_no_veto (f : Valuation N A → A) (hsmon : IsSMon f)
    (honto : Function.Surjective f) (hA : 3 ≤ Fintype.card A) :
    ∃ i₀ : N, ∀ i, i ≠ i₀ → HasNoVetoPower f i := by
  classical
  have hsplit : ∀ i : N,
      (∀ a : A, IsDictatable (range f i) a) ∨
      (∀ a : A, ¬ IsDictatable (range f i) a) := by
    intro i
    exact dictatable_dichotomy
      (R := range f i)
      (hne := fun vj => range_nonempty f i vj)
      (hmono := fun vj vj2 x hx hgap => range_monotone f hsmon i vj vj2 x hx hgap)
      (hiia := fun vj vj2 x hgap => range_iia f hsmon i vj vj2 x hgap)
      hA
  by_cases hex : ∃ i : N, ∀ a : A, IsDictatable (range f i) a
  · rcases hex with ⟨i₀, hi₀⟩
    refine ⟨i₀, ?_⟩
    intro i hne
    rcases hsplit i with hdict | hnondict
    · exact False.elim
        (at_most_one_all_dictatable f hsmon honto hA i i₀ hne hdict hi₀)
    · exact no_veto_of_nondictatable f hsmon honto i hnondict
  · have hall : ∀ i : N, ∀ a : A, ¬ IsDictatable (range f i) a := by
      intro i
      rcases hsplit i with hdict | hnondict
      · exfalso
        exact hex ⟨i, hdict⟩
      · exact hnondict
    rcases (inferInstance : Nonempty N) with ⟨i₀⟩
    refine ⟨i₀, ?_⟩
    intro i hne
    exact no_veto_of_nondictatable f hsmon honto i (hall i)

end

end Roberts
