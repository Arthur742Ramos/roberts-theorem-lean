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
  -- A third alternative lets monotonicity and IIA transfer any singleton range to every alternative.
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
  -- Merge the two forcing valuations to obtain incompatible outcomes at one profile.
  sorry

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
