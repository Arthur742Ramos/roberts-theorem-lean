module

public import Roberts.Defs
public import Mathlib.Tactic.Linarith

namespace Roberts

section

variable {N A : Type*} [Fintype N] [Fintype A] [DecidableEq N] [DecidableEq A]

@[expose] public def Achievable (f : Valuation N A → A) (i : N) (v : Valuation N A) (a : A) : Prop :=
  ∃ vi : A → Real, f (Function.update v i vi) = a

@[expose] public noncomputable def price (M : Mechanism N A) (i : N) (v : Valuation N A) (a : A) : Real :=
  by
    classical
    exact if h : Achievable M.choiceFn i v a then
      M.pay (Function.update v i h.choose) i
    else
      0

omit [Fintype N] [Fintype A] [DecidableEq A] in
public lemma achievable_update (f : Valuation N A → A) (i : N) (v : Valuation N A)
    (vi : A → Real) (a : A) :
    Achievable f i (Function.update v i vi) a ↔ Achievable f i v a := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, by simpa only [Function.update_idem] using hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, by simpa only [Function.update_idem] using hw⟩

omit [DecidableEq A] in
public lemma taxation_payment (M : Mechanism N A) (hdsic : IsDSIC M)
    (i : N) (v : Valuation N A) (vi1 vi2 : A → Real) (a : A)
    (h1 : M.choiceFn (Function.update v i vi1) = a)
    (h2 : M.choiceFn (Function.update v i vi2) = a) :
    M.pay (Function.update v i vi1) i = M.pay (Function.update v i vi2) i := by
  have h12 := hdsic i (Function.update v i vi1) vi2
  have h21 := hdsic i (Function.update v i vi2) vi1
  have hprof12 : @Function.update N (fun _ => A → Real) (Classical.decEq N)
      (Function.update v i vi1) i vi2 = Function.update v i vi2 := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  have hprof21 : @Function.update N (fun _ => A → Real) (Classical.decEq N)
      (Function.update v i vi2) i vi1 = Function.update v i vi1 := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  have hc12 : M.choiceFn (@Function.update N (fun _ => A → Real) (Classical.decEq N)
      (Function.update v i vi1) i vi2) = a := by
    calc
      _ = M.choiceFn (Function.update v i vi2) := congrArg M.choiceFn hprof12
      _ = a := h2
  have hc21 : M.choiceFn (@Function.update N (fun _ => A → Real) (Classical.decEq N)
      (Function.update v i vi2) i vi1) = a := by
    calc
      _ = M.choiceFn (Function.update v i vi1) := congrArg M.choiceFn hprof21
      _ = a := h1
  have hp12 := congrArg (fun p : Valuation N A => M.pay p i) hprof12
  have hp21 := congrArg (fun p : Valuation N A => M.pay p i) hprof21
  have h12prime : vi1 a - M.pay (Function.update v i vi1) i ≥
      vi1 a - M.pay (Function.update v i vi2) i := by
    simpa only [Function.update_self, h1, hc12, hp12] using h12
  have h21prime : vi2 a - M.pay (Function.update v i vi2) i ≥
      vi2 a - M.pay (Function.update v i vi1) i := by
    simpa only [Function.update_self, h2, hc21, hp21] using h21
  linarith [h12prime, h21prime]

public lemma price_eq_of_mem (M : Mechanism N A) (hdsic : IsDSIC M)
    (i : N) (v : Valuation N A) (vi : A → Real) (a : A)
    (h : M.choiceFn (Function.update v i vi) = a) :
    M.pay (Function.update v i vi) i = price M i v a := by
  unfold price
  have hex : Achievable M.choiceFn i v a := ⟨vi, h⟩
  rw [dite_eq_left hex]
  exact taxation_payment M hdsic i v vi hex.choose a h hex.choose_spec

public lemma price_independent (M : Mechanism N A) (hdsic : IsDSIC M)
    (i : N) (v : Valuation N A)
    (vi vi2 : A → Real) (a : A) :
    price M i (Function.update v i vi) a = price M i (Function.update v i vi2) a := by
  classical
  unfold price
  by_cases hc : Achievable M.choiceFn i v a
  · have hleft : Achievable M.choiceFn i (Function.update v i vi) a :=
      (achievable_update M.choiceFn i v vi a).mpr hc
    have hright : Achievable M.choiceFn i (Function.update v i vi2) a :=
      (achievable_update M.choiceFn i v vi2 a).mpr hc
    rw [dite_eq_left hleft, dite_eq_left hright]
    have hleft_spec :
        M.choiceFn (Function.update v i hleft.choose) = a := by
      simpa only [Function.update_idem] using hleft.choose_spec
    have hright_spec :
        M.choiceFn (Function.update v i hright.choose) = a := by
      simpa only [Function.update_idem] using hright.choose_spec
    simpa only [Function.update_idem] using
      taxation_payment M hdsic i v hleft.choose hright.choose a hleft_spec hright_spec
  · have hleft : ¬ Achievable M.choiceFn i (Function.update v i vi) a := by
      intro h
      exact hc ((achievable_update M.choiceFn i v vi a).mp h)
    have hright : ¬ Achievable M.choiceFn i (Function.update v i vi2) a := by
      intro h
      exact hc ((achievable_update M.choiceFn i v vi2 a).mp h)
    rw [dite_eq_right hleft, dite_eq_right hright]

public lemma taxation_ineq (M : Mechanism N A) (hdsic : IsDSIC M)
    (i : N) (v : Valuation N A) (vi : A → Real) (a : A)
    (ha : Achievable M.choiceFn i v a) :
    vi (M.choiceFn (Function.update v i vi)) -
        price M i v (M.choiceFn (Function.update v i vi)) ≥
      vi a - price M i v a := by
  obtain ⟨w, hw⟩ := ha
  let astar := M.choiceFn (Function.update v i vi)
  have hchoice : M.choiceFn (Function.update v i vi) = astar := rfl
  have hpStar : M.pay (Function.update v i vi) i = price M i v astar :=
    price_eq_of_mem M hdsic i v vi astar hchoice
  have hpA : M.pay (Function.update v i w) i = price M i v a :=
    price_eq_of_mem M hdsic i v w a hw
  have hdsicAtUpdate := hdsic i (Function.update v i vi) w
  have hprof : @Function.update N (fun _ => A → Real) (Classical.decEq N)
      (Function.update v i vi) i w = Function.update v i w := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  have hc : M.choiceFn (@Function.update N (fun _ => A → Real) (Classical.decEq N)
      (Function.update v i vi) i w) = a := by
    calc
      _ = M.choiceFn (Function.update v i w) := congrArg M.choiceFn hprof
      _ = a := hw
  have hp := congrArg (fun p : Valuation N A => M.pay p i) hprof
  have hfinal : vi astar - M.pay (Function.update v i vi) i ≥
      vi a - M.pay (Function.update v i w) i := by
    simpa only [Function.update_self, hchoice, hc, hp] using hdsicAtUpdate
  simpa only [hpStar, hpA] using hfinal

@[expose] public def IsWMon (f : Valuation N A → A) : Prop :=
  ∀ i v (vi vi2 : A → Real) (a b : A), a ≠ b →
    f (Function.update v i vi) = a →
    f (Function.update v i vi2) = b →
      vi a - vi b ≥ vi2 a - vi2 b

public theorem wmon_of_dsic (M : Mechanism N A) (hdsic : IsDSIC M) : IsWMon M.choiceFn := by
  intro i v vi vi2 a b hab h1 h2
  have hb : Achievable M.choiceFn i v b := ⟨vi2, h2⟩
  have ha : Achievable M.choiceFn i v a := ⟨vi, h1⟩
  have hvi := taxation_ineq M hdsic i v vi b hb
  have hvi2 := taxation_ineq M hdsic i v vi2 a ha
  rw [h1] at hvi
  rw [h2] at hvi2
  linarith

end

end Roberts
