import Roberts.TwoAgent
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt

namespace Roberts

section

variable {N A : Type*} [Fintype N] [Fintype A] [DecidableEq N] [DecidableEq A]
  [Nonempty N] [Nonempty A]

private lemma halfspace_homog (u u' : N → Real) (hne : u' ≠ 0)
    (hsub : ∀ z : N → Real,
      0 < Finset.univ.sum (fun i => u' i * z i) →
        0 ≤ Finset.univ.sum (fun i => u i * z i)) :
    ∃ alpha : Real, 0 ≤ alpha ∧ ∀ i, u i = alpha * u' i := by
  classical
  let S2 : Real := Finset.univ.sum (fun i => (u' i) ^ 2)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have hjpos : 0 < (u' j) ^ 2 := sq_pos_of_ne_zero hj
  have hS2lower : (u' j) ^ 2 ≤ S2 := by
    dsimp [S2]
    exact Finset.single_le_sum
      (fun i hi => sq_nonneg (u' i)) (Finset.mem_univ j)
  have hS2pos : 0 < S2 := lt_of_lt_of_le hjpos hS2lower
  let alpha : Real := (Finset.univ.sum (fun i => u i * u' i)) / S2
  let m : N → Real := fun i => u i - alpha * u' i
  have halphaS2 : alpha * S2 = Finset.univ.sum (fun i => u i * u' i) := by
    dsimp [alpha]
    exact div_mul_cancel₀ _ (ne_of_gt hS2pos)
  have horth : Finset.univ.sum (fun i => m i * u' i) = 0 := by
    calc
      Finset.univ.sum (fun i => m i * u' i) =
          Finset.univ.sum (fun i => u i * u' i - alpha * (u' i) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [m]
        ring
      _ = Finset.univ.sum (fun i => u i * u' i) -
          Finset.univ.sum (fun i => alpha * (u' i) ^ 2) := by
        rw [Finset.sum_sub_distrib]
      _ = Finset.univ.sum (fun i => u i * u' i) - alpha * S2 := by
        congr 1
        calc
          Finset.univ.sum (fun i => alpha * (u' i) ^ 2) =
              alpha * Finset.univ.sum (fun i => (u' i) ^ 2) := by
            rw [Finset.mul_sum]
          _ = alpha * S2 := by rfl
      _ = 0 := by rw [← halphaS2]; ring
  have hdecomp : ∀ i, u i = alpha * u' i + m i := by
    intro i
    dsimp [m]
    ring
  have hdual (t : Real) :
      Finset.univ.sum (fun i => u' i * (-m i + t * u' i)) = t * S2 := by
    have hcross : Finset.univ.sum (fun i => u' i * m i) = 0 := by
      calc
        Finset.univ.sum (fun i => u' i * m i) =
            Finset.univ.sum (fun i => m i * u' i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = 0 := horth
    have hterm : Finset.univ.sum (fun i => t * (u' i) ^ 2) = t * S2 := by
      calc
        Finset.univ.sum (fun i => t * (u' i) ^ 2) =
            t * Finset.univ.sum (fun i => (u' i) ^ 2) := by
          exact (Finset.mul_sum Finset.univ
            (fun i => (u' i) ^ 2) t).symm
        _ = t * S2 := by rfl
    calc
      Finset.univ.sum (fun i => u' i * (-m i + t * u' i)) =
          Finset.univ.sum (fun i => -(u' i * m i) + t * (u' i) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = Finset.univ.sum (fun i => -(u' i * m i)) +
          Finset.univ.sum (fun i => t * (u' i) ^ 2) := by
        rw [Finset.sum_add_distrib]
      _ = t * S2 := by
        rw [Finset.sum_neg_distrib, hcross, hterm]
        ring
  have hscore (t : Real) :
      Finset.univ.sum (fun i => u i * (-m i + t * u' i)) =
        -Finset.univ.sum (fun i => (m i) ^ 2) + alpha * t * S2 := by
    calc
      Finset.univ.sum (fun i => u i * (-m i + t * u' i)) =
          Finset.univ.sum (fun i =>
            (-(m i) ^ 2) + alpha * t * (u' i) ^ 2 +
              (t - alpha) * (m i * u' i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hdecomp i]
        ring
      _ = -(Finset.univ.sum (fun i => (m i) ^ 2)) +
          alpha * t * S2 + (t - alpha) *
            Finset.univ.sum (fun i => m i * u' i) := by
        have hsq : Finset.univ.sum (fun i => alpha * t * (u' i) ^ 2) =
            alpha * t * S2 := by
          calc
            Finset.univ.sum (fun i => alpha * t * (u' i) ^ 2) =
                alpha * t * Finset.univ.sum (fun i => (u' i) ^ 2) := by
              exact (Finset.mul_sum Finset.univ
                (fun i => (u' i) ^ 2) (alpha * t)).symm
            _ = alpha * t * S2 := by rfl
        have hmix : Finset.univ.sum
            (fun i => (t - alpha) * (m i * u' i)) =
              (t - alpha) * Finset.univ.sum (fun i => m i * u' i) := by
          exact (Finset.mul_sum Finset.univ
            (fun i => m i * u' i) (t - alpha)).symm
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_neg_distrib, hsq, hmix]
      _ = -Finset.univ.sum (fun i => (m i) ^ 2) + alpha * t * S2 := by
        rw [horth]
        ring
  have hmzero : ∀ i, m i = 0 := by
    intro i
    by_contra hmi
    have hmisq : 0 < (m i) ^ 2 := sq_pos_of_ne_zero hmi
    let S3 : Real := Finset.univ.sum (fun j => (m j) ^ 2)
    have hS3lower : (m i) ^ 2 ≤ S3 := by
      dsimp [S3]
      exact Finset.single_le_sum
        (fun j hj => sq_nonneg (m j)) (Finset.mem_univ i)
    have hS3pos : 0 < S3 := lt_of_lt_of_le hmisq hS3lower
    by_cases halpha : alpha ≤ 0
    · let t : Real := 1
      have ht : 0 < t := by norm_num [t]
      have hzpos : 0 < Finset.univ.sum
          (fun j => u' j * (-m j + t * u' j)) := by
        rw [hdual t]
        exact mul_pos ht hS2pos
      have hnonneg := hsub (fun j => -m j + t * u' j) hzpos
      rw [hscore t] at hnonneg
      have hbad : -S3 + alpha * t * S2 < 0 := by
        dsimp [t]
        nlinarith
      linarith
    · have hapos : 0 < alpha := lt_of_not_ge halpha
      let t : Real := S3 / (2 * alpha * S2)
      have ht : 0 < t := by
        dsimp [t]
        positivity
      have hzpos : 0 < Finset.univ.sum
          (fun j => u' j * (-m j + t * u' j)) := by
        rw [hdual t]
        exact mul_pos ht hS2pos
      have hnonneg := hsub (fun j => -m j + t * u' j) hzpos
      rw [hscore t] at hnonneg
      have hcalc : alpha * t * S2 = S3 / 2 := by
        dsimp [t]
        field_simp
      have hbad : -S3 + alpha * t * S2 < 0 := by
        rw [hcalc]
        linarith
      linarith
  have hu : ∀ i, u i = alpha * u' i := by
    intro i
    rw [hdecomp i, hmzero i]
    ring
  have hdot : Finset.univ.sum (fun i => u i * u' i) = alpha * S2 := by
    calc
      Finset.univ.sum (fun i => u i * u' i) =
          Finset.univ.sum (fun i => alpha * (u' i) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hu i]
        ring
      _ = alpha * S2 := by
        rw [Finset.mul_sum]
  have hdot_nonneg : 0 ≤ Finset.univ.sum (fun i => u i * u' i) := by
    apply hsub u'
    simpa [S2, pow_two] using hS2pos
  refine ⟨alpha, ?_, hu⟩
  rw [hdot] at hdot_nonneg
  nlinarith

/-- The choice function with agent i₀'s valuation fixed at vi₀. Used to state
    the per-slice affine representations in the n ≥ 3 induction step. -/
def slice (f : Valuation N A → A) (i₀ : N) (vi₀ : A → Real) : Valuation N A → A :=
  fun v => f (Function.update v i₀ vi₀)

private lemma weight_pos_of_hnd
    (i₀ : N) (w : (A → Real) → N → Real)
    (hwind : ∀ vi₀ vi₀' i, i ≠ i₀ → w vi₀ i = w vi₀' i)
    (hnd : ∃ i, i ≠ i₀ ∧ ∃ vi₀, 0 < w vi₀ i) :
    ∃ j, j ≠ i₀ ∧ ∀ vi₀, 0 < w vi₀ j := by
  obtain ⟨j, hj, vi₀star, hpos⟩ := hnd
  refine ⟨j, hj, ?_⟩
  intro vi₀
  rw [hwind vi₀ vi₀star j hj]
  exact hpos

private lemma slice_force_via_j
    (f : Valuation N A → A)
    (i₀ j : N) (hj : j ≠ i₀)
    (w : (A → Real) → N → Real) (k : (A → Real) → A → Real)
    (hrep : ∀ vi₀ : A → Real,
      (∀ i, 0 ≤ w vi₀ i) ∧
      (∀ v a, affineScore (w vi₀) (k vi₀) v (slice f i₀ vi₀ v) ≥
        affineScore (w vi₀) (k vi₀) v a))
    (hpos : ∀ vi₀, 0 < w vi₀ j)
    (vi₀ : A → Real) (target : A) :
    ∃ v : Valuation N A, slice f i₀ vi₀ v = target := by
  classical
  -- The sum bounds every individual absolute offset difference, so this
  -- finite value makes target strictly beat every other alternative.
  let B : Real := Finset.univ.sum (fun a => |k vi₀ target - k vi₀ a|)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let M : Real := (B + 1) / w vi₀ j
  have hM : w vi₀ j * M = B + 1 := by
    dsimp [M]
    rw [mul_comm]
    exact div_mul_cancel₀ _ (ne_of_gt (hpos vi₀))
  let v : Valuation N A :=
    fun i x => if i = j then if x = target then M else 0 else 0
  refine ⟨v, ?_⟩
  have htarget : affineScore (w vi₀) (k vi₀) v target =
      w vi₀ j * M + k vi₀ target := by
    simp [affineScore, v]
  have hforce : ∀ a, a ≠ target →
      affineScore (w vi₀) (k vi₀) v target >
        affineScore (w vi₀) (k vi₀) v a := by
    intro a ha
    have hother : affineScore (w vi₀) (k vi₀) v a = k vi₀ a := by
      simp [affineScore, v, ha]
    have hbound : |k vi₀ target - k vi₀ a| ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum (f := fun x => |k vi₀ target - k vi₀ x|)
        (fun x _ => abs_nonneg (k vi₀ target - k vi₀ x)) (Finset.mem_univ a)
    rw [htarget, hother, hM]
    have hneg := neg_abs_le (k vi₀ target - k vi₀ a)
    linarith
  by_contra hne
  have hstrict := hforce (slice f i₀ vi₀ v) hne
  have hmax := (hrep vi₀).2 v target
  linarith

namespace FixedAgentOffsetHelpers

private def bumpVal (vi₀ : A → Real) (c : A) (t : Real) : A → Real :=
  fun x => vi₀ x + if x = c then t else 0

private lemma bumpVal_apply_ne (vi₀ : A → Real) (c x : A) (t : Real)
    (h : x ≠ c) :
    bumpVal vi₀ c t x = vi₀ x := by
  unfold bumpVal
  rw [if_neg h]
  ring

private lemma bumpVal_add (vi₀ : A → Real) (c : A) (s t : Real) :
    bumpVal (bumpVal vi₀ c s) c t = bumpVal vi₀ c (s + t) := by
  funext x
  change (vi₀ x + (if x = c then s else 0)) + (if x = c then t else 0) =
    vi₀ x + (if x = c then s + t else 0)
  by_cases hx : x = c
  · simp only [if_pos hx]
    ring
  · simp only [if_neg hx]
    ring

end FixedAgentOffsetHelpers

private lemma weights_eq_of_pos_bump
    (f : Valuation N A → A) (hsmon : IsSMon f)
    (i₀ : N) (w : (A → Real) → N → Real) (k : (A → Real) → A → Real)
    (hrep : ∀ vi₀ : A → Real,
      (∀ i, 0 ≤ w vi₀ i) ∧
      (∀ v a, affineScore (w vi₀) (k vi₀) v (slice f i₀ vi₀ v) ≥
        affineScore (w vi₀) (k vi₀) v a))
    (hnorm : ∀ vi₀ : A → Real,
      Finset.univ.sum (fun i => w vi₀ i) = 1)
    (hA : 3 ≤ Fintype.card A)
    (vi₀ : A → Real) (c : A) (eps : Real) (heps : 0 < eps) :
    w (FixedAgentOffsetHelpers.bumpVal vi₀ c eps) = w vi₀ := by
  classical
  let vi₀' : A → Real := FixedAgentOffsetHelpers.bumpVal vi₀ c eps
  have hkey : ∀ v a b, slice f i₀ vi₀ v = a →
      slice f i₀ vi₀' v = b → a ≠ b → b = c := by
    intro v a b ha hb hab
    have hgap := hsmon i₀ v vi₀ vi₀' a b hab
      (by simpa [slice] using ha) (by simpa [slice] using hb)
    have hgap' : vi₀ a - vi₀ b >
        (vi₀ a + (if a = c then eps else 0)) -
          (vi₀ b + (if b = c then eps else 0)) := by
      simpa [vi₀', FixedAgentOffsetHelpers.bumpVal] using hgap
    have hpositive :
        (if b = c then eps else 0) - (if a = c then eps else 0) > 0 := by
      linarith
    by_contra hbnot
    by_cases hac : a = c
    · simp [hbnot, hac] at hpositive
      linarith
    · simp [hbnot, hac] at hpositive
  have hcard : 1 < Fintype.card A := by omega
  obtain ⟨altB, haltB⟩ := Fintype.exists_ne_of_one_lt_card hcard c
  obtain ⟨altA, haltA⟩ := Fintype.exists_ne_of_one_lt_card hcard altB
  let Tprime : Real := k vi₀' altB - k vi₀' altA
  let T : Real := k vi₀ altB - k vi₀ altA
  have hinclusion : ∀ z : N → Real,
      Finset.univ.sum (fun i => w vi₀' i * z i) < Tprime →
        Finset.univ.sum (fun i => w vi₀ i * z i) ≤ T := by
    intro z hz
    let p : N → Real := fun i => max (z i) 0
    let q : N → Real := fun i => max (-z i) 0
    have hpq : ∀ i, p i - q i = z i := by
      intro i
      dsimp [p, q]
      by_cases hzi : z i ≤ 0
      · rw [max_eq_right hzi, max_eq_left (neg_nonneg.mpr hzi)]
        simp
      · have hzi' : 0 ≤ z i := le_of_not_ge hzi
        rw [max_eq_left hzi', max_eq_right (neg_nonpos.mpr hzi')]
        simp
    let P : Real := Finset.univ.sum (fun i => w vi₀' i * p i)
    let Q : Real := Finset.univ.sum (fun i => w vi₀' i * q i)
    let M : Real :=
      (Finset.univ.sum (fun d => |k vi₀' d - k vi₀' altB - Q|)) + 1
    let v : Valuation N A := fun i x =>
      if x = altA then p i else if x = altB then q i else -M
    have haltBneA : altB ≠ altA := Ne.symm haltA
    have hvA : ∀ i, v i altA = p i := by
      intro i
      simp [v]
    have hvB : ∀ i, v i altB = q i := by
      intro i
      simp [v, haltBneA]
    have hqp (ww : N → Real) :
        Finset.univ.sum (fun i => ww i * q i) -
            Finset.univ.sum (fun i => ww i * p i) =
          -(Finset.univ.sum (fun i => ww i * z i)) := by
      calc
        Finset.univ.sum (fun i => ww i * q i) -
            Finset.univ.sum (fun i => ww i * p i) =
              Finset.univ.sum (fun i => ww i * q i - ww i * p i) := by
                rw [Finset.sum_sub_distrib]
        _ = Finset.univ.sum (fun i => -(ww i * z i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hqi : q i - p i = -z i := by linarith [hpq i]
          calc
            ww i * q i - ww i * p i = ww i * (q i - p i) := by ring
            _ = ww i * (-z i) := by rw [hqi]
            _ = -(ww i * z i) := by ring
        _ = -(Finset.univ.sum (fun i => ww i * z i)) := by
          rw [Finset.sum_neg_distrib]
    have hQminusP : Q - P = -(Finset.univ.sum (fun i => w vi₀' i * z i)) := by
      simpa [Q, P] using hqp (w vi₀')
    have hMbound (d : A) : k vi₀' d - k vi₀' altB - Q < M := by
      have hsingle : |k vi₀' d - k vi₀' altB - Q| ≤
          Finset.univ.sum (fun x => |k vi₀' x - k vi₀' altB - Q|) := by
        exact Finset.single_le_sum
          (f := fun x => |k vi₀' x - k vi₀' altB - Q|)
          (fun x hx => abs_nonneg (k vi₀' x - k vi₀' altB - Q))
          (Finset.mem_univ d)
      dsimp [M]
      have habs := le_abs_self (k vi₀' d - k vi₀' altB - Q)
      linarith
    have hscoreB : affineScore (w vi₀') (k vi₀') v altB = Q + k vi₀' altB := by
      simp only [affineScore, hvB, Q]
    have hscoreA : affineScore (w vi₀') (k vi₀') v altA = P + k vi₀' altA := by
      simp only [affineScore, hvA, P]
    have hBgtA : affineScore (w vi₀') (k vi₀') v altB >
        affineScore (w vi₀') (k vi₀') v altA := by
      have hgap : (Q + k vi₀' altB) - (P + k vi₀' altA) =
          Tprime - Finset.univ.sum (fun i => w vi₀' i * z i) := by
        dsimp [Q, P, Tprime]
        calc
          (Finset.univ.sum (fun i => w vi₀' i * q i) + k vi₀' altB) -
              (Finset.univ.sum (fun i => w vi₀' i * p i) + k vi₀' altA) =
              (Finset.univ.sum (fun i => w vi₀' i * q i) -
                Finset.univ.sum (fun i => w vi₀' i * p i)) +
                  (k vi₀' altB - k vi₀' altA) := by ring
          _ = k vi₀' altB - k vi₀' altA -
              Finset.univ.sum (fun i => w vi₀' i * z i) := by
                rw [hqp (w vi₀')]
                ring
      rw [hscoreB, hscoreA]
      linarith
    have hscoreD (d : A) (hda : d ≠ altA) (hdb : d ≠ altB) :
        affineScore (w vi₀') (k vi₀') v d = -M + k vi₀' d := by
      have hvD : ∀ i, v i d = -M := by
        intro i
        simp [v, hda, hdb]
      have hsumD : Finset.univ.sum (fun i => w vi₀' i * v i d) = -M := by
        calc
          Finset.univ.sum (fun i => w vi₀' i * v i d) =
              Finset.univ.sum (fun i => w vi₀' i * (-M)) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [hvD i]
          _ = (Finset.univ.sum (fun i => w vi₀' i)) * (-M) := by
            exact (Finset.sum_mul Finset.univ (fun i => w vi₀' i) (-M)).symm
          _ = -M := by rw [hnorm vi₀']; ring
      unfold affineScore
      rw [hsumD]
    have hBgtD (d : A) (hda : d ≠ altA) (hdb : d ≠ altB) :
        affineScore (w vi₀') (k vi₀') v altB >
          affineScore (w vi₀') (k vi₀') v d := by
      rw [hscoreB, hscoreD d hda hdb]
      have hMb := hMbound d
      linarith
    have hbumpwin : slice f i₀ vi₀' v = altB := by
      by_contra hneB
      have hmax := (hrep vi₀').2 v altB
      have hstrict : affineScore (w vi₀') (k vi₀') v altB >
          affineScore (w vi₀') (k vi₀') v (slice f i₀ vi₀' v) := by
        by_cases hsa : slice f i₀ vi₀' v = altA
        · rw [hsa]
          exact hBgtA
        · exact hBgtD (slice f i₀ vi₀' v) hsa hneB
      linarith
    have hsource : slice f i₀ vi₀ v = altB := by
      by_contra hsource
      have hc := hkey v (slice f i₀ vi₀ v) altB rfl hbumpwin hsource
      exact haltB hc
    have hscoreOldB : affineScore (w vi₀) (k vi₀) v altB =
        Finset.univ.sum (fun i => w vi₀ i * q i) + k vi₀ altB := by
      simp only [affineScore, hvB]
    have hscoreOldA : affineScore (w vi₀) (k vi₀) v altA =
        Finset.univ.sum (fun i => w vi₀ i * p i) + k vi₀ altA := by
      simp only [affineScore, hvA]
    have holdmax := (hrep vi₀).2 v altA
    rw [hsource, hscoreOldB, hscoreOldA] at holdmax
    have hqpOld := hqp (w vi₀)
    have hgapOld :
        (Finset.univ.sum (fun i => w vi₀ i * q i) + k vi₀ altB) -
          (Finset.univ.sum (fun i => w vi₀ i * p i) + k vi₀ altA) =
            T - Finset.univ.sum (fun i => w vi₀ i * z i) := by
      dsimp [T]
      calc
        (Finset.univ.sum (fun i => w vi₀ i * q i) + k vi₀ altB) -
            (Finset.univ.sum (fun i => w vi₀ i * p i) + k vi₀ altA) =
            (Finset.univ.sum (fun i => w vi₀ i * q i) -
              Finset.univ.sum (fun i => w vi₀ i * p i)) +
                (k vi₀ altB - k vi₀ altA) := by ring
        _ = k vi₀ altB - k vi₀ altA -
            Finset.univ.sum (fun i => w vi₀ i * z i) := by
              rw [hqpOld]
              ring
    linarith
  have hthreshold : ∀ z₀ : N → Real,
      0 < Finset.univ.sum (fun i => (-w vi₀' i) * z₀ i) →
        0 ≤ Finset.univ.sum (fun i => (-w vi₀ i) * z₀ i) := by
    intro z₀ hz
    by_contra hnot
    let Aold : Real := Finset.univ.sum (fun i => w vi₀ i * z₀ i)
    let Aprime : Real := Finset.univ.sum (fun i => w vi₀' i * z₀ i)
    have hnegdot (ww : N → Real) :
        Finset.univ.sum (fun i => (-ww i) * z₀ i) =
          -(Finset.univ.sum (fun i => ww i * z₀ i)) := by
      calc
        Finset.univ.sum (fun i => (-ww i) * z₀ i) =
            Finset.univ.sum (fun i => -(ww i * z₀ i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = -(Finset.univ.sum (fun i => ww i * z₀ i)) := by
          rw [Finset.sum_neg_distrib]
    have hApos : 0 < Aold := by
      have hneg : Finset.univ.sum (fun i => (-w vi₀ i) * z₀ i) < 0 :=
        lt_of_not_ge hnot
      rw [hnegdot (w vi₀)] at hneg
      linarith
    have hAprimeNeg : Aprime < 0 := by
      rw [hnegdot (w vi₀')] at hz
      change 0 < -Aprime at hz
      linarith
    let tau : Real := 1 + |T| / Aold + |Tprime| / (-Aprime)
    have hdivA : 0 ≤ |T| / Aold := div_nonneg (abs_nonneg _) (le_of_lt hApos)
    have hdivAprime : 0 ≤ |Tprime| / (-Aprime) :=
      div_nonneg (abs_nonneg _) (le_of_lt (by linarith))
    have htauA : |T| / Aold < tau := by
      dsimp [tau]
      linarith
    have htauPrime : |Tprime| / (-Aprime) < tau := by
      dsimp [tau]
      linarith
    have hlargeA : |T| < tau * Aold := by
      have hmul := mul_lt_mul_of_pos_right htauA hApos
      have hcancel := div_mul_cancel₀ |T| (ne_of_gt hApos)
      nlinarith
    have hlargePrime : |Tprime| < tau * (-Aprime) := by
      have hden : 0 < -Aprime := by linarith
      have hmul := mul_lt_mul_of_pos_right htauPrime hden
      have hcancel := div_mul_cancel₀ |Tprime| (ne_of_gt hden)
      nlinarith
    let z₁ : N → Real := fun i => tau * z₀ i
    have hscalePrime : Finset.univ.sum (fun i => w vi₀' i * z₁ i) =
        tau * Aprime := by
      calc
        Finset.univ.sum (fun i => w vi₀' i * z₁ i) =
            Finset.univ.sum (fun i => tau * (w vi₀' i * z₀ i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              dsimp [z₁]
              ring
        _ = tau * Finset.univ.sum (fun i => w vi₀' i * z₀ i) := by
          exact (Finset.mul_sum Finset.univ
            (fun i => w vi₀' i * z₀ i) tau).symm
        _ = tau * Aprime := by rfl
    have hz₁ : Finset.univ.sum (fun i => w vi₀' i * z₁ i) < Tprime := by
      rw [hscalePrime]
      have hnegT : -|Tprime| ≤ Tprime := neg_abs_le Tprime
      nlinarith
    have hinc := hinclusion z₁ hz₁
    have hscaleOld : Finset.univ.sum (fun i => w vi₀ i * z₁ i) =
        tau * Aold := by
      calc
        Finset.univ.sum (fun i => w vi₀ i * z₁ i) =
            Finset.univ.sum (fun i => tau * (w vi₀ i * z₀ i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              dsimp [z₁]
              ring
        _ = tau * Finset.univ.sum (fun i => w vi₀ i * z₀ i) := by
          exact (Finset.mul_sum Finset.univ
            (fun i => w vi₀ i * z₀ i) tau).symm
        _ = tau * Aold := by rfl
    rw [hscaleOld] at hinc
    have habsT : T ≤ |T| := le_abs_self T
    linarith
  have hu'ne : (fun i => -w vi₀' i) ≠ 0 := by
    intro hzero
    have hwzero : w vi₀' = 0 := by
      funext i
      have hi : -w vi₀' i = 0 := by simpa using congrFun hzero i
      exact neg_eq_zero.mp hi
    have hsumzero : Finset.univ.sum (fun i => w vi₀' i) = 0 := by
      simp [hwzero]
    have hone := hnorm vi₀'
    rw [hsumzero] at hone
    norm_num at hone
  obtain ⟨alpha, halpha, hscaled⟩ :=
    halfspace_homog (fun i => -w vi₀ i) (fun i => -w vi₀' i) hu'ne hthreshold
  have hweights : ∀ i, w vi₀ i = alpha * w vi₀' i := by
    intro i
    have hi := hscaled i
    linarith
  have hsum : Finset.univ.sum (fun i => w vi₀ i) =
      alpha * Finset.univ.sum (fun i => w vi₀' i) := by
    calc
      Finset.univ.sum (fun i => w vi₀ i) =
          Finset.univ.sum (fun i => alpha * w vi₀' i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hweights i]
      _ = alpha * Finset.univ.sum (fun i => w vi₀' i) := by
        exact (Finset.mul_sum Finset.univ (fun i => w vi₀' i) alpha).symm
  have halphaone : alpha = 1 := by
    rw [hnorm vi₀, hnorm vi₀'] at hsum
    nlinarith
  funext i
  rw [hweights i, halphaone]
  ring

private lemma weights_eq_upper
    (f : Valuation N A → A) (hsmon : IsSMon f)
    (i₀ : N) (w : (A → Real) → N → Real) (k : (A → Real) → A → Real)
    (hrep : ∀ vi₀ : A → Real,
      (∀ i, 0 ≤ w vi₀ i) ∧
      (∀ v a, affineScore (w vi₀) (k vi₀) v (slice f i₀ vi₀ v) ≥
        affineScore (w vi₀) (k vi₀) v a))
    (hnorm : ∀ vi₀ : A → Real,
      Finset.univ.sum (fun i => w vi₀ i) = 1)
    (hA : 3 ≤ Fintype.card A)
    (base u : A → Real) (hle : ∀ a, base a ≤ u a) :
    w u = w base := by
  classical
  have hclaim (s : Finset A) :
      w (fun a => if a ∈ s then u a else base a) = w base := by
    induction s using Finset.induction with
    | empty =>
        have heq : (fun a => if a ∈ (∅ : Finset A) then u a else base a) = base := by
          funext a
          simp
        rw [heq]
    | @insert c t hc ih =>
        let vt : A → Real := fun a => if a ∈ t then u a else base a
        have hsplit : (fun a => if a ∈ insert c t then u a else base a) =
            FixedAgentOffsetHelpers.bumpVal vt c (u c - base c) := by
          funext a
          by_cases hac : a = c
          · subst a
            simp [vt, FixedAgentOffsetHelpers.bumpVal, hc]
          · simp [vt, FixedAgentOffsetHelpers.bumpVal, hac]
        by_cases hdelta : u c - base c = 0
        · have hbumpeq :
              FixedAgentOffsetHelpers.bumpVal vt c (u c - base c) = vt := by
            funext a
            simp [FixedAgentOffsetHelpers.bumpVal, hdelta]
          rw [hsplit, hbumpeq]
          exact ih
        · have hnonneg : 0 ≤ u c - base c := by linarith [hle c]
          have hpos : 0 < u c - base c :=
            lt_of_le_of_ne hnonneg (Ne.symm hdelta)
          have hbump := weights_eq_of_pos_bump f hsmon i₀ w k hrep hnorm hA
            vt c (u c - base c) hpos
          rw [hsplit]
          exact hbump.trans ih
  have huniv := hclaim Finset.univ
  have heq : (fun a => if a ∈ Finset.univ then u a else base a) = u := by
    funext a
    simp
  rw [heq] at huniv
  exact huniv

/-- Lemma 9 (Dobzinski-Nisan, weight independence): in the induction step for n ≥ 3,
    the affine weights of the sliced (n-1)-agent problems do not depend on the fixed
    agent's valuation. If all agents other than i₀ have no veto power and f is S-MON,
    then for any choice of per-slice affine representations, the weights of agents
    i ≠ i₀ are independent of i₀'s fixed valuation. -/
lemma weights_independent_of_fixed_agent
    (f : Valuation N A → A) (hsmon : IsSMon f)
    (i₀ : N) (hveto : ∀ i, i ≠ i₀ → HasNoVetoPower f i)
    (hA : 3 ≤ Fintype.card A)
    (w : (A → Real) → N → Real) (k : (A → Real) → A → Real)
    (hrep : ∀ vi₀ : A → Real,
      (∀ i, 0 ≤ w vi₀ i) ∧
      (∀ v a, affineScore (w vi₀) (k vi₀) v (slice f i₀ vi₀ v) ≥
        affineScore (w vi₀) (k vi₀) v a))
    (hnorm : ∀ vi₀ : A → Real,
      Finset.univ.sum (fun i => w vi₀ i) = 1) :
    ∀ vi₀ vi₀' i, i ≠ i₀ → w vi₀ i = w vi₀' i := by
  classical
  intro vi₀ vi₀' i hi
  let u : A → Real := fun a => max (vi₀ a) (vi₀' a) + 1
  have hle₁ : ∀ a, vi₀ a ≤ u a := by
    intro a
    dsimp [u]
    have hmax := le_max_left (vi₀ a) (vi₀' a)
    linarith
  have hle₂ : ∀ a, vi₀' a ≤ u a := by
    intro a
    dsimp [u]
    have hmax := le_max_left (vi₀' a) (vi₀ a)
    rw [max_comm] at hmax
    linarith
  have hupper₁ := weights_eq_upper f hsmon i₀ w k hrep hnorm hA vi₀ u hle₁
  have hupper₂ := weights_eq_upper f hsmon i₀ w k hrep hnorm hA vi₀' u hle₂
  have hweights : w vi₀ = w vi₀' := hupper₁.symm.trans hupper₂
  rw [hweights]

private lemma affineScore_update_input_bump_diff
    (weights : N → Real) (offset : A → Real) (v : Valuation N A)
    (i₀ : N) (a b : A) (t : Real) (hab : a ≠ b) :
    affineScore weights offset
        (Function.update v i₀ (fun x => v i₀ x + if x = a then t else 0)) a -
      affineScore weights offset
        (Function.update v i₀ (fun x => v i₀ x + if x = a then t else 0)) b =
    (affineScore weights offset v a - affineScore weights offset v b) + weights i₀ * t := by
  classical
  have hsumA :
      (Finset.univ.sum fun i => weights i *
          (Function.update v i₀ (fun x => v i₀ x + if x = a then t else 0)) i a) =
        (Finset.univ.sum fun i => weights i * v i a) + weights i₀ * t := by
    have hterm : ∀ i, weights i *
        (Function.update v i₀ (fun x => v i₀ x + if x = a then t else 0)) i a =
          weights i * v i a + (if i = i₀ then weights i₀ * t else 0) := by
      intro i
      by_cases hi : i = i₀
      · subst i
        simp only [Function.update_self, if_pos]
        ring
      · simp [Function.update_of_ne hi, hi]
    calc
      _ = Finset.univ.sum (fun i =>
          weights i * v i a + (if i = i₀ then weights i₀ * t else 0)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hterm i
      _ = (Finset.univ.sum fun i => weights i * v i a) + weights i₀ * t := by
        rw [Finset.sum_add_distrib]
        have hite : Finset.univ.sum
            (fun i : N => if i = i₀ then weights i₀ * t else 0) = weights i₀ * t := by
          rw [Finset.sum_eq_single i₀]
          · simp
          · intro i hi hne
            simp [hne]
          · simp
        rw [hite]
  have hsumB :
      (Finset.univ.sum fun i => weights i *
          (Function.update v i₀ (fun x => v i₀ x + if x = a then t else 0)) i b) =
        Finset.univ.sum (fun i => weights i * v i b) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = i₀
    · subst i
      simp only [Function.update_self, if_neg (Ne.symm hab)]
      ring
    · simp [Function.update_of_ne hi]
  unfold affineScore
  rw [hsumA, hsumB]
  ring

private def onlyAgentProfile (j : N) (z : A → Real) : Valuation N A :=
  fun i a => if i = j then z a else 0

private lemma affineScore_onlyAgentProfile
    (weights : N → Real) (offset : A → Real) (j : N)
    (z : A → Real) (a : A) :
    affineScore weights offset (onlyAgentProfile j z) a =
      weights j * z a + offset a := by
  classical
  unfold affineScore onlyAgentProfile
  have hsum : Finset.univ.sum
      (fun i => weights i * (if i = j then z a else 0)) = weights j * z a := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hne
      simp [hne]
    · simp
  rw [hsum]

private lemma pair_offset_order_of_fixed_smon
    (f : Valuation N A → A) (hsmon : IsSMon f) (i₀ j : N) (hj : j ≠ i₀)
    (w : (A → Real) → N → Real) (k : (A → Real) → A → Real)
    (hrep : ∀ vi₀ : A → Real,
      (∀ i, 0 ≤ w vi₀ i) ∧
      (∀ v a, affineScore (w vi₀) (k vi₀) v (slice f i₀ vi₀ v) ≥
        affineScore (w vi₀) (k vi₀) v a))
    (hwind : ∀ vi₀ vi₀' i, i ≠ i₀ → w vi₀ i = w vi₀' i)
    (hpos : ∀ vi₀, 0 < w vi₀ j)
    (vi₀ vi₀' : A → Real) (a b : A) (hab : a ≠ b)
    (hT : k vi₀ a - k vi₀ b > k vi₀' a - k vi₀' b) :
    vi₀ a - vi₀ b > vi₀' a - vi₀' b := by
  classical
  let W : Real := w vi₀ j
  let T : Real := k vi₀ a - k vi₀ b
  let T' : Real := k vi₀' a - k vi₀' b
  let r : Real := -(T + T') / (2 * W)
  let D : Real := |W * r| + |k vi₀ a| + |k vi₀ b| + |k vi₀' a| + |k vi₀' b|
  let z : A → Real := fun c =>
    if c = a then r else if c = b then 0 else
      -(D + |k vi₀ c| + |k vi₀' c| + 1) / W
  let v : Valuation N A := onlyAgentProfile j z
  have hWpos : 0 < W := hpos vi₀
  have hWne : W ≠ 0 := ne_of_gt hWpos
  have hW' : w vi₀' j = W := by
    dsimp [W]
    exact hwind vi₀' vi₀ j hj
  have hWr : W * r = -(T + T') / 2 := by
    dsimp [r]
    field_simp [hWne]
  have hza : z a = r := by simp [z]
  have hzb : z b = 0 := by simp [z, Ne.symm hab]
  have hpa : affineScore (w vi₀) (k vi₀) v a = W * r + k vi₀ a := by
    rw [affineScore_onlyAgentProfile, hza]
  have hpb : affineScore (w vi₀) (k vi₀) v b = k vi₀ b := by
    rw [affineScore_onlyAgentProfile, hzb]
    simp [W]
  have hqa : affineScore (w vi₀') (k vi₀') v a = W * r + k vi₀' a := by
    rw [affineScore_onlyAgentProfile, hza, hW']
  have hqb : affineScore (w vi₀') (k vi₀') v b = k vi₀' b := by
    rw [affineScore_onlyAgentProfile, hzb, hW']
    ring
  have hpDiff :
      affineScore (w vi₀) (k vi₀) v a - affineScore (w vi₀) (k vi₀) v b =
        (T - T') / 2 := by
    rw [hpa, hpb, hWr]
    dsimp [T, T']
    ring
  have hqDiff :
      affineScore (w vi₀') (k vi₀') v b - affineScore (w vi₀') (k vi₀') v a =
        (T - T') / 2 := by
    rw [hqa, hqb, hWr]
    dsimp [T, T']
    ring
  have hmargin : 0 < (T - T') / 2 := by
    apply div_pos
    · exact sub_pos.mpr (by simpa [T, T'] using hT)
    · norm_num
  have hpaLower : -D ≤ affineScore (w vi₀) (k vi₀) v a := by
    rw [hpa]
    dsimp [D]
    linarith [neg_abs_le (W * r), neg_abs_le (k vi₀ a),
      abs_nonneg (k vi₀ b), abs_nonneg (k vi₀' a), abs_nonneg (k vi₀' b)]
  have hpbLower : -D ≤ affineScore (w vi₀) (k vi₀) v b := by
    rw [hpb]
    dsimp [D]
    linarith [neg_abs_le (k vi₀ b), abs_nonneg (W * r), abs_nonneg (k vi₀ a),
      abs_nonneg (k vi₀' a), abs_nonneg (k vi₀' b)]
  have hqaLower : -D ≤ affineScore (w vi₀') (k vi₀') v a := by
    rw [hqa]
    dsimp [D]
    linarith [neg_abs_le (W * r), neg_abs_le (k vi₀' a),
      abs_nonneg (k vi₀ a), abs_nonneg (k vi₀ b), abs_nonneg (k vi₀' b)]
  have hqbLower : -D ≤ affineScore (w vi₀') (k vi₀') v b := by
    rw [hqb]
    dsimp [D]
    linarith [neg_abs_le (k vi₀' b), abs_nonneg (W * r), abs_nonneg (k vi₀ a),
      abs_nonneg (k vi₀ b), abs_nonneg (k vi₀' a)]
  have hlow (c : A) (hca : c ≠ a) (hcb : c ≠ b) :
      affineScore (w vi₀) (k vi₀) v c ≤ -D - 1 ∧
        affineScore (w vi₀') (k vi₀') v c ≤ -D - 1 := by
    have hzc : z c = -(D + |k vi₀ c| + |k vi₀' c| + 1) / W := by
      simp [z, hca, hcb]
    have hmulp : W * z c = -(D + |k vi₀ c| + |k vi₀' c| + 1) := by
      rw [hzc]
      exact mul_div_cancel₀ _ hWne
    have hmulq : w vi₀' j * z c =
        -(D + |k vi₀ c| + |k vi₀' c| + 1) := by
      rw [hW', hzc]
      exact mul_div_cancel₀ _ hWne
    constructor
    · rw [affineScore_onlyAgentProfile, hmulp]
      linarith [le_abs_self (k vi₀ c), abs_nonneg (k vi₀' c)]
    · rw [affineScore_onlyAgentProfile, hmulq]
      linarith [le_abs_self (k vi₀' c), abs_nonneg (k vi₀ c)]
  have hstrict₀ : ∀ c, c ≠ a →
      affineScore (w vi₀) (k vi₀) v a > affineScore (w vi₀) (k vi₀) v c := by
    intro c hca
    by_cases hcb : c = b
    · subst c
      linarith [hpDiff]
    · have hc := (hlow c hca hcb).1
      linarith [hpaLower]
  have hstrict₀' : ∀ c, c ≠ b →
      affineScore (w vi₀') (k vi₀') v b > affineScore (w vi₀') (k vi₀') v c := by
    intro c hcb
    by_cases hca : c = a
    · subst c
      linarith [hqDiff]
    · have hc := (hlow c hca hcb).2
      linarith [hqbLower]
  have hwin₀ : slice f i₀ vi₀ v = a := by
    by_contra hne
    have hstrict := hstrict₀ (slice f i₀ vi₀ v) hne
    have hmax := (hrep vi₀).2 v a
    linarith
  have hwin₀' : slice f i₀ vi₀' v = b := by
    by_contra hne
    have hstrict := hstrict₀' (slice f i₀ vi₀' v) hne
    have hmax := (hrep vi₀').2 v b
    linarith
  exact hsmon i₀ v vi₀ vi₀' a b hab
    (by simpa [slice] using hwin₀) (by simpa [slice] using hwin₀')

private lemma pair_offset_eq_of_equal_gap
    (f : Valuation N A → A) (hsmon : IsSMon f) (i₀ j : N) (hj : j ≠ i₀)
    (w : (A → Real) → N → Real) (k : (A → Real) → A → Real)
    (hrep : ∀ vi₀ : A → Real,
      (∀ i, 0 ≤ w vi₀ i) ∧
      (∀ v a, affineScore (w vi₀) (k vi₀) v (slice f i₀ vi₀ v) ≥
        affineScore (w vi₀) (k vi₀) v a))
    (hwind : ∀ vi₀ vi₀' i, i ≠ i₀ → w vi₀ i = w vi₀' i)
    (hpos : ∀ vi₀, 0 < w vi₀ j)
    (vi₀ vi₀' : A → Real) (a b : A) (hab : a ≠ b)
    (hgap : vi₀ a - vi₀ b = vi₀' a - vi₀' b) :
    k vi₀ a - k vi₀ b = k vi₀' a - k vi₀' b := by
  by_contra hneq
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have hrev := pair_offset_order_of_fixed_smon f hsmon i₀ j hj w k hrep hwind hpos
      vi₀' vi₀ a b hab (by linarith)
    linarith
  · have hforw := pair_offset_order_of_fixed_smon f hsmon i₀ j hj w k hrep hwind hpos
      vi₀ vi₀' a b hab hgt
    linarith

#check weight_pos_of_hnd
#check slice_force_via_j
#check FixedAgentOffsetHelpers.bumpVal_apply_ne
#check FixedAgentOffsetHelpers.bumpVal_add
#check affineScore_update_input_bump_diff
#check affineScore_onlyAgentProfile
#check pair_offset_order_of_fixed_smon
#check pair_offset_eq_of_equal_gap
#check additive_mono_linear
#check Roberts.exists_ne_ne
#check Fintype.exists_ne_of_one_lt_card

/-- Lemma 10 (Dobzinski-Nisan, offset consistency): in the induction step for n ≥ 3,
    once weights are independent of the fixed agent's valuation, the offsets are
    consistent up to a common additive constant: k(vi₀) a - k(vi₀) b does not depend
    on vi₀. Uses S-MON and no-veto to transfer the affine representation across
    different fixed valuations of i₀. -/
private lemma offsets_consistent_of_fixed_agent_core
    (f : Valuation N A → A) (hsmon : IsSMon f)
    (i₀ : N) (hA : 3 ≤ Fintype.card A)
    (w : (A → Real) → N → Real) (k : (A → Real) → A → Real)
    (hrep : ∀ vi₀ : A → Real,
      (∀ i, 0 ≤ w vi₀ i) ∧
      (∀ v a, affineScore (w vi₀) (k vi₀) v (slice f i₀ vi₀ v) ≥
        affineScore (w vi₀) (k vi₀) v a))
    (hwind : ∀ vi₀ vi₀' i, i ≠ i₀ → w vi₀ i = w vi₀' i)
    (hnd : ∃ i, i ≠ i₀ ∧ ∃ vi₀, 0 < w vi₀ i) :
    ∃ α : Real, 0 ≤ α ∧ ∀ vi₀ vi₀' a b,
      (k vi₀ a - α * vi₀ a) - (k vi₀ b - α * vi₀ b) =
      (k vi₀' a - α * vi₀' a) - (k vi₀' b - α * vi₀' b) := by
  /-
  Reformulated: the slice offsets depend affinely on the fixed valuation.
  In a global affine maximizer with weight α on i₀, the slice offset is
  k vi₀ a = K a + α * vi₀ a for a global K. Hence (k vi₀ a - α * vi₀ a)
  has pairwise differences independent of vi₀. The α is the weight on i₀,
  identified via the switching thresholds. The dictator case (where slices
  are constant) must be separated before applying this.
  -/
  classical
  obtain ⟨j, hj, hpos⟩ := weight_pos_of_hnd i₀ w hwind hnd
  have _honto : ∀ vi₀ target, ∃ v, slice f i₀ vi₀ v = target := by
    intro vi₀ target
    exact slice_force_via_j f i₀ j hj w k hrep hpos vi₀ target
  let gapProfile : A → Real → A → Real := fun a t c => if c = a then t else 0
  let phi : A → A → Real → Real := fun a b t =>
    k (gapProfile a t) a - k (gapProfile a t) b
  let response : A → A → Real → Real := fun a b t => phi a b t - phi a b 0
  have hrepr (x : A → Real) (a b : A) (hab : a ≠ b) :
      k x a - k x b = phi a b (x a - x b) := by
    have hgap : x a - x b = gapProfile a (x a - x b) a -
        gapProfile a (x a - x b) b := by
      simp [gapProfile, Ne.symm hab]
    have heq := pair_offset_eq_of_equal_gap f hsmon i₀ j hj w k hrep hwind hpos
      x (gapProfile a (x a - x b)) a b hab hgap
    simpa [phi] using heq
  have hphiTri (a b c : A) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
      (s t : Real) : phi a b s + phi b c t = phi a c (s + t) := by
    let x : A → Real := fun d => if d = a then s + t else if d = b then t else 0
    have hxa : x a = s + t := by simp [x]
    have hxb : x b = t := by simp [x, Ne.symm hab]
    have hxc : x c = 0 := by simp [x, Ne.symm hac, Ne.symm hbc]
    have hgap₁ : x a - x b = s := by rw [hxa, hxb]; ring
    have hgap₂ : x b - x c = t := by rw [hxb, hxc]; ring
    have hgap₃ : x a - x c = s + t := by rw [hxa, hxc]; ring
    have h₁ : phi a b s = k x a - k x b := by
      rw [← hgap₁]
      exact (hrepr x a b hab).symm
    have h₂ : phi b c t = k x b - k x c := by
      rw [← hgap₂]
      exact (hrepr x b c hbc).symm
    have h₃ : phi a c (s + t) = k x a - k x c := by
      rw [← hgap₃]
      exact (hrepr x a c hac).symm
    calc
      phi a b s + phi b c t = (k x a - k x b) + (k x b - k x c) := by rw [h₁, h₂]
      _ = k x a - k x c := by ring
      _ = phi a c (s + t) := h₃.symm
  have hresponseTri (a b c : A) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
      (s t : Real) : response a b s + response b c t = response a c (s + t) := by
    have h := hphiTri a b c hab hbc hac s t
    have h0 := hphiTri a b c hab hbc hac 0 0
    dsimp [response]
    have hzero : phi a b 0 + phi b c 0 = phi a c 0 := by simpa using h0
    calc
      _ = (phi a b s + phi b c t) - (phi a b 0 + phi b c 0) := by ring
      _ = phi a c (s + t) - phi a c 0 := by rw [h, hzero]
      _ = _ := rfl
  have hresponseABAC (a b c : A) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
      (t : Real) : response a b t = response a c t := by
    have h := hresponseTri a b c hab hbc hac t 0
    have hz : response b c 0 = 0 := by simp [response]
    rw [hz, add_zero] at h
    simpa using h
  have hresponseBCAC (a b c : A) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
      (t : Real) : response b c t = response a c t := by
    have h := hresponseTri a b c hab hbc hac 0 t
    have hz : response a b 0 = 0 := by dsimp [response]; ring
    rw [hz, zero_add] at h
    simpa using h
  obtain ⟨baseB⟩ := (inferInstance : Nonempty A)
  have hcard : 1 < Fintype.card A := by omega
  obtain ⟨baseA, hbaseA⟩ := Fintype.exists_ne_of_one_lt_card hcard baseB
  let F : Real → Real := response baseA baseB
  have hresponseFromRef (a : A) (ha : a ≠ baseB) (t : Real) :
      response a baseB t = F t := by
    by_cases haa : a = baseA
    · subst a
      rfl
    · have h := hresponseBCAC a baseA baseB haa hbaseA ha t
      dsimp [F]
      exact h.symm
  have hresponseReverse (a b : A) (hab : a ≠ b) (t : Real) :
      response a b t = response b a t := by
    obtain ⟨c, hca, hcb⟩ := Roberts.exists_ne_ne hab hA
    have h₁ := hresponseABAC a b c hab (Ne.symm hcb) (Ne.symm hca) t
    have h₂ := hresponseBCAC a b c hab (Ne.symm hcb) (Ne.symm hca) t
    have h₃ := hresponseABAC b a c (Ne.symm hab) (Ne.symm hca) (Ne.symm hcb) t
    calc
      response a b t = response a c t := h₁
      _ = response b c t := h₂.symm
      _ = response b a t := h₃.symm
  have hresponseCommon (a b : A) (hab : a ≠ b) (t : Real) :
      response a b t = F t := by
    by_cases hb : b = baseB
    · subst b
      exact hresponseFromRef a hab t
    · by_cases ha : a = baseB
      · subst a
        calc
          response baseB b t = response b baseB t := hresponseReverse baseB b hab t
          _ = F t := hresponseFromRef b hb t
      · calc
          response a b t = response a baseB t :=
            hresponseABAC a b baseB hab hb ha t
          _ = F t := hresponseFromRef a ha t
  have hphiMono (a b : A) (hab : a ≠ b) (s t : Real) (hst : s ≤ t) :
      phi a b s ≤ phi a b t := by
    by_contra hnot
    have hT : phi a b s > phi a b t := lt_of_not_ge hnot
    have hSgap : gapProfile a s a - gapProfile a s b = s := by
      simp [gapProfile, Ne.symm hab]
    have hTgap : gapProfile a t a - gapProfile a t b = t := by
      simp [gapProfile, Ne.symm hab]
    have hstrict := pair_offset_order_of_fixed_smon f hsmon i₀ j hj w k hrep hwind hpos
      (gapProfile a s) (gapProfile a t) a b hab (by simpa [phi] using hT)
    rw [hSgap, hTgap] at hstrict
    linarith
  have hresponseMono : ∀ δ γ : Real, δ ≥ γ → F δ ≥ F γ := by
    intro δ γ hδγ
    have h := hphiMono baseA baseB hbaseA γ δ hδγ
    dsimp [F, response] at h ⊢
    linarith
  obtain ⟨third, hthirdA, hthirdB⟩ := Roberts.exists_ne_ne hbaseA hA
  have hresponseAdd : ∀ s t : Real, F (s + t) = F s + F t := by
    intro s t
    have h := hresponseTri baseA baseB third hbaseA (Ne.symm hthirdB)
      (Ne.symm hthirdA) s t
    have hs := hresponseCommon baseA baseB hbaseA s
    have ht := hresponseCommon baseB third (Ne.symm hthirdB) t
    have hst := hresponseCommon baseA third (Ne.symm hthirdA) (s + t)
    rw [hs, ht, hst] at h
    linarith
  let l : Real → Real := fun t => -F t
  have hadd : ∀ δ γ : Real, l (δ + γ) = l δ + l γ := by
    intro δ γ
    dsimp [l]
    rw [hresponseAdd]
    ring
  have hmono : ∀ δ γ : Real, δ ≥ γ → l δ ≤ l γ := by
    intro δ γ hδγ
    have h := hresponseMono δ γ hδγ
    dsimp [l]
    linarith
  let α : Real := F 1
  have hlinear : ∀ t : Real, F t = α * t := by
    intro t
    have h := additive_mono_linear hadd hmono t
    dsimp [l, α] at h
    linarith
  have hαnonneg : 0 ≤ α := by
    have h := hresponseMono 1 0 (by norm_num)
    have hFzero : F 0 = 0 := by simp [F, response]
    dsimp [α]
    linarith
  refine ⟨α, hαnonneg, ?_⟩
  intro vi₀ vi₀' a b
  by_cases hab : a = b
  · subst b
    ring
  · have hleftRep := hrepr vi₀ a b hab
    have hrightRep := hrepr vi₀' a b hab
    have hleftPhi : phi a b (vi₀ a - vi₀ b) =
        phi a b 0 + α * (vi₀ a - vi₀ b) := by
      have h := hresponseCommon a b hab (vi₀ a - vi₀ b)
      have hlin := hlinear (vi₀ a - vi₀ b)
      dsimp [response] at h
      rw [hlin] at h
      linarith
    have hrightPhi : phi a b (vi₀' a - vi₀' b) =
        phi a b 0 + α * (vi₀' a - vi₀' b) := by
      have h := hresponseCommon a b hab (vi₀' a - vi₀' b)
      have hlin := hlinear (vi₀' a - vi₀' b)
      dsimp [response] at h
      rw [hlin] at h
      linarith
    have hleft : (k vi₀ a - α * vi₀ a) - (k vi₀ b - α * vi₀ b) = phi a b 0 := by
      calc
        _ = (k vi₀ a - k vi₀ b) - α * (vi₀ a - vi₀ b) := by ring
        _ = phi a b (vi₀ a - vi₀ b) - α * (vi₀ a - vi₀ b) := by rw [hleftRep]
        _ = phi a b 0 := by rw [hleftPhi]; ring
    have hright : (k vi₀' a - α * vi₀' a) - (k vi₀' b - α * vi₀' b) = phi a b 0 := by
      calc
        _ = (k vi₀' a - k vi₀' b) - α * (vi₀' a - vi₀' b) := by ring
        _ = phi a b (vi₀' a - vi₀' b) - α * (vi₀' a - vi₀' b) := by rw [hrightRep]
        _ = phi a b 0 := by rw [hrightPhi]; ring
    rw [hleft, hright]

/-- Lemma 10 (Dobzinski-Nisan, offset consistency), with its original
    no-veto hypotheses. The proof only needs the affine slice representations,
    their weight independence, and a positive weight away from the fixed agent. -/
lemma offsets_consistent_of_fixed_agent
    (f : Valuation N A → A) (hsmon : IsSMon f)
    (i₀ : N) (hveto : ∀ i, i ≠ i₀ → HasNoVetoPower f i)
    (hA : 3 ≤ Fintype.card A)
    (w : (A → Real) → N → Real) (k : (A → Real) → A → Real)
    (hrep : ∀ vi₀ : A → Real,
      (∀ i, 0 ≤ w vi₀ i) ∧
      (∀ v a, affineScore (w vi₀) (k vi₀) v (slice f i₀ vi₀ v) ≥
        affineScore (w vi₀) (k vi₀) v a))
    (hwind : ∀ vi₀ vi₀' i, i ≠ i₀ → w vi₀ i = w vi₀' i)
    (hnd : ∃ i, i ≠ i₀ ∧ ∃ vi₀, 0 < w vi₀ i) :
    ∃ α : Real, ∀ vi₀ vi₀' a b,
      (k vi₀ a - α * vi₀ a) - (k vi₀ b - α * vi₀ b) =
      (k vi₀' a - α * vi₀' a) - (k vi₀' b - α * vi₀' b) := by
  obtain ⟨alpha, _, hoff⟩ :=
    offsets_consistent_of_fixed_agent_core f hsmon i₀ hA w k hrep hwind hnd
  exact ⟨alpha, hoff⟩

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
        have h3 : 3 ≤ Fintype.card N := by
          have hpos : 1 ≤ Fintype.card N := Fintype.card_pos
          omega
        obtain ⟨exceptional, hexceptional⟩ :=
          all_but_one_no_veto M.choiceFn hsmon honto hA
        obtain ⟨i₀, hi₀exceptional⟩ :=
          Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card N) exceptional
        have hi₀exceptional' : i₀ ≠ exceptional := hi₀exceptional
        have hnv₀ : HasNoVetoPower M.choiceFn i₀ :=
          hexceptional i₀ hi₀exceptional'

        let N' := {i : N // i ∈ Finset.univ.erase i₀}
        letI : Fintype N' := ⟨(Finset.univ.erase i₀).attach, by
          intro i
          exact Finset.mem_attach _ i⟩
        letI : Nonempty N' := ⟨⟨exceptional, by
          simpa using hi₀exceptional'.symm⟩⟩
        have hcardN' : Fintype.card N' + 1 = Fintype.card N := by
          calc
            Fintype.card N' + 1 = (Finset.univ.erase i₀).card + 1 := by
              rw [Fintype.card_coe]
            _ = Finset.univ.card := Finset.card_erase_add_one (Finset.mem_univ i₀)
            _ = Fintype.card N := by simp
        have hle' : Fintype.card N' ≤ k := by omega

        let extendProfile (fixed : A → Real) (v : Valuation N' A) : Valuation N A :=
          fun i a => if hi : i = i₀ then fixed a else
            v ⟨i, by simp [Finset.mem_erase, hi]⟩ a
        let restrictProfile (v : Valuation N A) : Valuation N' A :=
          fun i => v i.1
        have subtype_ne (i : N') : i.1 ≠ i₀ := by
          simpa using (Finset.mem_erase.mp i.2).1
        have hextend_update (fixed : A → Real) (v : Valuation N' A)
            (i : N') (vi : A → Real) :
            extendProfile fixed (Function.update v i vi) =
              Function.update (extendProfile fixed v) i.1 vi := by
          funext j a
          by_cases hji : j = i.1
          · subst j
            simp [extendProfile, subtype_ne i]
          · by_cases h₀j : j = i₀
            · subst j
              simp [extendProfile, Ne.symm (subtype_ne i), hji]
            · have hsub : (⟨j, by simp [h₀j]⟩ : N') ≠ i := by
                intro heq
                exact hji (congrArg Subtype.val heq)
              simp [extendProfile, hji, h₀j, hsub]
        have hextend_restrict (fixed : A → Real) (v : Valuation N A) :
            extendProfile fixed (restrictProfile v) = Function.update v i₀ fixed := by
          funext j a
          by_cases hj : j = i₀
          · subst j
            simp [extendProfile, restrictProfile]
          · simp [extendProfile, restrictProfile, hj, Function.update_of_ne (Ne.symm hj)]

        let slicedMechanism (fixed : A → Real) : Mechanism N' A :=
          ⟨fun v => M.choiceFn (extendProfile fixed v),
            fun v i => M.pay (extendProfile fixed v) i.1⟩
        have hdsicSlice (fixed : A → Real) : IsDSIC (slicedMechanism fixed) := by
          intro i v vi2
          have hiReport : (extendProfile fixed v) i.1 = v i := by
            funext a
            simp [extendProfile, subtype_ne i]
          let utility (p : Valuation N A) : Real :=
            v i (M.choiceFn p) - M.pay p i.1
          have h := hdsic i.1 (extendProfile fixed v) vi2
          -- Bridge the DecidableEq instance mismatch: h uses Classical.propDecidable
          have hUpdateInst :
              (@Function.update N _ (fun a b => Classical.propDecidable (a = b)) (extendProfile fixed v) i.1 vi2) =
              (Function.update (extendProfile fixed v) i.1 vi2) := by
            funext j a
            by_cases hj : j = i.1 <;> simp [Function.update, hj]
          have hDSIC : utility (extendProfile fixed v) ≥
              utility (Function.update (extendProfile fixed v) i.1 vi2) := by
            rw [← hUpdateInst]
            show utility (extendProfile fixed v) ≥ utility _
            simpa [utility, hiReport] using h
          have hEq : utility (extendProfile fixed (Function.update v i vi2)) =
              utility (Function.update (extendProfile fixed v) i.1 vi2) :=
            congrArg utility (hextend_update fixed v i vi2)
          -- Bridge N' instance mismatch as well
          have hUpdateInstN' :
              (@Function.update N' _ (fun a b => Classical.propDecidable (a = b)) v i vi2) =
              (Function.update v i vi2) := by
            funext j a
            by_cases hj : j = i <;> simp [Function.update, hj]
          dsimp [slicedMechanism]
          have hcalc : utility (extendProfile fixed v) ≥
              utility (extendProfile fixed (Function.update v i vi2)) :=
            calc
              utility (extendProfile fixed v) ≥
                  utility (Function.update (extendProfile fixed v) i.1 vi2) := hDSIC
              _ = utility (extendProfile fixed (Function.update v i vi2)) := hEq.symm
          rw [← hUpdateInstN'] at hcalc
          simpa [utility] using hcalc
        have hsmonSlice (fixed : A → Real) :
            IsSMon (slicedMechanism fixed).choiceFn := by
          intro i v vi vi2 a b hab hwin hwin2
          have hwin' : M.choiceFn
              (Function.update (extendProfile fixed v) i.1 vi) = a := by
            rw [← hextend_update fixed v i vi]
            exact hwin
          have hwin2' : M.choiceFn
              (Function.update (extendProfile fixed v) i.1 vi2) = b := by
            rw [← hextend_update fixed v i vi2]
            exact hwin2
          exact hsmon i.1 (extendProfile fixed v) vi vi2 a b hab hwin' hwin2'
        have hontoSlice (fixed : A → Real) :
            Function.Surjective (slicedMechanism fixed).choiceFn := by
          intro a
          have hfull := hnv₀ fixed
          have hmem : a ∈ range M.choiceFn i₀ fixed := by
            rw [hfull]
            exact Finset.mem_univ a
          unfold range at hmem
          simp only [Finset.mem_filter] at hmem
          obtain ⟨v, hv⟩ := hmem.2
          refine ⟨restrictProfile v, ?_⟩
          change M.choiceFn (extendProfile fixed (restrictProfile v)) = a
          rw [hextend_restrict]
          exact hv
        have hAMslice (fixed : A → Real) :
            IsAffineMaximizer (slicedMechanism fixed).choiceFn :=
          ih N' (slicedMechanism fixed) (hdsicSlice fixed) (hsmonSlice fixed)
            (hontoSlice fixed) hA hle'

        let wRaw : (A → Real) → N' → Real :=
          fun fixed => Classical.choose (hAMslice fixed)
        let kRaw : (A → Real) → A → Real := fun fixed =>
          Classical.choose (Classical.choose_spec (hAMslice fixed))
        have hraw (fixed : A → Real) :
            (∀ i, 0 ≤ wRaw fixed i) ∧
              (∃ i, wRaw fixed i ≠ 0) ∧
              ∀ v a, affineScore (wRaw fixed) (kRaw fixed) v
                ((slicedMechanism fixed).choiceFn v) ≥
                  affineScore (wRaw fixed) (kRaw fixed) v a :=
          Classical.choose_spec (Classical.choose_spec (hAMslice fixed))
        let total (fixed : A → Real) : Real :=
          Finset.univ.sum (fun i : N' => wRaw fixed i)
        have htotal_pos (fixed : A → Real) : 0 < total fixed := by
          obtain ⟨j, hj⟩ := (hraw fixed).2.1
          have hjpos : 0 < wRaw fixed j :=
            lt_of_le_of_ne ((hraw fixed).1 j) (Ne.symm hj)
          have hjle : wRaw fixed j ≤ total fixed := by
            dsimp [total]
            exact Finset.single_le_sum
              (fun i hi => (hraw fixed).1 i) (Finset.mem_univ j)
          exact lt_of_lt_of_le hjpos hjle

        let lift (g : N' → Real) : N → Real := fun i =>
          if hi : i ≠ i₀ then g ⟨i, by simp [Finset.mem_erase, hi]⟩ else 0
        have hsumLift (g : N' → Real) :
            Finset.univ.sum (fun i : N => lift g i) =
              Finset.univ.sum (fun i : N' => g i) := by
          have hdrop :
              Finset.univ.sum (fun i : N => lift g i) =
                (Finset.univ.erase i₀).sum (fun i => lift g i) := by
            rw [← Finset.sum_erase_add Finset.univ (fun i : N => lift g i)
              (Finset.mem_univ i₀)]
            simp [lift]
          rw [hdrop]
          rw [Finset.sum_subtype (s := Finset.univ.erase i₀)
            (p := fun i : N => i ∈ Finset.univ.erase i₀) (by intro i; rfl)
            (fun i => lift g i)]
          calc
            _ = (Finset.univ.erase i₀).attach.sum (fun a : N' => g a) := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  simp [lift, subtype_ne a]
            _ = Finset.univ.sum (fun i : N' => g i) := rfl

        let w : (A → Real) → N → Real := fun fixed i =>
          if hi : i ≠ i₀ then
            wRaw fixed ⟨i, by simp [Finset.mem_erase, hi]⟩ / total fixed else 0
        let offsets : (A → Real) → A → Real := fun fixed a =>
          kRaw fixed a / total fixed
        have hsumw (fixed : A → Real) :
            Finset.univ.sum (fun i : N => w fixed i) = 1 := by
          calc
            _ = Finset.univ.sum
                (fun i : N => lift (fun j : N' => wRaw fixed j / total fixed) i) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  by_cases hir : i = i₀
                  · subst i
                    simp [w, lift]
                  · simp [w, lift, hir]
            _ = Finset.univ.sum (fun j : N' => wRaw fixed j / total fixed) :=
                  hsumLift (fun j : N' => wRaw fixed j / total fixed)
            _ = (Finset.univ.sum (fun j : N' => wRaw fixed j)) * (total fixed)⁻¹ := by
                  simp_rw [div_eq_mul_inv]
                  rw [← Finset.sum_mul]
            _ = 1 := by
                  simp [total, div_eq_mul_inv, (ne_of_gt (htotal_pos fixed))]

        have hsumScore (fixed : A → Real) (v : Valuation N A) (a : A) :
            Finset.univ.sum (fun i : N => w fixed i * v i a) =
              (Finset.univ.sum (fun j : N' => wRaw fixed j * v j.1 a)) /
                total fixed := by
          calc
            _ = Finset.univ.sum (fun i : N =>
                lift (fun j : N' => wRaw fixed j * v j.1 a / total fixed) i) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  by_cases hir : i = i₀
                  · subst i
                    simp [w, lift]
                  · simp [w, lift, hir]
                    ring_nf
            _ = Finset.univ.sum
                (fun j : N' => wRaw fixed j * v j.1 a / total fixed) :=
                  hsumLift (fun j : N' => wRaw fixed j * v j.1 a / total fixed)
            _ = (Finset.univ.sum (fun j : N' => wRaw fixed j * v j.1 a)) /
                total fixed := by
                  simp_rw [div_eq_mul_inv]
                  rw [← Finset.sum_mul]
        have hscore (fixed : A → Real) (v : Valuation N A) (a : A) :
            affineScore (w fixed) (offsets fixed) v a =
              affineScore (wRaw fixed) (kRaw fixed) (restrictProfile v) a /
                total fixed := by
          unfold affineScore
          rw [hsumScore]
          dsimp [offsets]
          simp only [div_eq_mul_inv]
          ring

        have hrep : ∀ fixed : A → Real,
            (∀ i, 0 ≤ w fixed i) ∧
            (∀ v a, affineScore (w fixed) (offsets fixed) v
              (slice M.choiceFn i₀ fixed v) ≥ affineScore (w fixed) (offsets fixed) v a) := by
          intro fixed
          constructor
          · intro i
            by_cases hi : i = i₀
            · simp [w, hi]
            · simpa [w, hi, Finset.mem_erase] using
                div_nonneg ((hraw fixed).1 ⟨i, by simp [Finset.mem_erase, hi]⟩)
                  (le_of_lt (htotal_pos fixed))
          · intro v a
            have hsliceEq : (slicedMechanism fixed).choiceFn (restrictProfile v) =
                slice M.choiceFn i₀ fixed v := by
              change M.choiceFn (extendProfile fixed (restrictProfile v)) =
                M.choiceFn (Function.update v i₀ fixed)
              rw [hextend_restrict]
            have hmax := (hraw fixed).2.2 (restrictProfile v) a
            rw [hsliceEq] at hmax
            rw [hscore fixed v (slice M.choiceFn i₀ fixed v), hscore fixed v a]
            have hdiv :
                affineScore (wRaw fixed) (kRaw fixed) (restrictProfile v) a /
                    total fixed ≤
                  affineScore (wRaw fixed) (kRaw fixed) (restrictProfile v)
                    (slice M.choiceFn i₀ fixed v) / total fixed :=
              (div_le_div_iff_of_pos_right (htotal_pos fixed)).2 hmax
            linarith

        have hwind : ∀ fixed fixed' i, i ≠ i₀ → w fixed i = w fixed' i := by
          intro fixed fixed' i hi
          let u : A → Real := fun a => max (fixed a) (fixed' a) + 1
          have hle₁ : ∀ a, fixed a ≤ u a := by
            intro a
            dsimp [u]
            linarith [le_max_left (fixed a) (fixed' a)]
          have hle₂ : ∀ a, fixed' a ≤ u a := by
            intro a
            dsimp [u]
            linarith [le_max_right (fixed a) (fixed' a)]
          have hu₁ := weights_eq_upper M.choiceFn hsmon i₀ w offsets hrep hsumw hA fixed u hle₁
          have hu₂ := weights_eq_upper M.choiceFn hsmon i₀ w offsets hrep hsumw hA fixed' u hle₂
          have heq : w fixed = w fixed' := hu₁.symm.trans hu₂
          exact congrFun heq i

        let fixed₀ : A → Real := fun _ => 0
        obtain ⟨j', hj'⟩ := (hraw fixed₀).2.1
        have hjRawPos : 0 < wRaw fixed₀ j' :=
          lt_of_le_of_ne ((hraw fixed₀).1 j') (Ne.symm hj')
        have hjPos : 0 < w fixed₀ j'.1 := by
          have hwval : w fixed₀ j'.1 = wRaw fixed₀ j' / total fixed₀ := by
            simp [w, subtype_ne j']
          rw [hwval]
          exact div_pos hjRawPos (htotal_pos fixed₀)
        have hnd : ∃ i, i ≠ i₀ ∧ ∃ fixed, 0 < w fixed i :=
          ⟨j'.1, subtype_ne j', fixed₀, hjPos⟩
        obtain ⟨alpha, halpha, hoff⟩ :=
          offsets_consistent_of_fixed_agent_core M.choiceFn hsmon i₀ hA
            w offsets hrep hwind hnd
        let W : N → Real := fun i => if hi : i = i₀ then alpha else w fixed₀ i
        let K : A → Real := fun a => offsets fixed₀ a - alpha * fixed₀ a
        have hWnonneg : ∀ i, 0 ≤ W i := by
          intro i
          by_cases hi : i = i₀
          · simp [W, hi]
            exact halpha
          · simp [W, hi]
            exact (hrep fixed₀).1 i
        have hWnonzero : ∃ i, W i ≠ 0 := by
          refine ⟨j'.1, ?_⟩
          have hjW : W j'.1 = w fixed₀ j'.1 := by
            simp [W, subtype_ne j']
          rw [hjW]
          exact ne_of_gt hjPos
        have hoffdiff (fixed : A → Real) (a b : A) :
            (offsets fixed a - alpha * fixed a) -
              (offsets fixed b - alpha * fixed b) = K a - K b := by
          have h := hoff fixed fixed₀ a b
          simpa [K] using h
        have hweightEq (fixed : A → Real) (i : N) :
            W i = w fixed i + (if i = i₀ then alpha else 0) := by
          by_cases hi : i = i₀
          · subst i
            simp [W, w]
          · have hw := hwind fixed₀ fixed i hi
            simp [W, hi, hw]
        have hsumW (fixed : A → Real) (v : Valuation N A) (a : A) :
            Finset.univ.sum (fun i : N => W i * v i a) =
              Finset.univ.sum (fun i : N => w fixed i * v i a) +
                alpha * v i₀ a := by
          calc
            _ = Finset.univ.sum (fun i : N =>
                (w fixed i + (if i = i₀ then alpha else 0)) * v i a) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [hweightEq fixed i]
            _ = Finset.univ.sum (fun i : N => w fixed i * v i a) +
                Finset.univ.sum (fun i : N =>
                  (if i = i₀ then alpha else 0) * v i a) := by
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = Finset.univ.sum (fun i : N => w fixed i * v i a) +
                alpha * v i₀ a := by
                  congr 1
                  rw [Finset.sum_eq_single i₀]
                  · simp
                  · intro i hi hne
                    simp [hne]
                  · simp
        have hscoreDiff (v : Valuation N A) (a b : A) :
            affineScore W K v a - affineScore W K v b =
              affineScore (w (v i₀)) (offsets (v i₀)) v a -
                affineScore (w (v i₀)) (offsets (v i₀)) v b := by
          have hsumA := hsumW (v i₀) v a
          have hsumB := hsumW (v i₀) v b
          have hoffset := hoffdiff (v i₀) a b
          unfold affineScore
          rw [hsumA, hsumB]
          dsimp [K] at hoffset ⊢
          linarith
        refine ⟨W, K, hWnonneg, hWnonzero, ?_⟩
        intro v a
        have hsliceMax : affineScore (w (v i₀)) (offsets (v i₀)) v
            (M.choiceFn v) ≥ affineScore (w (v i₀)) (offsets (v i₀)) v a := by
          have h := (hrep (v i₀)).2 v a
          simpa [slice, Function.update_self] using h
        have hdiff := hscoreDiff v (M.choiceFn v) a
        linarith

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

/-- Onto preservation: tie-breaking an onto choice function keeps it onto.
    Every alternative in the range of f remains achievable after tie-breaking. -/
lemma tieBreak_onto (f : Valuation N A → A) (hwmon : IsWMon f)
    (honto : Function.Surjective f) :
    Function.Surjective (tieBreak f hwmon) := by
  intro a
  obtain ⟨v, hv⟩ := honto a
  refine ⟨perturb v a 1, ?_⟩
  exact tieBreak_eq_after_positive_bump f hwmon v a hv 1 one_pos

/-- Taxation converse (W-MON → DSIC payments): a weakly monotone choice
    function can be equipped with payments making it DSIC.

    Fixing the other reports, the proof anchors the menu at the outcome chosen
    by the zero valuation and prices each alternative by the negative infimum
    of its value gap over reports selecting that anchor. W-MON bounds these
    infima, and a two-coordinate perturbation shows the selected outcome
    maximizes utility at every report.

    NOTE (2026-09-27): This replaces the false `tieBreakMechanism_dsic`.
    Reusing the *original* mechanism's menu prices for tie-broken outcomes
    does NOT preserve DSIC: a counterexample (2 agents, 2 alternatives)
    shows tie-breaking can force an outcome whose menu price exceeds the
    agent's value, creating a profitable deviation. The payments must be
    constructed fresh from the tie-broken choice function's own W-MON
    structure, not inherited from the original mechanism. -/
lemma wmon_dsic_payments (f : Valuation N A → A) (hwmon : IsWMon f) :
    ∃ pay : Valuation N A → N → Real, IsDSIC ⟨f, pay⟩ := by
  classical
  let zeroVal : A → Real := fun _ => 0
  have updateEq (p : Valuation N A) (j : N) (w : A → Real) :
      Function.update p j w =
        @Function.update N (fun _ : N => A → Real) (Classical.decEq N) p j w := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  let baseProfile : Valuation N A → N → Valuation N A :=
    fun v i => Function.update v i zeroVal
  let menuCost : Valuation N A → N → A → Real := fun v i a =>
    sInf {t : Real | ∃ w : A → Real,
      f (Function.update (baseProfile v i) i w) = f (baseProfile v i) ∧
        t = w (f (baseProfile v i)) - w a}
  let pay : Valuation N A → N → Real := fun v i => -menuCost v i (f v)
  refine ⟨pay, ?_⟩
  unfold IsDSIC
  intro i v vi2
  let base := baseProfile v i
  let K := f base
  let g : (A → Real) → A := fun w => f (Function.update base i w)
  let S : A → Set Real := fun a =>
    {t | ∃ w : A → Real, g w = K ∧ t = w K - w a}
  let d : A → Real := fun a => sInf (S a)
  have hzero : g zeroVal = K := by
    dsimp [g, K, base, baseProfile]
    rw [Function.update_idem]
  have htruthout : g (v i) = f v := by
    dsimp [g, base, baseProfile]
    rw [Function.update_idem, update_self v i]
  have hdevout : g vi2 = f (Function.update v i vi2) := by
    dsimp [g, base, baseProfile]
    rw [Function.update_idem]
  have hcost_eq : ∀ a, menuCost v i a = d a := by
    intro a
    rfl
  have hbaseUpdate : baseProfile (Function.update v i vi2) i = base := by
    dsimp [base, baseProfile]
    rw [Function.update_idem]
  have hcostUpdate : ∀ a,
      menuCost (Function.update v i vi2) i a = menuCost v i a := by
    intro a
    dsimp [menuCost]
    rw [hbaseUpdate]
  have hnonempty : ∀ a, (S a).Nonempty := by
    intro a
    refine ⟨0, ?_⟩
    change ∃ w : A → Real, g w = K ∧ 0 = w K - w a
    exact ⟨zeroVal, hzero, by simp [zeroVal]⟩
  have hdLower : ∀ a (u : A → Real), g u = a → u K - u a ≤ d a := by
    intro a u hu
    apply le_csInf (hnonempty a)
    intro t ht
    rcases ht with ⟨w, hw, rfl⟩
    by_cases h : a = K
    · simp [h]
    · have hm : w K - w a ≥ u K - u a :=
        hwmon i base w u K a (Ne.symm h) hw hu
      exact hm
  have hdUpper : ∀ a, (∃ u : A → Real, g u = a) →
      ∀ w : A → Real, g w = K → d a ≤ w K - w a := by
    intro a ha w hw
    have hbelow : BddBelow (S a) := by
      by_cases h : a = K
      · refine ⟨0, ?_⟩
        intro t ht
        rcases ht with ⟨z, hz, rfl⟩
        simp [h]
      · obtain ⟨u, hu⟩ := ha
        refine ⟨u K - u a, ?_⟩
        intro t ht
        rcases ht with ⟨z, hz, rfl⟩
        have hm : z K - z a ≥ u K - u a :=
          hwmon i base z u K a (Ne.symm h) hz hu
        exact hm
    change sInf (S a) ≤ w K - w a
    apply csInf_le hbelow
    change ∃ z : A → Real, g z = K ∧ w K - w a = z K - z a
    exact ⟨w, hw, rfl⟩
  have hdk : d K = 0 := by
    have hlow := hdLower K zeroVal hzero
    have hupp := hdUpper K ⟨zeroVal, hzero⟩ zeroVal hzero
    simp [zeroVal] at hlow hupp
    linarith
  have hselected : ∀ x : A → Real, x (g x) + d (g x) ≥ x K := by
    intro x
    have h := hdLower (g x) x rfl
    linarith
  have hanchorBest : ∀ x : A → Real, ∀ b : A,
      (∃ y : A → Real, g y = b) → g x = K →
        x K ≥ x b + d b := by
    intro x b hb hx
    have h := hdUpper b hb x hx
    linarith
  have hmenuMax : ∀ x y : A → Real,
      x (g x) + d (g x) ≥ x (g y) + d (g y) := by
    intro x y
    by_contra hnot
    have hlt : x (g x) + d (g x) < x (g y) + d (g y) := by linarith
    have hnotxK : g x ≠ K := by
      intro hx
      rw [hx, hdk] at hlt
      have hbest := hanchorBest x (g y) ⟨y, rfl⟩ hx
      linarith
    have hnotyK : g y ≠ K := by
      intro hy
      rw [hy, hdk] at hlt
      have hsel := hselected x
      linarith
    have hxy : g x ≠ g y := by
      intro hxy
      rw [hxy] at hlt
      exact lt_irrefl _ hlt
    let ε : Real := (x (g y) + d (g y) - (x (g x) + d (g x))) / 4
    let γ : Real := (x (g x) + d (g x) - x K) + 2 * ε
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hγgreater : ε < γ := by dsimp [γ]; linarith [hselected x]
    have hleft : x (g x) + d (g x) + ε < x K + γ := by
      dsimp [γ]
      linarith
    have hright : x K + γ < x (g y) + d (g y) := by
      dsimp [γ, ε]
      linarith
    let z : A → Real := Function.update
      (Function.update x K (x K + γ)) (g x) (x (g x) + ε)
    have hza : z (g x) = x (g x) + ε := by simp [z]
    have hzk : z K = x K + γ := by simp [z, Ne.symm hnotxK]
    have hzy : z (g y) = x (g y) := by simp [z, hnotyK, Ne.symm hxy]
    have hselectedZ : z (g z) + d (g z) ≥ z K := hselected z
    have hnotza : g z ≠ g x := by
      intro heq
      rw [heq, hza, hzk] at hselectedZ
      linarith
    have hnotzK : g z ≠ K := by
      intro heq
      have hbest := hanchorBest z (g y) ⟨y, rfl⟩ heq
      rw [hzk, hzy] at hbest
      linarith
    have hzz : z (g z) = x (g z) := by simp [z, hnotza, hnotzK]
    have hmono : x (g x) - x (g z) ≥ z (g x) - z (g z) :=
      hwmon i base x z (g x) (g z) (Ne.symm hnotza) rfl rfl
    rw [hza, hzz] at hmono
    linarith [hε]
  have hcostUpdateD : ∀ a, menuCost (Function.update v i vi2) i a = d a := by
    intro a
    rw [hcostUpdate a, hcost_eq a]
  have hptruth : pay v i = -d (g (v i)) := by
    dsimp [pay]
    rw [hcost_eq, htruthout]
  have hpdev : pay (Function.update v i vi2) i = -d (g vi2) := by
    dsimp [pay]
    rw [hcostUpdateD, hdevout]
  have hFdev : f (@Function.update N (fun _ : N => A → Real)
      (Classical.decEq N) v i vi2) = g vi2 := by
    calc
      _ = f (Function.update v i vi2) := congrArg f (updateEq v i vi2).symm
      _ = g vi2 := hdevout.symm
  have hpdevClassical : pay
      (@Function.update N (fun _ : N => A → Real) (Classical.decEq N) v i vi2) i =
      -d (g vi2) := by
    rw [(updateEq v i vi2).symm]
    exact hpdev
  simp only [Mechanism.choiceFn, Mechanism.pay]
  rw [htruthout.symm, hFdev, hptruth, hpdevClassical]
  linarith [hmenuMax (v i) vi2]

/-- Roberts' theorem (M6 assembly): DSIC + onto implies affine maximizer. -/
theorem roberts_theorem (hA : 3 ≤ Fintype.card A)
    (M : Mechanism N A)
    (hdsic : IsDSIC M)
    (honto : Function.Surjective M.choiceFn) :
    IsAffineMaximizer M.choiceFn := by
  -- (a) DSIC gives W-MON (taxation principle).
  have hwmon : IsWMon M.choiceFn := wmon_of_dsic M hdsic
  -- (b) S-MON reduction: the tie-broken rule is S-MON (hence W-MON).
  have hsmon_g : IsSMon (tieBreak M.choiceFn hwmon) :=
    tieBreak_isSMon M.choiceFn hwmon
  have hwmon_g : IsWMon (tieBreak M.choiceFn hwmon) :=
    smon_implies_wmon _ hsmon_g
  -- (c) Build DSIC payments for the tie-broken choice function from its W-MON.
  obtain ⟨pay_g, hdsic_g⟩ := wmon_dsic_payments _ hwmon_g
  -- (d) Induction (Lemmas 8-10): the tie-broken rule is an affine maximizer.
  have htb_onto : Function.Surjective (tieBreak M.choiceFn hwmon) :=
    tieBreak_onto M.choiceFn hwmon honto
  have htb_am : IsAffineMaximizer (tieBreak M.choiceFn hwmon) :=
    dsic_smon_affine_maximizer ⟨tieBreak M.choiceFn hwmon, pay_g⟩
      hdsic_g hsmon_g htb_onto hA
  -- (e) Transfer back to the original choice function.
  exact affine_maximizer_transfer M.choiceFn hwmon htb_am

end

end Roberts
