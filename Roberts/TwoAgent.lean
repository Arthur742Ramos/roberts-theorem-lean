import Roberts.NoVeto
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

namespace Roberts

section

variable {N A : Type*} [Fintype N] [Fintype A] [DecidableEq N] [DecidableEq A]
  [Nonempty N] [Nonempty A]

/-- Affine price structure: agent i_price's prices are affine in agent i_val's values.
    price M i_price v a = h v - alpha * v i_val a - beta a with 0 ≤ alpha.
    This is the price representation of Lemma 5.1 in the modular proof. -/
def HasAffinePrices (M : Mechanism N A) (i_price i_val : N) : Prop :=
  Exists fun alpha : Real => 0 ≤ alpha ∧ Exists fun h : Valuation N A → Real =>
    Exists fun beta : A → Real => ∀ v a, price M i_price v a = h v - alpha * v i_val a - beta a

/-- Every alternative is achievable by agent i2 at any profile, from i1's no-veto power.
    This is the "prices are finite" step of Claim 5.3: i1 having no veto power means
    i2 is decisive, so taxation applies to every alternative. -/
lemma achievable_of_noVeto {M : Mechanism N A} {i1 i2 : N} (h12 : i1 ≠ i2)
    (hall : ∀ i, i = i1 ∨ i = i2) (hdec : HasNoVetoPower M.choiceFn i1)
    (w : Valuation N A) (c : A) : Achievable M.choiceFn i2 w c := by
  classical
  have hmem : c ∈ range M.choiceFn i1 (w i1) := (hdec (w i1)).symm ▸ Finset.mem_univ c
  unfold range at hmem
  obtain ⟨vc, hvc⟩ := (Finset.mem_filter.mp hmem).2
  refine ⟨vc i2, ?_⟩
  have heq : Function.update w i2 (vc i2) = Function.update vc i1 (w i1) := by
    funext j
    rcases hall j with rfl | rfl
    · rw [Function.update_of_ne h12, Function.update_self]
    · rw [Function.update_self, Function.update_of_ne (Ne.symm h12)]
  rw [heq]
  exact hvc

/-- Claim 5.3 (Dobzinski-Nisan): prices are pairwise (decreasing) monotone.
    If agent i1's value-difference for (a,b) weakly decreases from v to v',
    then agent i2's price-difference for (a,b) weakly decreases as well.
    Proof: otherwise pick agent i2's value-difference strictly between the two
    price-differences (with very low values elsewhere); taxation forces
    f = b at v but f = a at v', contradicting S-MON. -/
lemma pairwise_le {M : Mechanism N A} (hdsic : IsDSIC M) (hsmon : IsSMon M.choiceFn)
    {i1 i2 : N} (h12 : i1 ≠ i2) (hall : ∀ i, i = i1 ∨ i = i2)
    (hdec : HasNoVetoPower M.choiceFn i1)
    (v v' : Valuation N A) (a b : A) (hab : a ≠ b)
    (hle : v i1 a - v i1 b ≥ v' i1 a - v' i1 b) :
    price M i2 v a - price M i2 v b ≤ price M i2 v' a - price M i2 v' b := by
  by_contra hlt
  rw [not_le] at hlt
  -- midpoint strictly between the two price differences
  set d : Real := ((price M i2 v a - price M i2 v b) +
    (price M i2 v' a - price M i2 v' b)) / 2 with hd
  have hd1 : price M i2 v a - price M i2 v b > d := by rw [hd]; linarith
  have hd2 : d > price M i2 v' a - price M i2 v' b := by rw [hd]; linarith
  -- crude uniform bound via a sum of absolute values
  set S : Real := Finset.univ.sum (fun c => |price M i2 v c| + |price M i2 v' c|) with hS
  have hSbound : ∀ c, |price M i2 v c| + |price M i2 v' c| ≤ S := by
    intro c
    have h1 := Finset.add_sum_erase Finset.univ
      (fun c => |price M i2 v c| + |price M i2 v' c|) (Finset.mem_univ c)
    have h2 : 0 ≤ (Finset.univ.erase c).sum
        (fun c => |price M i2 v c| + |price M i2 v' c|) :=
      Finset.sum_nonneg (fun c _ => by positivity)
    rw [hS]; linarith
  have hSnonneg : 0 ≤ S := by
    have h1 := hSbound (Classical.choice inferInstanceAs (Nonempty A))
    have h2 : (0:Real) ≤ |price M i2 v (Classical.choice inferInstanceAs (Nonempty A))| :=
      abs_nonneg _
    have h3 : (0:Real) ≤ |price M i2 v' (Classical.choice inferInstanceAs (Nonempty A))| :=
      abs_nonneg _
    linarith
  set K : Real := S + |d| + 2 with hK
  have hKpos : 0 < K := by rw [hK]; have := abs_nonneg d; linarith
  have hKbound : ∀ c, |price M i2 v c| ≤ K ∧ |price M i2 v' c| ≤ K := by
    intro c
    have h1 := hSbound c
    have h2 : (0:Real) ≤ |d| := abs_nonneg d
    rw [hK]
    constructor <;> linarith [abs_nonneg (price M i2 v c), abs_nonneg (price M i2 v' c)]
  have hKd : |d| < K := by rw [hK]; linarith
  -- agent i2's separating valuation: y_a - y_b = d, others very low
  set y : A → Real := fun c => if c = a then d else if c = b then 0 else -3 * K with hy
  have hya : y a = d := by simp [hy]
  have hyb : y b = 0 := by simp [hy, Ne.symm hab]
  have hyc : ∀ c : A, c ≠ a → c ≠ b → y c = -3 * K := by
    intro c hca hcb; simp [hy, hca, hcb]
  set w : Valuation N A := Function.update v i2 y with hw_def
  set w' : Valuation N A := Function.update v' i2 y with hw'_def
  -- prices transfer from v to w (they only depend on agent i1's report)
  have hPw : ∀ c, price M i2 w c = price M i2 v c := fun c => by
    have h := price_independent M hdsic i2 v y (v i2) c
    rw [← hw_def, Function.update_eq_self i2 v] at h
    exact h
  have hPw' : ∀ c, price M i2 w' c = price M i2 v' c := fun c => by
    have h := price_independent M hdsic i2 v' y (v' i2) c
    rw [← hw'_def, Function.update_eq_self i2 v'] at h
    exact h
  have hach : ∀ c, Achievable M.choiceFn i2 w c :=
    fun c => achievable_of_noVeto h12 hall hdec w c
  have hach' : ∀ c, Achievable M.choiceFn i2 w' c :=
    fun c => achievable_of_noVeto h12 hall hdec w' c
  -- at w, b is the unique surplus maximizer, so f w = b
  have hfw : M.choiceFn w = b := by
    by_contra hne
    have htax := taxation_ineq M hdsic i2 w y b (hach b)
    have hww : Function.update w i2 y = w := by
      rw [hw_def]; exact Function.update_idem y y v
    rw [hww] at htax
    have hstrict : y b - price M i2 w b >
        y (M.choiceFn w) - price M i2 w (M.choiceFn w) := by
      by_cases hfa : M.choiceFn w = a
      · rw [hfa, hya, hyb, hPw a, hPw b]; linarith [hd1]
      · by_cases hfb : M.choiceFn w = b
        · exact absurd hfb hne
        · rw [hyc _ hfa hfb, hyb, hPw b, hPw (M.choiceFn w)]
          have hb1 := abs_le.mp (hKbound b).1
          have hc1 := abs_le.mp (hKbound (M.choiceFn w)).1
          linarith [hKpos]
    linarith
  -- at w', a is the unique surplus maximizer, so f w' = a
  have hfw' : M.choiceFn w' = a := by
    by_contra hne
    have htax := taxation_ineq M hdsic i2 w' y a (hach' a)
    have hww : Function.update w' i2 y = w' := by
      rw [hw'_def]; exact Function.update_idem y y v'
    rw [hww] at htax
    have hstrict : y a - price M i2 w' a >
        y (M.choiceFn w') - price M i2 w' (M.choiceFn w') := by
      by_cases hfb : M.choiceFn w' = b
      · rw [hfb, hya, hyb, hPw' a, hPw' b]; linarith [hd2]
      · by_cases hfa : M.choiceFn w' = a
        · exact absurd hfa hne
        · rw [hyc _ hfa hfb, hya, hPw' a, hPw' (M.choiceFn w')]
          have ha1 := abs_le.mp (hKbound a).2
          have hc1 := abs_le.mp (hKbound (M.choiceFn w')).2
          have hd1' := abs_lt.mp hKd
          linarith [hKpos]
    linarith
  -- cast to S-MON form: w = update w i1 (v i1), w' = update w i1 (v' i1)
  have heq1 : Function.update w i1 (v i1) = w := by
    have h1 : w i1 = v i1 := by
      rw [hw_def]; exact Function.update_of_ne h12 y v
    rw [← h1]; exact Function.update_eq_self i1 w
  have heq2 : Function.update w i1 (v' i1) = w' := by
    funext j
    rcases hall j with rfl | rfl
    · rw [Function.update_self, hw'_def, Function.update_of_ne h12]
    · rw [Function.update_of_ne (Ne.symm h12), hw_def, hw'_def,
        Function.update_self, Function.update_self]
  -- S-MON on agent i1 gives the contradiction
  have hs := hsmon i1 w (v i1) (v' i1) b a (Ne.symm hab)
    (by rw [heq1]; exact hfw) (by rw [heq2]; exact hfw')
  linarith [hle, hs]

/-- Pairwise determination: equal value-differences give equal price-differences. -/
lemma pairwise_eq {M : Mechanism N A} (hdsic : IsDSIC M) (hsmon : IsSMon M.choiceFn)
    {i1 i2 : N} (h12 : i1 ≠ i2) (hall : ∀ i, i = i1 ∨ i = i2)
    (hdec : HasNoVetoPower M.choiceFn i1)
    (v v' : Valuation N A) (a b : A) (hab : a ≠ b)
    (heq : v i1 a - v i1 b = v' i1 a - v' i1 b) :
    price M i2 v a - price M i2 v b = price M i2 v' a - price M i2 v' b :=
  le_antisymm (pairwise_le hdsic hsmon h12 hall hdec v v' a b hab (le_of_eq heq.symm))
    (pairwise_le hdsic hsmon h12 hall hdec v' v a b hab (le_of_eq heq))

/-! ## Increment analysis: the price difference is affine in one coordinate -/

/-- Bumping agent i1's value for alternative a by δ in profile v. -/
def bumpVal {N A : Type*} [DecidableEq N] [DecidableEq A] (i1 : N) (v : Valuation N A)
    (a : A) (δ : Real) : Valuation N A :=
  Function.update v i1 (fun a' => v i1 a' + if a' = a then δ else 0)

lemma bumpVal_i1 {N A : Type*} [DecidableEq N] [DecidableEq A] (i1 : N)
    (v : Valuation N A) (a : A) (δ : Real) (a' : A) :
    (bumpVal i1 v a δ) i1 a' = v i1 a' + if a' = a then δ else 0 := by
  simp [bumpVal]

lemma bumpVal_j_ne {N A : Type*} [DecidableEq N] [DecidableEq A] (i1 : N)
    (v : Valuation N A) (a : A) (δ : Real) {j : N} (hj : j ≠ i1) :
    (bumpVal i1 v a δ) j = v j := by
  unfold bumpVal
  exact Function.update_of_ne hj _ _

lemma bumpVal_zero {N A : Type*} [DecidableEq N] [DecidableEq A] (i1 : N)
    (v : Valuation N A) (a : A) : bumpVal i1 v a 0 = v := by
  unfold bumpVal
  have h : (fun a' : A => v i1 a' + if a' = a then (0:Real) else 0) = v i1 := by
    funext a'
    by_cases haa : a' = a <;> simp [haa]
  rw [h]
  exact Function.update_eq_self i1 v

/-- Single bump: the a-vs-c difference shifts by δ. -/
lemma bumpVal_adiff {N A : Type*} [DecidableEq N] [DecidableEq A] (i1 : N)
    (v : Valuation N A) (a c : A) (δ : Real) (hac : a ≠ c) :
    (bumpVal i1 v a δ) i1 a - (bumpVal i1 v a δ) i1 c = (v i1 a + δ) - v i1 c := by
  have h1 : (bumpVal i1 v a δ) i1 a = v i1 a + δ := by
    rw [bumpVal_i1]; simp
  have h2 : (bumpVal i1 v a δ) i1 c = v i1 c := by
    rw [bumpVal_i1]; simp [Ne.symm hac]
  rw [h1, h2]

/-- Double bump (a then b): the a-vs-c difference still shifts by δ only. -/
lemma bumpVal2_adiff {N A : Type*} [DecidableEq N] [DecidableEq A] (i1 : N)
    (v : Valuation N A) (a b c : A) (δ : Real)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (bumpVal i1 (bumpVal i1 v a δ) b δ) i1 a - (bumpVal i1 (bumpVal i1 v a δ) b δ) i1 c
      = (v i1 a + δ) - v i1 c := by
  have h1 : (bumpVal i1 (bumpVal i1 v a δ) b δ) i1 a = v i1 a + δ := by
    have hinner : (bumpVal i1 v a δ) i1 a = v i1 a + δ := by rw [bumpVal_i1]; simp
    rw [bumpVal_i1, hinner]; simp [hab]
  have h2 : (bumpVal i1 (bumpVal i1 v a δ) b δ) i1 c = v i1 c := by
    have hinner : (bumpVal i1 v a δ) i1 c = v i1 c := by
      rw [bumpVal_i1]; simp [Ne.symm hac]
    rw [bumpVal_i1, hinner]; simp [Ne.symm hbc]
  rw [h1, h2]

/-- Normalized price Q_a(v) = P_a(v) - P_{c0}(v). -/
noncomputable def normPrice (M : Mechanism N A) (i2 : N) (c0 : A) (v : Valuation N A)
    (a : A) : Real :=
  price M i2 v a - price M i2 v c0

/-- The normalized price difference depends only on i1's value difference. -/
lemma Q_pairwise {M : Mechanism N A} (hdsic : IsDSIC M) (hsmon : IsSMon M.choiceFn)
    {i1 i2 : N} (h12 : i1 ≠ i2) (hall : ∀ i, i = i1 ∨ i = i2)
    (hdec : HasNoVetoPower M.choiceFn i1) (c0 : A)
    (v v' : Valuation N A) (a : A) (ha : a ≠ c0)
    (heq : v i1 a - v i1 c0 = v' i1 a - v' i1 c0) :
    normPrice M i2 c0 v a = normPrice M i2 c0 v' a := by
  unfold normPrice
  exact pairwise_eq hdsic hsmon h12 hall hdec v v' a c0 ha heq

/-- Claim 5.6: the increment from bumping a by δ is the same for any a ≠ c0. -/
lemma incr_eq {M : Mechanism N A} (hdsic : IsDSIC M) (hsmon : IsSMon M.choiceFn)
    {i1 i2 : N} (h12 : i1 ≠ i2) (hall : ∀ i, i = i1 ∨ i = i2)
    (hdec : HasNoVetoPower M.choiceFn i1) (c0 : A)
    (v : Valuation N A) (a b : A) (ha : a ≠ c0) (hb : b ≠ c0) (hab : a ≠ b)
    (δ : Real) :
    normPrice M i2 c0 (bumpVal i1 v a δ) a - normPrice M i2 c0 v a =
    normPrice M i2 c0 (bumpVal i1 v b δ) b - normPrice M i2 c0 v b := by
  -- double-bumped profile
  set z := bumpVal i1 (bumpVal i1 v a δ) b δ with hzdef
  have hQa : normPrice M i2 c0 (bumpVal i1 v a δ) a = normPrice M i2 c0 z a := by
    apply Q_pairwise hdsic hsmon h12 hall hdec c0 _ _ _ ha
    rw [hzdef]
    have e1 := bumpVal_adiff i1 v a c0 δ ha
    have e2 := bumpVal2_adiff i1 v a b c0 δ hab ha hb
    linarith
  have hQb : normPrice M i2 c0 (bumpVal i1 v b δ) b = normPrice M i2 c0 z b := by
    apply Q_pairwise hdsic hsmon h12 hall hdec c0 _ _ _ hb
    rw [hzdef]
    have e1 := bumpVal_adiff i1 v b c0 δ hb
    have ez1 : (bumpVal i1 (bumpVal i1 v a δ) b δ) i1 b = v i1 b + δ := by
      have hinner : (bumpVal i1 v a δ) i1 b = v i1 b := by
        rw [bumpVal_i1]; simp [Ne.symm hab]
      rw [bumpVal_i1, hinner]; simp
    have ez2 : (bumpVal i1 (bumpVal i1 v a δ) b δ) i1 c0 = v i1 c0 := by
      have hinner : (bumpVal i1 v a δ) i1 c0 = v i1 c0 := by
        rw [bumpVal_i1]; simp [Ne.symm ha]
      rw [bumpVal_i1, hinner]; simp [Ne.symm hb]
    linarith
  have hdiff : normPrice M i2 c0 z a - normPrice M i2 c0 z b =
      normPrice M i2 c0 v a - normPrice M i2 c0 v b := by
    have hzz : z i1 a - z i1 b = v i1 a - v i1 b := by
      rw [hzdef]
      have ez1 : (bumpVal i1 (bumpVal i1 v a δ) b δ) i1 a = v i1 a + δ := by
        have hinner : (bumpVal i1 v a δ) i1 a = v i1 a + δ := by rw [bumpVal_i1]; simp
        rw [bumpVal_i1, hinner]; simp [hab]
      have ez2 : (bumpVal i1 (bumpVal i1 v a δ) b δ) i1 b = v i1 b + δ := by
        have hinner : (bumpVal i1 v a δ) i1 b = v i1 b := by
          rw [bumpVal_i1]; simp [Ne.symm hab]
        rw [bumpVal_i1, hinner]; simp
      rw [ez1, ez2]; ring
    have h := pairwise_eq hdsic hsmon h12 hall hdec z v a b hab hzz
    unfold normPrice
    linarith
  linarith

/-- The increment depends only on the a-vs-c0 value difference. -/
lemma incr_dep {M : Mechanism N A} (hdsic : IsDSIC M) (hsmon : IsSMon M.choiceFn)
    {i1 i2 : N} (h12 : i1 ≠ i2) (hall : ∀ i, i = i1 ∨ i = i2)
    (hdec : HasNoVetoPower M.choiceFn i1) (c0 : A)
    (v v' : Valuation N A) (a : A) (ha : a ≠ c0) (δ : Real)
    (heq : v i1 a - v i1 c0 = v' i1 a - v' i1 c0) :
    normPrice M i2 c0 (bumpVal i1 v a δ) a - normPrice M i2 c0 v a =
    normPrice M i2 c0 (bumpVal i1 v' a δ) a - normPrice M i2 c0 v' a := by
  have h1 : normPrice M i2 c0 (bumpVal i1 v a δ) a =
      normPrice M i2 c0 (bumpVal i1 v' a δ) a := by
    apply Q_pairwise hdsic hsmon h12 hall hdec c0 _ _ _ ha
    have e1 := bumpVal_adiff i1 v a c0 δ ha
    have e2 := bumpVal_adiff i1 v' a c0 δ ha
    linarith
  have h2 : normPrice M i2 c0 v a = normPrice M i2 c0 v' a :=
    Q_pairwise hdsic hsmon h12 hall hdec c0 v v' a ha heq
  linarith

/-- With ≥3 alternatives there is always a third alternative distinct from two given. -/
lemma exists_ne_ne {A : Type*} [Fintype A] [DecidableEq A] {a c0 : A} (ha : a ≠ c0)
    (hA : 3 ≤ Fintype.card A) : ∃ b, b ≠ a ∧ b ≠ c0 := by
  by_contra h
  rw [not_exists] at h
  have h2 : ∀ b : A, b = a ∨ b = c0 := by
    intro b
    by_contra hc
    rw [not_or] at hc
    exact h b hc
  have hsub : Finset.univ ⊆ ({a, c0} : Finset A) := by
    intro b _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact h2 b
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, Finset.card_pair ha] at hle
  omega

/-- Claim 5.7: the increment is independent of the profile (for fixed a, δ). -/
lemma incr_const {M : Mechanism N A} (hdsic : IsDSIC M) (hsmon : IsSMon M.choiceFn)
    {i1 i2 : N} (h12 : i1 ≠ i2) (hall : ∀ i, i = i1 ∨ i = i2)
    (hdec : HasNoVetoPower M.choiceFn i1) (c0 : A) (hA : 3 ≤ Fintype.card A)
    (a : A) (ha : a ≠ c0) (δ : Real) (v v' : Valuation N A) :
    normPrice M i2 c0 (bumpVal i1 v a δ) a - normPrice M i2 c0 v a =
    normPrice M i2 c0 (bumpVal i1 v' a δ) a - normPrice M i2 c0 v' a := by
  obtain ⟨b, hab, hbc⟩ := exists_ne_ne ha hA
  suffices hsuff : ∀ w : Valuation N A,
      normPrice M i2 c0 (bumpVal i1 w a δ) a - normPrice M i2 c0 w a =
      normPrice M i2 c0 (bumpVal i1 (fun _ _ => 0) a δ) a -
        normPrice M i2 c0 (fun _ _ => 0) a by
    rw [hsuff v, hsuff v']
  intro w
  set vt : Valuation N A := Function.update (fun _ _ => (0:Real)) i1
    (fun a' => if a' = a then w i1 a - w i1 c0 else 0) with hvt
  have hvt_a : vt i1 a = w i1 a - w i1 c0 := by simp [hvt]
  have hvt_c : vt i1 c0 = 0 := by simp [hvt, Ne.symm ha]
  have hvt_b : vt i1 b = 0 := by simp [hvt, hab]
  calc normPrice M i2 c0 (bumpVal i1 w a δ) a - normPrice M i2 c0 w a
      = normPrice M i2 c0 (bumpVal i1 vt a δ) a - normPrice M i2 c0 vt a :=
        incr_dep hdsic hsmon h12 hall hdec c0 w vt a ha δ (by rw [hvt_a, hvt_c, sub_zero])
    _ = normPrice M i2 c0 (bumpVal i1 vt b δ) b - normPrice M i2 c0 vt b :=
        incr_eq hdsic hsmon h12 hall hdec c0 vt a b ha hbc (Ne.symm hab) δ
    _ = normPrice M i2 c0 (bumpVal i1 (fun _ _ => 0) b δ) b -
          normPrice M i2 c0 (fun _ _ => 0) b := by
        apply incr_dep hdsic hsmon h12 hall hdec c0 vt (fun _ _ => 0) b hbc δ
        rw [hvt_b, hvt_c]
    _ = normPrice M i2 c0 (bumpVal i1 (fun _ _ => 0) a δ) a -
          normPrice M i2 c0 (fun _ _ => 0) a :=
        (incr_eq hdsic hsmon h12 hall hdec c0 (fun _ _ => 0) a b ha hbc (Ne.symm hab) δ).symm

end

end Roberts
