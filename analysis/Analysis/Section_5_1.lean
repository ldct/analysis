import Mathlib.Tactic
import Analysis.Section_4_3

/-!
# Analysis I, Section 5.1

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a sequence of rationals
- Notions of `ε`-steadiness, eventual `ε`-steadiness, and Cauchy sequences

-/

namespace Chapter5

/--
  Definition 5.1.1 (Sequence). To avoid some technicalities involving dependent types, we extend
  sequences by zero to the left of the starting point `n₀`.
-/
@[ext]
structure Sequence where
  n₀ : ℤ
  seq : ℤ → ℚ
  vanish : ∀ n < n₀, seq n = 0

/-- Sequences can be thought of as functions from ℤ to ℚ. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℚ) where
  coe := fun a ↦ a.seq

/--
Functions from ℕ to ℚ can be thought of as sequences starting from 0; `ofNatFun` performs this conversion.

The `coe` attribute allows the delaborator to print `Sequence.ofNatFun f` as `↑f`, which is more concise; you may safely remove this if you prefer the more explicit notation.
-/
@[coe]
def Sequence.ofNatFun (a : ℕ → ℚ) : Sequence where
    n₀ := 0
    seq := fun n ↦ if n ≥ 0 then a n.toNat else 0
    vanish := by
      intro n hn
      simp [hn]

/--
If `a : ℕ → ℚ` is used in a context where a `Sequence` is expected, automatically coerce `a` to `Sequence.ofNatFun a` (which will be pretty-printed as `↑a`)
-/
instance : Coe (ℕ → ℚ) Sequence where
  coe := Sequence.ofNatFun

abbrev Sequence.mk' (n₀:ℤ) (a: { n // n ≥ n₀ } → ℚ) : Sequence where
  n₀ := n₀
  seq := fun n ↦ if h : n ≥ n₀ then a ⟨n, h⟩ else 0
  vanish := by
    intro n hn
    simp [hn]

lemma Sequence.eval_mk {n n₀:ℤ} (a: { n // n ≥ n₀ } → ℚ) (h: n ≥ n₀) :
    (Sequence.mk' n₀ a) n = a ⟨ n, h ⟩ := by simp [seq, h]

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℚ) : (a:Sequence) n = a n := by norm_cast

@[simp]
lemma Sequence.eval_coe_at_int (n:ℤ) (a: ℕ → ℚ) : (a:Sequence) n = if n ≥ 0 then a n.toNat else 0 := by norm_cast

@[simp]
lemma Sequence.n0_coe (a: ℕ → ℚ) : (a:Sequence).n₀ = 0 := by norm_cast

/-- Example 5.1.2 -/
abbrev Sequence.squares : Sequence := ((fun n:ℕ ↦ (n^2:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.squares n = n^2 := Sequence.eval_coe _ _

/-- Example 5.1.2 -/
abbrev Sequence.three : Sequence := ((fun (_:ℕ) ↦ (3:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.three n = 3 := Sequence.eval_coe _ (fun (_:ℕ) ↦ (3:ℚ))

/-- Example 5.1.2 -/
abbrev Sequence.squares_from_three : Sequence := mk' 3 (fun n ↦ n^2)

/-- Example 5.1.2 -/
example (n:ℤ) (hn: n ≥ 3) : Sequence.squares_from_three n = n^2 := Sequence.eval_mk _ hn

-- need to temporarily leave the `Chapter5` namespace to introduce the following notation

end Chapter5

/--
A slight generalization of 5.1.3 - definition of ε-steadiness for a sequence with an arbitrary starting point n₀
-/
abbrev Rat.steady (ε: ℚ) (a: Chapter5.Sequence) : Prop :=
  ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.close (a n) (a m)

lemma Rat.steady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.steady a ↔ ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.close (a n) (a m) := by rfl

namespace Chapter5

/--
5.1.3 - definition of ε-steadiness for a sequence starting at 0
-/
lemma Rat.isSteady_of_coe (ε : ℚ) (a:ℕ → ℚ) :
    ε.steady a ↔ ∀ n m : ℕ, ε.close (a n) (a m) := by
  constructor
  · intro h n m
    specialize h n (by simp) m (by simp)
    dsimp at h
    exact h

  intro h n hn m hm
  lift n to ℕ using hn
  lift m to ℕ using hm
  simp [h n m]

/--
Not in textbook: the sequence 2, 2 ... is 1-steady
Intended as a demonstration of `isSteady_of_coe`
-/
example : (1:ℚ).steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  rw [Rat.isSteady_of_coe]
  unfold Rat.close
  intro n m
  simp

/--
Compare: if you need to work with `Rat.steady` on the coercion directly, there will be side conditions `hn : n ≥ 0` and `hm : m ≥ 0` that you will need to deal with.
-/
example : (1:ℚ).steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  unfold Rat.steady Rat.close
  intro n hn m hm
  simp only [Sequence.n0_coe, Sequence.eval_coe_at_int] at hn hm
  simp [hn, hm]

/--
Example 5.1.5
-/
example : (1:ℚ).steady (fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)) := by
  rw [Rat.isSteady_of_coe]
  intro n m
  obtain h | h := Decidable.em (Even n)
  obtain h' | h' := Decidable.em (Even m)

  simp [h, h']
  unfold Rat.close
  norm_cast

  simp [h, h']
  unfold Rat.close
  norm_cast

  obtain h' | h' := Decidable.em (Even m)

  simp [h, h']
  unfold Rat.close
  norm_cast

  simp [h, h']
  unfold Rat.close
  norm_cast


/-- Example 5.1.5 -/
example : ¬ (0.5:ℚ).steady (fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)) := by
  rw [Rat.isSteady_of_coe]
  by_contra h
  specialize h 0 1
  dsimp at h
  unfold Rat.close at h
  norm_num at h

/-- Example 5.1.5 -/
example : (0.1:ℚ).steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.isSteady_of_coe]
  intro n m
  unfold Rat.close
  wlog h : m ≤ n
  · specialize this m n (by linarith)
    rwa [abs_sub_comm]
  rw [show (10: ℚ) ^ (-(m:ℤ) - 1) = (10: ℚ) ^ ((-(m:ℤ)) + (-1))  by congr, ← Section_4_3.zpow_add]
  rw [show (10: ℚ) ^ (-(n:ℤ) - 1) = (10: ℚ) ^ ((-(n:ℤ)) + (-1))  by congr, ← Section_4_3.zpow_add]
  rw [show 10 ^ (-(n:ℤ)) * 10 ^ (-1:ℤ) - 10 ^ (-(m:ℤ)) * 10 ^ (-1:ℤ) = (10 ^ (-1:ℤ)) * (10 ^ (-(n:ℤ)) - 10 ^ (-(m:ℤ)):ℚ) by ring]
  rw [abs_mul]
  rw [show |(10:ℚ) ^ (-1:ℤ)| = 0.1 by norm_num]
  -- suffices : |(10:ℚ) ^ (-n) - 10 ^ (-m)| ≤ 1
  -- field_simp
  -- field_simp at this
  -- exact this
  -- have : ((10) ^ (-n) - 10 ^ (-m) : ℚ) = 10^(m-n) := by sorry

  -- field_simp
  repeat sorry


/-- Example 5.1.5 -/
example : ¬(0.01:ℚ).steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.isSteady_of_coe]
  intro h
  specialize h 0 2
  dsimp at h
  unfold Rat.close at h
  norm_num at h
  rw [abs_of_nonneg (by positivity)] at h
  norm_num at h


/-- Example 5.1.5 -/
example (ε:ℚ) : ¬ ε.steady ((fun n:ℕ ↦ (2 ^ (n+1):ℚ) ):Sequence) := by
  intro h
  rw [Rat.isSteady_of_coe] at h
  specialize h 0
  have : ∃ n : ℕ, ε < n := by sorry
  obtain ⟨ n, hn ⟩ := this
  specialize h n
  dsimp at h
  unfold Rat.close at h
  norm_num at h
  sorry

/-- Example 5.1.5 -/
example (ε:ℚ) (hε: ε>0) : ε.steady ((fun _:ℕ ↦ (2:ℚ) ):Sequence) := by
  rw [Rat.isSteady_of_coe]
  intro n m
  unfold Rat.close
  norm_num
  positivity

def TenZeroZeroFun := (fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ))

def TenZeroZero := ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence)

example : (10:ℚ).steady (TenZeroZeroFun:Sequence) := by
  rw [Rat.isSteady_of_coe]
  unfold TenZeroZeroFun
  intro n m
  unfold Rat.close
  obtain h | h := Decidable.em (n = 0)
  all_goals {
    obtain h' | h' := Decidable.em (m = 0)
    simp [h]
    all_goals simp [h, h']
  }

example (ε:ℚ) (hε:ε<10):  ¬ ε.steady TenZeroZero := by
  unfold TenZeroZero
  intro h
  rw [Rat.isSteady_of_coe] at h
  specialize h 0 1
  dsimp at h
  unfold Rat.close at h
  norm_num at h
  linarith

/--
  a.from n₁ starts `a:Sequence` from `n₁`.  It is intended for use when `n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence `a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (n₁:ℤ) : Sequence :=
  mk' (max a.n₀ n₁) (fun n ↦ a (n:ℤ))

lemma Sequence.from_eval (a:Sequence) {n₁ n:ℤ} (hn: n ≥ n₁) :
  (a.from n₁) n = a n := by
  simp [Sequence.from, seq, hn]
  intro h
  exact (a.vanish n h).symm

end Chapter5

/-- Definition 5.1.6 (Eventually ε-steady) -/
abbrev Rat.eventuallySteady (ε: ℚ) (a: Chapter5.Sequence) : Prop :=
  ∃ N ≥ a.n₀, ε.steady (a.from N)

lemma Rat.eventuallySteady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.eventuallySteady a ↔ ∃ N ≥ a.n₀, ε.steady (a.from N) := by rfl

namespace Chapter5

def bassel := ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence)

/-- Example 5.1.7 -/
lemma Sequence.ex_5_1_7_a : ¬ (0.1:ℚ).steady bassel := by
  unfold bassel
  intro h
  rw [Rat.isSteady_of_coe] at h
  specialize h 0 3
  dsimp at h
  unfold Rat.close at h
  norm_num at h
  rw [abs_of_nonneg (by positivity)] at h
  norm_num at h

lemma Sequence.ex_5_1_7_b : (0.1:ℚ).steady (bassel.from 10) := by
  sorry

lemma Sequence.ex_5_1_7_c : (0.1:ℚ).eventuallySteady bassel := by
  sorry

lemma Sequence.ex_5_1_7_d {ε:ℚ} (hε:ε>0) :
    ε.eventuallySteady ((fun n:ℕ ↦ if n=0 then (10:ℚ) else (0:ℚ) ):Sequence) := by sorry

abbrev Sequence.isCauchy (a:Sequence) : Prop := ∀ ε > (0:ℚ), ε.eventuallySteady a

lemma Sequence.isCauchy_def (a:Sequence) :
  a.isCauchy ↔ ∀ ε > (0:ℚ), ε.eventuallySteady a := by rfl

lemma Sequence.isCauchy_of_coe (a:ℕ → ℚ) :
    (a:Sequence).isCauchy ↔ ∀ ε > (0:ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (a j) (a k) ≤ ε := by
  constructor
  intro h
  intro ε hε
  unfold Sequence.isCauchy at h
  specialize h ε hε
  unfold Rat.eventuallySteady at h
  obtain ⟨ N, hN, h' ⟩ := h
  lift N to ℕ using hN

  use N
  intro j hj k hk
  unfold Rat.steady at h'
  simp at h'
  have : max (0 : ℤ) N = N := by omega

  specialize h' j (by omega)
  specialize h' k (by omega)

  unfold Rat.close at h'
  simp at h'
  unfold Section_4_3.dist
  simp [hj, hk] at h'
  exact h'

  -- other implication

  intro h
  unfold Sequence.isCauchy
  intro ε hε
  unfold Rat.eventuallySteady

  specialize h ε hε
  obtain ⟨ N, h' ⟩ := h
  use max N 0
  constructor
  · simp
  unfold Rat.steady
  intro n hn m hm

  simp at hn hm
  have npos : 0 ≤ n := by omega
  have mpos : 0 ≤ m := by omega

  simp [hn, hm, npos, mpos]

  have : n.toNat = n := by omega

  lift n to ℕ using npos
  lift m to ℕ using mpos
  specialize h' n (by omega) m (by omega)
  simp

  unfold Section_4_3.dist at h'
  unfold Rat.close
  exact h'

example : ((fun _:ℕ ↦ (3:ℚ)):Sequence).isCauchy := by
  rw [Sequence.isCauchy_of_coe (fun _:ℕ ↦ (3:ℚ))]
  intro ε hε
  use 0
  intro j hj k hk
  unfold Section_4_3.dist
  norm_num
  positivity

lemma Sequence.isCauchy_of_mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℚ) :
    (mk' n₀ a).isCauchy ↔ ∀ ε > (0:ℚ), ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  constructor
  intro h ε hε
  specialize h ε hε
  obtain ⟨ N, hN, h' ⟩ := h
  use N
  dsimp at hN
  constructor
  · exact hN
  intro j hj k hk
  simp [show j ≥ n₀ by linarith, show k ≥ n₀ by linarith]
  unfold Rat.steady at h'
  dsimp at h'
  rw [show max n₀ N = N by omega] at *
  specialize h' j (by omega) k (by omega)
  simp [show n₀ ≤ j by omega, hj, show n₀ ≤ k by omega, hk] at h'
  trivial

  intro h
  intro ε hε

  unfold mk' Rat.eventuallySteady
  specialize h ε hε
  simp at h
  obtain ⟨ N, hN, h' ⟩ := h

  use max n₀ N
  constructor
  · simp
  unfold Rat.steady
  intro n hn m hm
  simp at hn hm
  simp [hn, hm]
  unfold Rat.close

  specialize h' n (by omega) m (by omega)
  simp [hn, hm] at h'
  unfold Section_4_3.dist at h'
  exact h'


noncomputable def Sequence.sqrt_two : Sequence :=
  (fun n:ℕ ↦ ((⌊ (Real.sqrt 2)*10^n ⌋ / 10^n):ℚ))

/--
  Example 5.1.10. (This requires extensive familiarity with Mathlib's API for the real numbers.)
-/
theorem Sequence.ex_5_1_10_a : (1:ℚ).steady sqrt_two := by sorry

/--
  Example 5.1.10. (This requires extensive familiarity with Mathlib's API for the real numbers.)
-/
theorem Sequence.ex_5_1_10_b : (0.1:ℚ).steady (sqrt_two.from 1) := by sorry

theorem Sequence.ex_5_1_10_c : (0.1:ℚ).eventuallySteady sqrt_two := by sorry

/-- Proposition 5.1.11 -/
theorem Sequence.harmonic_steady : (mk' 1 (fun n ↦ (1:ℚ)/n)).isCauchy := by
  -- This is proof is probably longer than it needs to be; there should be a shorter proof that
  -- is still in the spirit of  the proof in the book.
  rw [isCauchy_of_mk]
  intro ε hε
  have : ∃ N:ℕ, N > 1/ε := exists_nat_gt (1 / ε)
  obtain ⟨ N, hN ⟩ := this
  use N
  have hN' : (N:ℤ) > 0 := by
    have : (1/ε) > 0 := by positivity
    replace hN := this.trans hN
    simp at hN ⊢; assumption
  constructor
  . simp at hN' ⊢; linarith
  intro j hj k hk
  have hj' : (j:ℚ) ≥ 0 := by simp; linarith
  have hj'' : (1:ℚ)/j ≤ (1:ℚ)/N := by
    gcongr
    . simp at hN' ⊢; assumption
    . simp at hj ⊢; qify at hj; assumption
  have hj''' : (1:ℚ)/j ≥ 0 := by positivity
  have hj'''' : j ≥ 1 := by simp at hj'; linarith
  have hk' : (k:ℚ) ≥ 0 := by simp; linarith
  have hk'' : (1:ℚ)/k ≤ (1:ℚ)/N := by
    gcongr
    . simp at hN' ⊢; assumption
    . simp at hk ⊢; qify at hk; assumption
  have hk''' : (1:ℚ)/k ≥ 0 := by positivity
  have hk'''' : k ≥ 1 := by simp at hk'; linarith
  have hdist : Section_4_3.dist ((1:ℚ)/j) ((1:ℚ)/k) ≤ (1:ℚ)/N := by
    rw [Section_4_3.dist_eq, abs_le']
    constructor <;> linarith
  simp [seq, hj'''', hk'''']
  convert hdist.trans _ using 2
  . simp
  . simp
  rw [div_le_iff₀, mul_comm, ←div_le_iff₀ hε]
  . exact le_of_lt hN
  simp at hN' ⊢; assumption

abbrev BoundedBy {n:ℕ} (a: Fin n → ℚ) (M:ℚ) :=
  ∀ i, |a i| ≤ M

/--
  Definition 5.1.12 (bounded sequences). Here we start sequences from 0 rather than 1 to align
  better with Mathlib conventions.
-/
lemma BoundedBy_def {n:ℕ} (a: Fin n → ℚ) (M:ℚ) :
  BoundedBy a M ↔ ∀ i, |a i| ≤ M := by rfl

abbrev Sequence.BoundedBy (a:Sequence) (M:ℚ) : Prop :=
  ∀ n, |a n| ≤ M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.BoundedBy_def (a:Sequence) (M:ℚ) :
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

abbrev Sequence.isBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.isBounded_def (a:Sequence) :
  a.isBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

/-- Example 5.1.13 -/
example : BoundedBy ![1,-2,3,-4] 4 := by
  intro i
  fin_cases i <;> norm_num

/-- Example 5.1.13 -/
example : ¬ ((fun n:ℕ ↦ (-1)^n * (n+1:ℚ)):Sequence).isBounded := by
  sorry

/-- Example 5.1.13 -/
example : ((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).isBounded := by
  use 1
  constructor
  · norm_num
  intro i
  simp
  obtain h | h := Decidable.em (0 ≤ i) <;> simp [h]

/-- Example 5.1.13
Hint: the lemmas `Even.neg_one_pow` and `Odd.neg_one_pow` will be useful
-/
example : ¬ ((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).isCauchy := by
  rw [Sequence.isCauchy_of_coe]
  by_contra h
  specialize h (1/2 : ℚ) (by norm_num)
  obtain ⟨ N, h ⟩ := h
  specialize h N (by omega) (N+1) (by omega)
  simp at h
  obtain h' | h' := Decidable.em (Even N)
  rw [Even.neg_one_pow h', Odd.neg_one_pow (Even.add_one h')] at h
  unfold Section_4_3.dist at h
  norm_num at h
  have h' : Odd N := by exact Nat.not_even_iff_odd.mp h'
  rw [Odd.neg_one_pow h'] at h
  have : Even (N+1) := by exact Odd.add_one h'
  rw [Even.neg_one_pow this] at h
  unfold Section_4_3.dist at h
  norm_num at h

/-- Lemma 5.1.14 -/
lemma bounded_of_finite {n:ℕ} (a: Fin n → ℚ) : ∃ M ≥ 0,  BoundedBy a M := by
  -- this proof is written to follow the structure of the original text.
  induction' n with n hn
  . use 0
    simp [BoundedBy_def]
  set a' : Fin n → ℚ := fun m ↦ a m
  obtain ⟨ M, hpos, hM ⟩ := hn a'
  have h1 : BoundedBy a' (M + |a n|) := by
    intro m
    apply (hM m).trans
    simp
  have h2 : |a n| ≤ M + |a n| := by simp [hpos]
  use M + |a n|
  constructor
  . positivity
  intro m
  rcases Fin.eq_castSucc_or_eq_last m with hm | hm
  . obtain ⟨ j, hj ⟩ := hm
    convert h1 j
    simp [hj]
  convert h2
  simp [hm]

/-- Lemma 5.1.15 (Cauchy sequences are bounded) / Exercise 5.1.1 -/
lemma Sequence.isBounded_of_isCauchy {a:Sequence} (h: a.isCauchy) : a.isBounded := by
  sorry

end Chapter5
