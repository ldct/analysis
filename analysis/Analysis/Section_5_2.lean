import Mathlib.Tactic
import Analysis.Section_5_1


/-!
# Analysis I, Section 5.2: Equivalent Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of an ε-close and eventually ε-close sequences of rationals.
- Notion of an equivalent Cauchy sequence of rationals.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


abbrev Rat.CloseSeq (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Rat.EventuallyClose (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∃ N, ε.CloseSeq (a.from N) (b.from N)

namespace Chapter5

/-- Definition 5.2.1 ($ε$-close sequences) -/
lemma Rat.closeSeq_def (ε: ℚ) (a b: Sequence) :
    ε.CloseSeq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n) := by rfl

-- todo rename
theorem Rat.Close_of_coe_coe (ε: ℚ) (a b: ℕ → ℚ)
  : ε.CloseSeq (a:Sequence) (b:Sequence) ↔ ∀ n, ε.Close (a n) (b n) := by
  rw [Rat.closeSeq_def]
  constructor
  intro h
  intro n
  specialize h n
  grind [Sequence.n0_coe, Nat.cast_nonneg, Sequence.eval_coe_at_int]

  intro h n h1 h2
  simp
  simp at h1 h2
  lift n to ℕ using h1
  simp
  exact h n


example : (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ ((-1)^n:ℚ)))
((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  rw [Rat.Close_of_coe_coe]
  intro n
  unfold Rat.Close
  obtain h | h := Decidable.em (Even n)
  simp [h]
  norm_num
  rw [abs_of_nonneg]
  norm_num
  simp at h
  simp [h]
  norm_num
  rw [abs_of_nonneg]
  norm_num

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady (fun n:ℕ ↦ ((-1)^n:ℚ))
:= by
  rw [Rat.Steady.coe]
  intro h
  specialize h 0 1
  unfold Rat.Close at h
  norm_num at h

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence)
:= by
  rw [Rat.Steady.coe]
  intro h
  specialize h 0 1
  unfold Rat.Close at h
  norm_num at h
  rw [abs_of_nonneg (by norm_num)] at h
  norm_num at h


/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_def (ε: ℚ) (a b: Sequence) :
    ε.EventuallyClose a b ↔ ∃ N, ε.CloseSeq (a.from N) (b.from N) := by rfl

example (N : ℤ) : (N ≤ N.toNat) := by exact Int.self_le_toNat N

lemma toNat_idemp (n : ℤ) : ((n.toNat):Int).toNat = n.toNat := rfl

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventually_close_of_coe_coe (ε: ℚ) (a b: ℕ → ℚ) :
    ε.EventuallyClose (a:Sequence) (b:Sequence) ↔  ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  constructor
  intro h
  rw [Rat.eventuallyClose_def] at h
  obtain ⟨ N, hN ⟩ := h
  rw [Rat.closeSeq_def] at hN
  use N.toNat
  intro n hn
  specialize hN n
  simp at hN
  have l := Int.toNat_le.mp hn
  specialize hN l
  simp [l] at hN
  unfold Rat.Close at hN
  exact hN

  intro h
  obtain ⟨ N, hN ⟩ := h
  use N
  rw [Rat.closeSeq_def]
  simp
  intro n hn
  simp [hn]
  lift n to ℕ using (by omega)
  norm_cast at hn
  simp
  specialize hN n hn
  rw [Rat.Close]
  exact hN

/-- Example 5.2.5 -/
example : ¬ (0.1:ℚ).CloseSeq (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1))
  (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  rw [Rat.Close_of_coe_coe]
  intro h
  specialize h 0
  simp [Rat.Close] at h
  norm_num at h
  rw [abs_of_nonneg (by norm_num)] at h
  linarith

example : (0.1:ℚ).EventuallyClose (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1))
  (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  rw [Rat.eventually_close_of_coe_coe]
  use 1
  intro n hn
  rw [add_sub_sub_cancel, abs_of_nonneg (by positivity)]
  have : (10:ℚ) ^ (-(n:ℤ) - 1) ≤ (10:ℚ)^(-2:ℤ) := by gcongr <;> grind
  norm_num at this
  linarith

example : (0.01:ℚ).EventuallyClose (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1))
  (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  rw [Rat.eventually_close_of_coe_coe]
  use 2
  intro n hn
  rw [add_sub_sub_cancel, abs_of_nonneg (by positivity)]
  have : (10:ℚ) ^ (-(n:ℤ) - 1) ≤ (10:ℚ)^(-3:ℤ) := by gcongr <;> grind
  norm_num at this
  linarith

/-- Definition 5.2.6 (Equivalent sequences) -/
abbrev Sequence.Equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.EventuallyClose a b

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_def (a b: ℕ → ℚ) :
    Sequence.Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose a b := by rfl

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_iff (a b: ℕ → ℚ) : Sequence.Equiv a b ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  constructor
  intro h ε εpos
  specialize h ε εpos
  rw [Rat.eventually_close_of_coe_coe] at h
  exact h

  intro h ε εpos
  rw [Rat.eventually_close_of_coe_coe]
  exact h ε εpos


/-- Proposition 5.2.8 -/
lemma Sequence.equiv_example :
  -- This proof is perhaps more complicated than it needs to be; a shorter version may be
  -- possible that is still faithful to the original text.
  Sequence.Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)
  rw [equiv_iff]
  intro ε hε
  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := calc
    _ = |((1:ℚ) + (10:ℚ)^(-(n:ℤ)-1)) - ((1:ℚ) - (10:ℚ)^(-(n:ℤ)-1))| := rfl
    _ = |2 * (10:ℚ)^(-(n:ℤ)-1)| := by ring_nf
    _ = _ := abs_of_nonneg (by positivity)
  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn; rw [hab n]; gcongr; norm_num
  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := calc
      _ = 2 / (10:ℚ)^(N+1) := by
        field_simp
        simp [mul_assoc, ←Section_4_3.pow_eq_zpow, ←zpow_add₀ (show 10 ≠ (0:ℚ) by norm_num)]
      _ ≤ _ := by
        gcongr
        apply le_trans _ (pow_le_pow_left₀ (show 0 ≤ (2:ℚ) by norm_num)
          (show (2:ℚ) ≤ 10 by norm_num) _)
        convert Nat.cast_le.mpr (Section_4_3.two_pow_geq (N+1)) using 1 <;> try infer_instance
        all_goals simp
    choose N hN using exists_nat_gt (2 / ε)
    refine ⟨ N, (hN' N).trans ?_ ⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    grind [mul_comm]
  choose N hN using hN; use N; intro n hn
  linarith [hab' N n hn]

lemma Sequence.cauchy_of_equiv' {a b: ℕ → ℚ}
  (hab: Sequence.Equiv a b)
  (ha : (a:Sequence).IsCauchy)
: (b:Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe] at *
  intro ε εpos
  specialize ha (ε/4) (by positivity)
  obtain ⟨ N, hN ⟩ := ha
  specialize hab (ε/4) (by positivity)
  rw [Rat.eventually_close_of_coe_coe] at hab
  obtain ⟨ M, hM ⟩ := hab
  use max N M
  intro j hj k hk
  specialize hN j (le_of_max_le_left hj) k (le_of_max_le_left hk)
  have l1 := hM j (by exact le_of_max_le_right hj)
  have l2 := hM k (by exact le_of_max_le_right hk)
  unfold Section_4_3.dist at *
  rw [abs_le] at *
  constructor
  linarith
  linarith

/-- Exercise 5.2.1 -/
theorem Sequence.IsCauchy.equiv {a b: ℕ → ℚ} (hab: Sequence.Equiv a b) :
    (a:Sequence).IsCauchy ↔ (b:Sequence).IsCauchy := by
  constructor
  exact fun a_1 ↦ cauchy_of_equiv' hab a_1
  have : Equiv b a := by
    unfold Equiv at *
    simp_rw [Rat.eventually_close_of_coe_coe, abs_sub_comm] at *
    exact hab
  exact fun a_1 ↦ cauchy_of_equiv' this a_1

lemma Sequence.bounded_of_close' {ε:ℚ} {a b: ℕ → ℚ}
  (hab: ε.EventuallyClose a b)
  (ha : (a:Sequence).IsBounded)
: (b:Sequence).IsBounded := by
  rw [Rat.eventually_close_of_coe_coe] at hab
  obtain ⟨ n₀, hn₀ ⟩ := hab
  rw [Sequence.isBounded_def] at *

  obtain ⟨ M, hM1, hM2 ⟩ := ha
  rw [BoundedBy.coe] at hM2

  -- need to bound the finite b_0 ... b_n₀
  obtain ⟨ M3, _, hM3 ⟩  := finitePrefix b n₀
  use max |M3| (M + ε)
  constructor
  positivity
  rw [BoundedBy.coe]
  intro n
  have : n < n₀ ∨ n ≥ n₀ := by omega
  obtain h | h := this
  specialize hM3 n h

  simp
  left
  rw [le_abs]
  left
  exact hM3

  simp
  right
  specialize hn₀ n h
  specialize hM2 n

  rw [abs_le] at *
  constructor <;> linarith

/-- Exercise 5.2.2 -/
theorem Sequence.bounded_of_close {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded ↔ (b:Sequence).IsBounded := by
  constructor
  intro h
  exact bounded_of_close' hab h
  intro h
  have : ε.EventuallyClose b a := by
    rw [Rat.eventually_close_of_coe_coe] at *
    simp_rw [abs_sub_comm]
    exact hab
  exact bounded_of_close' this h

end Chapter5
