import Mathlib.Tactic
import Analysis.Section_4_3

/-!
# Analysis I, Section 5.1

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.
-/

namespace Chapter5
variable (ε : ℚ)

/-!
Main constructions and results of this section:

- Notion of a sequence of rationals
- Notions of `ε`-steadiness, eventual `ε`-steadiness, and Cauchy sequences

-/


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

-- Notice how the delaborator prints this as `↑fun n ↦ ↑n ^ 2 : Sequence`.
#check Sequence.ofNatFun (fun n ↦ n ^ 2)

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
abbrev Rat.Steady (ε: ℚ) (a: Chapter5.Sequence) : Prop :=
  ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m)

lemma Rat.steady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m) := by rfl

namespace Chapter5

/--
5.1.3 - definition of ε-steadiness for a sequence starting at 0
-/
lemma Rat.Steady.coe (ε : ℚ) (a:ℕ → ℚ) :
    ε.Steady a ↔ ∀ n m : ℕ, ε.Close (a n) (a m) := by
  constructor
  · intro h n m
    specialize h n (by simp) m (by simp)
    simp_all
  intro h n hn m hm
  lift n to ℕ using hn
  lift m to ℕ using hm
  simp [h n m]

/--
Not in textbook: the sequence 2, 2 ... is 1-steady
Intended as a demonstration of `Rat.Steady.coe`
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  simp [Rat.Steady.coe, Rat.Close]

/--
Compare: if you need to work with `Rat.Steady` on the coercion directly, there will be side conditions `hn : n ≥ 0` and `hm : m ≥ 0` that you will need to deal with.

simp_all [Rat.Steady, Rat.Close, Sequence.n0_coe, Sequence.eval_coe_at_int]
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  unfold Rat.Steady Rat.Close
  intro n hn m hm
  simp_all [Sequence.n0_coe, Sequence.eval_coe_at_int]

/--
Example 5.1.5

The sequence `1, 0, 1, 0, ...` is 1-steady.
-/
example : (1:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m
  -- Split into 4 cases base on whether n and m are even or odd
  obtain h | h := Decidable.em (Even n) <;> obtain h' | h' := Decidable.em (Even m)
  all_goals {
    -- In each case, we know the exact value of a n and a m
    simp [h, h']
    unfold Rat.Close
    norm_num
  }

/--
Example 5.1.5

The sequence `1, 0, 1, 0, ...` is not ½-steady.
-/
example : ¬ (0.5:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h
  specialize h 0 1
  unfold Rat.Close at h
  norm_num at h

/--
Example 5.1.5

The sequence 0.1, 0.01, 0.001, ... is 0.1-steady.
-/
example : (0.1:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m
  unfold Rat.Close
  wlog h : m ≤ n
  · specialize this m n (by linarith)
    rwa [abs_sub_comm]
  rw [abs_sub_comm, abs_of_nonneg (by
    have : (10:ℚ) ^ (-(n:ℤ)-1) ≤ (10:ℚ) ^ (-(m:ℤ)-1) := by
      gcongr
      norm_num
    linarith)]
  rw [show  (0.1:ℚ) = (10:ℚ)^(-1:ℤ) - 0 by norm_num]
  gcongr
  norm_num
  linarith
  positivity

/--
Example 5.1.5

The sequence 0.1, 0.01, 0.001, ... is not 0.01-steady. Left as an exercise.
-/
example : ¬(0.01:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by sorry

/-- Example 5.1.5

The sequence 1, 2, 4, 8, ... is not ε-steady for any ε. Left as an exercise.
-/
example (ε:ℚ) : ¬ ε.Steady ((fun n:ℕ ↦ (2 ^ (n+1):ℚ) ):Sequence) := by sorry

/-- Example 5.1.5

The sequence 2, 2, 2, ... is ε-steady for any ε > 0.
-/
example (ε:ℚ) (hε: ε>0) : ε.Steady ((fun _:ℕ ↦ (2:ℚ) ):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m
  unfold Rat.Close
  norm_num
  positivity

/--
The sequence 10, 0, 0, ... is 10-steady.
-/
example : (10:ℚ).Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m
  unfold Rat.Close
  -- Split into 4 cases based on whether n and m are 0 or not
  obtain h | h := Decidable.em (n = 0) <;> obtain h' | h' := Decidable.em (m = 0) <;> simp [h, h']


/--
The sequence 10, 0, 0, ... is not ε-steady for any smaller value of ε.
-/
example (ε:ℚ) (hε:ε<10):  ¬ ε.Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  intro h
  rw [Rat.Steady.coe] at h
  specialize h 0 1
=======
-/
example : (1:ℚ).Steady (fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)) := by
  rw [Rat.Steady.coe]
  intro n m
  obtain h | h := Decidable.em (Even n)
  obtain h' | h' := Decidable.em (Even m)

  simp [h, h']
  unfold Rat.Close
  norm_cast

  simp [h, h']
  unfold Rat.Close
  norm_cast

  obtain h' | h' := Decidable.em (Even m)

  simp [h, h']
  unfold Rat.Close
  norm_cast

  simp [h, h']
  unfold Rat.Close
  norm_cast


/-- Example 5.1.5 -/
example : ¬ (0.5:ℚ).Steady (fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)) := by
  rw [Rat.Steady.coe]
  by_contra h
  specialize h 0 1
  dsimp at h
  unfold Rat.Close at h
  norm_num at h

/-- Example 5.1.5 -/
example : (0.1:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m
  unfold Rat.Close
  wlog h : m ≤ n
  · specialize this m n (by linarith)
    rwa [abs_sub_comm]
  rw [show (10: ℚ) ^ (-(m:ℤ) - 1) = (10: ℚ) ^ ((-(m:ℤ)) + (-1))  by congr, ← Section_4_3.zpow_add]
  rw [show (10: ℚ) ^ (-(n:ℤ) - 1) = (10: ℚ) ^ ((-(n:ℤ)) + (-1))  by congr, ← Section_4_3.zpow_add]
  rw [show 10 ^ (-(n:ℤ)) * 10 ^ (-1:ℤ) - 10 ^ (-(m:ℤ)) * 10 ^ (-1:ℤ) = (10 ^ (-1:ℤ)) * (10 ^ (-(n:ℤ)) - 10 ^ (-(m:ℤ)):ℚ) by ring]
  rw [abs_mul]
  rw [show |(10:ℚ) ^ (-1:ℤ)| = 0.1 by norm_num]
  suffices : |(10:ℚ) ^ (-(n:ℤ)) - 10 ^ (-(m:ℤ))| ≤ 1
  linarith
  have : (10:ℚ) ^ (-(n:ℤ)) ≤ (10:ℚ) ^ (-(m:ℤ)) := by
    gcongr
    norm_num
  rw [abs_sub_comm]
  rw [abs_of_nonneg (by linarith)]
  clear this
  rw [show (1:ℚ) = (10:ℚ)^(0:ℤ) - 0 by norm_num]
  gcongr
  norm_num
  omega
  positivity

/-- Example 5.1.5 -/
example (ε:ℚ) : ¬ ε.Steady ((fun n:ℕ ↦ (2 ^ (n+1):ℚ) ):Sequence) := by
  intro h
  rw [Rat.Steady.coe] at h
  specialize h 0
  obtain ⟨ n, hn ⟩ := exists_nat_gt ε
  specialize h n
  dsimp at h
  unfold Rat.Close at h
  norm_num at h
  rw [abs_sub_comm] at h
  have : (2:ℚ)^1 ≤ 2 ^ (n + 1) := by
    gcongr
    norm_num
    omega
  norm_num at this
  rw [abs_of_nonneg (by linarith)] at h
  clear this
  have : (2:ℚ) ^ (n + 1) - 2 < (n:ℚ) := by linarith
  clear h hn ε
  suffices h : (2:ℚ) ^ (n + 1) - 2 ≥ (n:ℚ)
  linarith
  clear this
  induction' n with n IH
  norm_num
  rw [show (2:ℚ) ^ (n + 1 + 1) = (2:ℚ) ^ (n + 1) + (2:ℚ) ^ (n + 1) by ring]
  suffices : (2:ℚ) ^ (n + 1) ≥ 1
  push_cast
  linarith
  rw [show (1:ℚ) = (2:ℚ) ^ 0 by norm_num]
  gcongr
  norm_num
  omega

/-- Example 5.1.5 -/
example (ε:ℚ) (hε: ε>0) : ε.Steady ((fun _:ℕ ↦ (2:ℚ) ):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m
  unfold Rat.Close
  norm_num
  positivity

def TenZeroZeroFun := (fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ))

def TenZeroZero := ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence)

example : (10:ℚ).Steady (TenZeroZeroFun:Sequence) := by
  rw [Rat.Steady.coe]
  unfold TenZeroZeroFun
  intro n m
  unfold Rat.Close
  obtain h | h := Decidable.em (n = 0)
  all_goals {
    obtain h' | h' := Decidable.em (m = 0)
    simp [h]
    all_goals simp [h, h']
  }

example (ε:ℚ) (hε:ε<10):  ¬ ε.Steady TenZeroZero := by
  unfold TenZeroZero
  intro h
  rw [Rat.Steady.coe] at h
  specialize h 0 1
  dsimp at h
>>>>>>> 919091b (Fill in sorries)
  unfold Rat.Close at h
  norm_num at h
  linarith

variable (n₁ n₀ : ℤ)

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

lemma Rat.Steady.coe_from_coe (ε : ℚ) (n₁ : ℕ) (a:ℕ → ℚ) :
    ε.Steady ((a:Sequence).from n₁) ↔ ∀ n ≥ n₁, ∀ m ≥ n₁, ε.Close (a n) (a m) := by
  constructor
  · intro h n hn m hm
    specialize h n (by simp ; omega) m (by simp ; omega)
    simp_all [hn, hm, h]

  intro h n hn m hm
  simp at hn hm
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  simp_all [hn, hm]

end Chapter5

/-- Definition 5.1.6 (Eventually ε-steady) -/
abbrev Rat.EventuallySteady (ε: ℚ) (a: Chapter5.Sequence) : Prop :=
  ∃ N ≥ a.n₀, ε.Steady (a.from N)

lemma Rat.eventuallySteady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.EventuallySteady a ↔ ∃ N ≥ a.n₀, ε.Steady (a.from N) := by rfl

lemma Rat.EventuallySteady.coe (ε: ℚ) (a: ℕ → ℚ) :
  ε.EventuallySteady a ↔ ∃ N:ℕ, ε.Steady ((a:Chapter5.Sequence).from N) := by
  constructor
  intro h
  rw [Rat.eventuallySteady_def] at h
  simp at h
  obtain ⟨ N, hN, h' ⟩ := h
  lift N to ℕ using hN
  use N
  intro h
  obtain ⟨ N, h' ⟩ := h
  rw [Chapter5.Rat.Steady.coe_from_coe] at h'
  use N
  simp
  rw [Chapter5.Rat.Steady.coe_from_coe]
  exact h'

namespace Chapter5

def bassel := ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence)

/-- Example 5.1.7 -/
lemma Sequence.ex_5_1_7_a : ¬ (0.1:ℚ).Steady bassel := by
  unfold bassel
  intro h
  rw [Rat.Steady.coe] at h
  specialize h 0 3
  dsimp at h
  unfold Rat.Close at h
  norm_num at h
  rw [abs_of_nonneg (by positivity)] at h
  norm_num at h

lemma Sequence.ex_5_1_7_b : (0.1:ℚ).Steady (bassel.from 10) := by
  unfold bassel
  rw [Rat.Steady]
  intro n hn m hm
  simp at hn hm
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  norm_cast at hn hm
  simp [hn, hm]
  unfold Rat.Close
  wlog h : m ≤ n
  specialize this m n (by omega) (by omega) (by omega)
  rwa [abs_sub_comm] at this
  rw [abs_sub_comm]
  have : ((n:ℚ) + 1)⁻¹ ≤ ((m:ℚ) + 1)⁻¹ := by gcongr
  rw [abs_of_nonneg (by linarith)]
  rw [show (0.1:ℚ) = (10:ℚ)⁻¹  - 0 by norm_num]
  gcongr
  norm_cast
  omega
  positivity

lemma Sequence.ex_5_1_7_c : (0.1:ℚ).EventuallySteady bassel := by
  use 10
  constructor
  simp [bassel]
  exact ex_5_1_7_b

/--
Example 5.1.7

The sequence 10, 0, 0, ... is eventually ε-steady for every ε > 0. Left as an exercise.
-/
lemma Sequence.ex_5_1_7_d {ε:ℚ} (hε:ε>0) :
    ε.EventuallySteady ((fun n:ℕ ↦ if n=0 then (10:ℚ) else (0:ℚ) ):Sequence) := by
  use 1
  constructor
  simp
  unfold Rat.Steady
  intro n hn m hm
  simp at hn hm
  simp [show 0 ≤ n by omega, show 0 ≤ m by omega, hn, hm, show ¬(n ≤ 0) by omega, show ¬(m ≤ 0) by omega]
  unfold Rat.Close
  norm_num
  positivity

abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℚ), ε.EventuallySteady a

lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℚ), ε.EventuallySteady a := by rfl

/-- Definition of Cauchy sequences, for a sequence starting at 0 -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℚ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (a j) (a k) ≤ ε := by
  constructor
  intro h
  intro ε hε
  unfold Sequence.IsCauchy at h
  specialize h ε hε
  unfold Rat.EventuallySteady at h
  obtain ⟨ N, hN, h' ⟩ := h
  lift N to ℕ using hN

  use N
  intro j hj k hk
  unfold Rat.Steady at h'
  simp at h'
  have : max (0 : ℤ) N = N := by omega

  specialize h' j (by omega)
  specialize h' k (by omega)

  unfold Rat.Close at h'
  simp at h'
  unfold Section_4_3.dist
  simp [hj, hk] at h'
  exact h'

  -- other implication

  intro h
  unfold Sequence.IsCauchy
  intro ε hε
  unfold Rat.EventuallySteady

  specialize h ε hε
  obtain ⟨ N, h' ⟩ := h
  use max N 0
  constructor
  · simp
  unfold Rat.Steady
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
  unfold Rat.Close
  exact h'

example : ((fun _:ℕ ↦ (3:ℚ)):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  intro ε hε
  use 0
  intro j hj k hk
  unfold Section_4_3.dist
  norm_num
  positivity

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℚ) :
    (mk' n₀ a).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N,
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
  unfold Rat.Steady at h'
  dsimp at h'
  rw [show max n₀ N = N by omega] at *
  specialize h' j (by omega) k (by omega)
  simp [show n₀ ≤ j by omega, hj, show n₀ ≤ k by omega, hk] at h'
  trivial

  intro h
  intro ε hε

  specialize h ε hε
  simp at h
  obtain ⟨ N, hN, h' ⟩ := h

  use max n₀ N
  constructor
  · simp
  intro n hn m hm
  simp at hn hm
  simp [hn, hm]

  specialize h' n (by omega) m (by omega)
  simp [hn, hm] at h'
  exact h'


noncomputable def Sequence.sqrt_two : Sequence :=
  (fun n:ℕ ↦ ((⌊ (Real.sqrt 2)*10^n ⌋ / 10^n):ℚ))

/--
  Example 5.1.10. (This requires extensive familiarity with Mathlib's API for the real numbers.)
-/
theorem Sequence.ex_5_1_10_a : (1:ℚ).Steady sqrt_two := by sorry

/--
  Example 5.1.10. (This requires extensive familiarity with Mathlib's API for the real numbers.)
-/
theorem Sequence.ex_5_1_10_b : (0.1:ℚ).Steady (sqrt_two.from 1) := by sorry

theorem Sequence.ex_5_1_10_c : (0.1:ℚ).EventuallySteady sqrt_two := by sorry


/-- Proposition 5.1.11 -/
theorem Sequence.IsCauchy.harmonic : (mk' 1 (fun n ↦ (1:ℚ)/n)).IsCauchy := by
  rw [IsCauchy.mk]
  intro ε hε
  -- We go by reverse from the book - first choose N such that N > 1/ε
  obtain ⟨ N, hN : N > 1/ε ⟩ := exists_nat_gt (1 / ε)
  use N
  have hN' : N > 0 := by
    have : (1/ε) > 0 := by positivity
    have hN := this.trans hN
    norm_cast at *
  constructor
  . norm_cast
  intro j hj k hk
  lift j to ℕ using (by linarith)
  lift k to ℕ using (by linarith)
  norm_cast at hj hk
  simp [show j ≥ 1 by linarith, show k ≥ 1 by linarith]

  have hdist : Section_4_3.dist ((1:ℚ)/j) ((1:ℚ)/k) ≤ (1:ℚ)/N := by
    rw [Section_4_3.dist_eq, abs_le']
    /-
    We establish the following bounds:
    - 1/j ∈ [0, 1/N]
    - 1/k ∈ [0, 1/N]
    These imply that the distance between 1/j and 1/k is at most 1/N - when they are as "far apart" as possible.
    -/
    have hj'' : 1/j ≤ (1:ℚ)/N := by gcongr
    have hj''' : (0:ℚ) ≤ 1/j := by positivity
    have hk'' : 1/k ≤ (1:ℚ)/N := by gcongr
    have hk''' : (0:ℚ) ≤ 1/k := by positivity
    constructor <;> linarith
  convert hdist.trans _ using 2
  . simp
  . simp
  rw [div_le_iff₀ (by positivity), mul_comm, ←div_le_iff₀ hε]
  exact le_of_lt hN

abbrev BoundedBy {n:ℕ} (a: Fin n → ℚ) (M:ℚ) :=
  ∀ i, |a i| ≤ M

/--
  Definition 5.1.12 (bounded sequences). Here we start sequences from 0 rather than 1 to align
  better with Mathlib conventions.

  -- should we enforce n₀ ≤ i?
-/
lemma boundedBy_def {n:ℕ} (a: Fin n → ℚ) (M:ℚ) :
  BoundedBy a M ↔ ∀ i, |a i| ≤ M := by rfl

abbrev Sequence.BoundedBy (a:Sequence) (M:ℚ) : Prop :=
  ∀ n, |a n| ≤ M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℚ) :
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

lemma Sequence.BoundedBy_of_coe (a : (ℕ → ℚ)) (M:ℚ) :
  (a:Sequence).BoundedBy M  ↔ ∀ n, |a n| ≤ M := by
  unfold BoundedBy
  simp
  constructor
  intro h n
  specialize h n
  simp at h
  exact h

  intro h n
  obtain npos | nneg := le_or_lt 0 n
  lift n to ℕ using npos
  simp only [Nat.cast_nonneg, ↓reduceIte, Int.toNat_natCast]
  exact h n

  have Mpos := (Section_4_3.abs_nonneg (a 0)).trans (h 0)
  simp [Int.not_le.mpr nneg, Mpos]

lemma boundedBy_of_boundedBy_of_lt {a b : ℚ} {s : Sequence} (h : a ≤ b) ( hs : s.BoundedBy a) : s.BoundedBy b := by
  intro n
  specialize hs n
  linarith

abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.isBounded_def (a:Sequence) :
  a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

lemma Sequence.IsBounded.coe (a : (ℕ → ℚ))
: (a:Sequence).IsBounded ↔ ∃ M ≥ 0, ∀ i, |a i| ≤ M := by
  unfold IsBounded
  constructor
  intro h
  obtain ⟨ M, h ⟩ := h
  rw [BoundedBy_of_coe] at h
  use M

  intro h
  obtain ⟨ M, h ⟩ := h
  use M
  rw [BoundedBy_of_coe]
  exact h

lemma isBounded_iff_of_minimum (m₀ : ℚ) (s : Sequence) :
  s.IsBounded ↔ ∃ M > m₀, s.BoundedBy  M := by
  constructor
  intro h
  obtain ⟨ M, h1, h2 ⟩ := h
  use (max m₀ M) + 1
  constructor
  exact lt_add_of_le_of_pos (le_max_left m₀ M) rfl
  have : M ≤ (max m₀ M + 1) := by linarith [le_max_right m₀ M]
  exact boundedBy_of_boundedBy_of_lt this h2

  intro h
  obtain ⟨ M, h1, h2 ⟩ := h
  use max 0 M
  constructor
  positivity
  exact boundedBy_of_boundedBy_of_lt (le_max_right 0 M) h2




/-- Example 5.1.13 -/
example : BoundedBy ![1,-2,3,-4] 4 := by
  intro i
  fin_cases i <;> norm_num

/-- Example 5.1.13 -/
example : ¬ ((fun n:ℕ ↦ (-1)^n * (n+1:ℚ)):Sequence).IsBounded := by
  by_contra h
  rw [Sequence.IsBounded.coe] at h
  obtain ⟨ M, h1, h2 ⟩ := h
  have ⟨ M', hM' ⟩ := exists_nat_gt M
  specialize h2 M'
  rw [abs_mul] at h2
  simp at h2
  rw [abs_of_nonneg (by positivity)] at h2
  linarith

/-- Example 5.1.13 -/
example : ((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsBounded := by
  use 1
  constructor
  · norm_num
  intro i
  simp
  obtain h | h := Decidable.em (0 ≤ i) <;> simp [h]

/-- Example 5.1.13
Hint: the lemmas `Even.neg_one_pow` and `Odd.neg_one_pow` will be useful
-/
example : ¬ ((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
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
lemma IsBounded.finite {n:ℕ} (a: Fin n → ℚ) : ∃ M ≥ 0,  BoundedBy a M := by
  -- this proof is written to follow the structure of the original text.
  induction' n with n hn
  . use 0
    simp [boundedBy_def]
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
lemma Sequence.isBounded_of_isCauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  sorry

end Chapter5
