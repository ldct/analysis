import Mathlib.Tactic
import Analysis.Section_2_2

/-!
# Analysis I, Section 2.3

This file is a translation of Section 2.3 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of multiplication and exponentiation for the "Chapter 2" natural numbers,
  `Chapter2.Nat`

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" for pedagogical purposes.
-/

namespace Chapter2

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

instance Nat.instMul : Mul Nat where
  mul := mul

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
theorem Nat.zero_mul (m: Nat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod+m) _

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
theorem Nat.succ_mul (n m: Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

theorem Nat.one_mul' (m: Nat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]

theorem Nat.one_mul (m: Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem Nat.two_mul (m: Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ, succ_mul, one_mul']

/-- This lemma will be useful to prove Lemma 2.3.2. -/
lemma Nat.mul_zero (m: Nat) : m * 0 = 0 := by
  revert m; apply induction
  rw [zero_mul]
  intro n IH
  rw [succ_mul, IH, zero_add]

/-- This lemma will be useful to prove Lemma 2.3.2. -/
lemma Nat.mul_succ (n m: Nat) : n * m++ = n * m + n := by
  revert n; apply induction
  rw [zero_mul, zero_mul, add_zero]
  intro n IH
  rw [succ_mul, succ_mul, IH, add_assoc, add_assoc, add_succ, add_succ m, add_comm n]

/-- Lemma 2.3.2 (Multiplication is commutative) / Exercise 2.3.1 -/
lemma Nat.mul_comm (n m: Nat) : n * m = m * n := by
  revert m; apply induction
  rw [zero_mul, mul_zero]
  intro m IH
  rw [succ_mul, mul_succ, IH]

theorem Nat.mul_one (m: Nat) : m * 1 = m := by
  rw [mul_comm, one_mul]

/-- This lemma will be useful to prove Lemma 2.3.3. -/
lemma Nat.pos_mul_pos {n m: Nat} (h₁: n.IsPos) (h₂: m.IsPos) : (n * m).isPos := by
  revert n; apply induction
  intro h
  exfalso
  exact h rfl
  intro n IH h
  rw [succ_mul]
  exact add_pos_right (n * m) h₂

/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) / Exercise 2.3.2 -/
lemma Nat.mul_eq_zero_iff (n m: Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  intro h
  by_contra hnm
  rw [not_or] at hnm
  rcases hnm with ⟨ hn, hm ⟩
  replace hn : n.isPos := by exact hn
  replace hm : m.isPos := by exact hm
  have := pos_mul_pos hn hm
  trivial

  intro h
  cases h with
  | inl hn => rw [hn, zero_mul]
  | inr hm => rw [hm, mul_zero]

lemma Nat.ne_0 (n: Nat) : ¬ n ≠ 0 ↔ n=0 := by
  exact not_ne_iff

lemma Nat.factor_pos {n m: Nat} (h: (n * m).isPos) : n.isPos := by
  by_contra n_eq_0
  unfold Nat.isPos at n_eq_0
  replace n_eq_0 := (Nat.ne_0 n).mp n_eq_0
  rw [n_eq_0, zero_mul] at h
  unfold Nat.isPos at h
  trivial

lemma Nat.factors_pos {n m: Nat} (h: (n * m).isPos) : n.isPos ∧ m.isPos := by
  constructor
  exact factor_pos h
  rw [mul_comm] at h
  exact factor_pos h

/-- Proposition 2.3.4 (Distributive law)-/
theorem Nat.mul_add (a b c: Nat) : a * (b + c) = a * b + a * c := by
  -- This proof is written to follow the structure of the original text.
  revert c; apply induction
  . rw [add_zero]
    rw [mul_zero, add_zero]
  intro c habc
  rw [add_succ, mul_succ]
  rw [mul_succ, ←add_assoc, ←habc]

/-- Proposition 2.3.4 (Distributive law)-/
theorem Nat.add_mul (a b c: Nat) : (a + b)*c = a*c + b*c := by
  simp only [mul_comm, mul_add]

/-- Proposition 2.3.5 (Multiplication is associative) / Exercise 2.3.3 -/
theorem Nat.mul_assoc (a b c: Nat) : (a * b) * c = a * (b * c) := by
  revert c; apply induction
  . rw [mul_zero, mul_zero, mul_zero]
  intro c habc
  rw [mul_succ, mul_succ, habc, mul_add]

/-- (Not from textbook)  Nat is a commutative semiring. -/
instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_lt_mul_of_pos_right {a b c: Nat} (h: a < b) (hc: c.IsPos) : a * c < b * c := by
  -- This proof is written to follow the structure of the original text.
  rw [lt_iff_add_pos] at h
  obtain ⟨ d, hdpos, hd ⟩ := h
  apply_fun (· * c) at hd
  rw [add_mul] at hd
  have hdcpos : (d * c).IsPos := pos_mul_pos hdpos hc
  rw [lt_iff_add_pos]
  use d*c

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_right {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    a * c > b * c := mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_lt_mul_of_pos_left {a b c: Nat} (h: a < b) (hc: c.IsPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_left {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc



/-- Corollary 2.3.7 (Cancellation law) -/
lemma Nat.mul_cancel_right {a b c: Nat} (h: a * c = b * c) (hc: c.IsPos) : a = b := by
  -- This proof is written to follow the structure of the original text.
  have := trichotomous a b
  rcases this with hlt | heq | hgt
  . replace hlt := mul_lt_mul_of_pos_right hlt hc
    replace hlt := ne_of_lt _ _ hlt
    contradiction
  . assumption
  replace hgt := mul_gt_mul_of_pos_right hgt hc
  replace hgt := ne_of_gt _ _ hgt
  contradiction

lemma Nat.mul_le_mul_of_nonneg_left {a b c: Nat} (h1: a ≤ b) : c * a ≤ c * b := by
    rcases h1 with ⟨ d, hd ⟩
    use c * d
    rw [hd, mul_add]

/-- (Not from textbook) Nat is an ordered semiring. -/
instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := by
    use 1
    rfl
  mul_le_mul_of_nonneg_left := by
    intro a b c h1 _
    exact mul_le_mul_of_nonneg_left h1
  mul_le_mul_of_nonneg_right := by
    intro a b c h1 _
    rw [mul_comm a c, mul_comm b c]
    exact mul_le_mul_of_nonneg_left h1

lemma zero_le (n : Nat) : (0 : Nat) ≤ n := by
  use n
  rw [zero_add]

lemma zero_le_self : (0 : Nat) ≤ 0 := zero_le 0

/-- Proposition 2.3.9 (Euclid's division lemma) / Exercise 2.3.5 -/
theorem Nat.exists_div_mod (n :Nat) {q: Nat} (hq: q.IsPos) :
    ∃ m r: Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  revert n; apply induction
  use 0, 0
  constructor
  exact zero_le_self
  constructor
  rw [Nat.lt_iff_add_pos]
  use q
  constructor
  exact hq
  rw [zero_add]
  rw [zero_mul, add_zero]

  intro n IH
  rcases IH with ⟨ m, r, h0r, hrq, hnr ⟩

  have : r++ = q ∨ r++ ≠ q := by exact eq_or_ne (r++) q

  cases' this with h1 h2

  use m++, 0
  constructor
  exact zero_le_self
  constructor
  exact lt_of_le_of_lt h0r hrq
  rw [add_zero, succ_mul, hnr, ← add_succ, h1]

  use m, r.succ
  constructor

  exact zero_le (r++)
  constructor

  rw [Nat.lt_iff_succ_le r q] at hrq
  exact lt_of_le_of_ne hrq h2

  rw [hnr, add_succ]



/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
abbrev Nat.pow (m n: Nat) : Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
theorem Nat.pow_zero (m: Nat) : m ^ (0:Nat) = 1 := recurse_zero (fun _ prod ↦ prod * m) _

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
theorem Nat.zero_pow_zero : (0:Nat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
theorem Nat.pow_succ (m n: Nat) : (m:Nat) ^ n++ = m^n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

theorem Nat.pow_one (m: Nat) : m ^ (1 : Nat) = m := by
  have : 1 = 0++ := by decide
  rw [this, pow_succ]
  exact rfl

lemma Nat.pow_2_eq_sq (a : Nat) : a ^ (2 : Nat) = a * a := by
  have : 2 = 1++ := by decide
  rw [this, pow_succ, pow_one]

lemma Nat.add_cancel_left' (a b c: Nat) : a + b = a + c ↔  b = c := by
  constructor
  intro h
  exact add_left_cancel a b c h
  intro h
  rw [h]

/-- Exercise 2.3.4-/
theorem Nat.sq_add_eq (a b: Nat) :
    (a + b) ^ (2 : Nat) = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by
  rw [pow_2_eq_sq, pow_2_eq_sq, pow_2_eq_sq, mul_add, add_mul, add_assoc, add_assoc, add_cancel_left', show (2 : Nat) = 1 + 1 by decide, add_mul, add_mul, one_mul, add_mul, mul_comm]
  rw [add_assoc, add_cancel_left']

end Chapter2
