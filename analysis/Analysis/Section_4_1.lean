import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

import Plausible

/-!
# Analysis I, Section 4.1

This file is a translation of Section 4.1 of Analysis I to Lean 4.  All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of ℕ

- Equivalence with the Mathlib integers `_root_.Int` (or `ℤ`), which we will use going forward.

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by
      intro ⟨a, b⟩
      rw [Nat.add_left_cancel_iff]
    symm := by
      intro ⟨a, b⟩ ⟨c, d⟩ h
      linarith
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2
      simp at h1 h2 ⊢
      have h3 := congrArg₂ (· + ·) h1 h2
      simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

def five_minus_three : PreInt := ⟨ 5, 3 ⟩
def six_minus_four : PreInt := ⟨ 6, 4 ⟩
def six_minus_three : PreInt := ⟨ 6, 3 ⟩
example : five_minus_three ≈ six_minus_four := rfl

example (a b : PreInt) : a ≈ b ↔ b ≈ a := by
  exact eq_comm

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
@[simp high]
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b := by
  constructor
  . exact Quotient.exact
  intro h; exact Quotient.sound h

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by
  apply Quot.ind _ n; intro ⟨ a, b ⟩
  use a, b; rfl

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [Setoid.r] at *
    omega
)

/-- Note: the operator precedence is parsed as (a —— b) + (c —— d)  -/
@[simp]
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

theorem Int.add_comm : ∀ a b: Int, a + b = b + a := by
    intro a b
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    simp
    omega

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a——b = a'——b') : (a*c+b*d)——(a*d+b*c) = (a'*c+b'*d)——(a'*d+b'*c) := by
  simp at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') : (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp at h1 h2
    convert mul_congr _ _ <;> simpa
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
@[simp]
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) :
    (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
      simp only [ofNat_eq, eq, add_zero]
      rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) :
    (n : Int) = (m : Int) ↔ n = m := by
      simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := by rfl

example : 3 = 4 —— 1 := by
  rw [Int.ofNat_eq, Int.eq]

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    intro a b h
    dsimp
    rw [Int.eq]
    whnf at h
    linarith
  )

@[simp]
theorem Int.neg_eq (a b:ℕ) : -(a——b) = b——a := rfl

example : -(3——5) = 5——3 := by rfl

abbrev Int.isPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.isNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.isPos ∨ x.isNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  have := _root_.trichotomous (r := LT.lt) a b
  rcases this with h_lt | h_eq | h_gt
  . obtain ⟨ c,rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, ?_, ?_ ⟩
    . linarith
    simp_rw [natCast_eq, neg_eq, eq]
    abel
  . left; simp_rw [h_eq, ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, ?_, ?_ ⟩
  . linarith
  simp_rw [natCast_eq, eq]
  abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.isPos → False := by
  rintro ⟨ rfl, ⟨ n, hn, hn' ⟩ ⟩
  simp [←natCast_ofNat] at hn'
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.isNeg → False := by
  rintro ⟨ rfl, ⟨ n, hn, hn' ⟩ ⟩
  simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn'
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.isPos ∧ x.isNeg → False := by
  rintro ⟨ ⟨ n, hn, rfl ⟩, ⟨ m, hm, hm' ⟩ ⟩
  simp_rw [natCast_eq, neg_eq, eq] at hm'
  linarith

@[simp]
theorem Int.eq_0' (a b : ℕ) : a——b = 0 ↔ a = b := by
  rw [show (0 : Int) = 0 —— 0 by rfl]
  constructor
  intro h
  simp at h
  omega
  intro h
  rw [h, eq]
  omega

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
AddGroup.ofLeftAxioms (by
  intro a b c
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
  obtain ⟨ c1, c2, rfl ⟩ := eq_diff c
  simp
  omega
) (by
  intro a
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  rw [show (0 : Int) = 0 —— 0 by rfl]
  simp
) (by
  intro a
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  simp
  omega
)

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := add_comm


lemma Int.mul_comm (x y : Int) : x * y = y * x := by
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, rfl ⟩ := eq_diff y
  simp
  ring

lemma Int.one_mul (x : Int) : 1 * x = x := by
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  rw [show (1 : Int) = 1 —— 0 by rfl]
  simp

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := by
    intro x y
    exact mul_comm x y
  mul_assoc := by
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp
    ring
  one_mul := by
    intro a
    exact one_mul a
  mul_one := by
    intro a
    rw [mul_comm]
    exact one_mul a

lemma Int.zero_mul (x : Int) : 0 * x = 0 := by
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  rw [show (0 : Int) = 0 —— 0 by rfl]
  simp

lemma Int.left_distrib (x y z : Int) : x * (y + z) = x * y + x * z := by
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, rfl ⟩ := eq_diff y
  obtain ⟨ e, f, rfl ⟩ := eq_diff z
  simp only [mul_eq, add_eq, eq]
  ring

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := by
    intro a b c
    exact left_distrib a b c
  right_distrib := by
    intro x y z
    simp only [mul_comm, left_distrib]
  zero_mul := zero_mul
  mul_zero := by
    intro a
    rw [mul_comm]
    exact zero_mul a

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a - b := by
  obtain ⟨ x, y, h1 ⟩ := eq_diff a
  obtain ⟨ p, q, h2 ⟩ := eq_diff b
  rw [h1, h2]

-- a rearrangement-type inequality on ℕ
lemma test (x y p q : ℕ)
(h : x * p + y * q = x * q + y * p) : x = y ∨ p = q := by
  by_cases h2 : p ≤ q
  · -- Case where p ≤ q
    have h3 : q = p + (q - p) := by omega
    rw [h3] at h
    have eq3 : y * (q - p) = x * (q - p) := by
      nlinarith
    by_cases h4 : 0 < (q - p)
    · -- Case where (q - p) > 0
      have h5 : y = x := by
        apply (mul_left_inj' (show (q - p : ℕ) ≠ 0 by omega)).mp
        omega
      left
      omega
    · -- Case where (q - p) ≤ 0
      have h7 : p = q := by omega
      right
      exact h7
  · -- Case where p > q
    have h5 : p = q + (p - q) := by omega
    rw [h5] at h
    have eq2 : x * (q + (p - q)) + y * q = x * q + y * (q + (p - q)) := by linarith
    have eq3 : x * (p - q) = y * (p - q) := by
      nlinarith
    by_cases h6 : (p - q) > 0
    · -- Case where (p - q) > 0
      have h7 : x = y := by
        apply (mul_left_inj' (show (p - q : ℕ) ≠ 0 by omega)).mp
        omega
      left
      omega
    · -- Case where (p - q) ≤ 0
      exfalso
      have h7 : p - q = 0 := by omega
      have h8 : p ≤ q := by omega
      linarith

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ⟨ x, y, h1 ⟩ := eq_diff a
  obtain ⟨ p, q, h2 ⟩ := eq_diff b
  rw [h1, h2, mul_eq] at h
  rw [show (0 : Int) = 0 —— 0 by rfl] at h
  simp at h
  rw [h1, h2]
  simp
  clear h1 h2
  exact test x y p q h


/- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  have : a * c - b * c = b * c - b * c := by congr
  simp at this
  have : (a - b) * c = 0 := by
    ring_nf
    exact this
  have := mul_eq_zero this
  rcases this with h | h
  have : (a - b) + b = 0 + b := by congr
  ring_nf at this
  exact this
  trivial

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := (∃ a:ℕ, m = n + a) ∧ n ≠ m

theorem Int.le_iff (n m:Int) : n ≤ m ↔ ∃ a:ℕ, m = n + a := by rfl

theorem Int.lt_iff (n m:Int): n < m ↔ (∃ a:ℕ, m = n + a) ∧ n ≠ m := by rfl

lemma Int.test (n m : Int) : n < m → m > n := by
  intro h
  exact h

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.gt_iff (a b:Int) : a > b ↔ ∃ n:ℕ, n ≠ 0 ∧ a = b + n := by
  rw [show a > b ↔ b < a by rfl]
  constructor
  intro h
  rw [lt_iff] at h
  rcases h.1 with ⟨ c, hc ⟩
  use c
  constructor
  intro h2
  rw [h2] at hc
  simp at hc
  have h3 := h.2.symm
  exact h3 hc
  exact hc
  intro h
  rcases h with ⟨ n, ⟨h1, h2⟩  ⟩
  rw [lt_iff]
  constructor
  use n
  intro h
  rw [h] at h2
  simp at h2
  rw [natCast_eq] at h2
  simp at h2
  exact h1 h2

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_gt_add_right {a b:Int} (c:Int) (h: a > b) : a+c > b+c := by
  rw [gt_iff] at *
  rcases h with ⟨ n, hn ⟩
  use n
  constructor
  exact hn.left
  have hn := hn.right
  rw [hn]
  ring

/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_left {a b c:Int} (hab : a > b) (hc: c > 0) : a*c > b*c := by
  rw [gt_iff] at *
  rcases hab with ⟨ n, ⟨hn1, hn2⟩⟩
  rcases hc with ⟨ m, ⟨hm1, hm2⟩⟩
  use n * m
  constructor
  positivity
  rw [hn2, hm2]
  simp
  ring

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: a > b) : -a < -b := by
  rw [gt_iff] at *
  rcases h with ⟨ n, ⟨hn1, hn2⟩⟩
  rw [lt_iff]
  constructor
  use n
  rw [hn2]
  ring
  rw [hn2]
  intro h
  ring_nf at h
  have h' : (-b - ↑n) + b = -b + b := by
    rw [h]
  rw [show  -(b : Int) + b = 0 by ring] at h'
  rw [show -(b : Int) - n + b = -n by ring] at h'
  simp at h'
  rw [natCast_eq] at h'
  simp at h'
  exact hn1 h'

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.gt_trans {a b c:Int} (hab: a > b) (hbc: b > c) : a > c := by sorry

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b c:Int) : a > b ∨ a < b ∨ a = b := by sorry

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b):= by sorry

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by sorry

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by sorry

/-- (Not from textbook) The order is decidable.  This exercise is only recommended for Lean experts. Alternatively, one can establish this fact in classical logic via `classical; exact Classical.decRel _`.  -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  sorry

/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_le := sorry
  le_antisymm := sorry
  le_total := sorry
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by sorry

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, P 0 ∧ ∀ n, P n → P (n+1) ∧ ¬ ∀ n, P n := by sorry

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg (n:Int) : n*n ≥ 0 := by sorry

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by sorry

/-- Not in textbook: create an equivalence between Int and ℤ.  This requires some familiarity with the API for Mathlib's version of the integers. -/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ a - b) (by
    sorry)
  invFun := sorry
  left_inv n := sorry
  right_inv n := sorry

/-- Not in textbook: equivalence preserves order -/
abbrev Int.equivInt_order : Int ≃o ℤ where
  toEquiv := equivInt
  map_rel_iff' := by sorry

/-- Not in textbook: equivalence preserves ring operations -/
abbrev Int.equivInt_ring : Int ≃+* ℤ where
  toEquiv := equivInt
  map_add' := by sorry
  map_mul' := by sorry

end Section_4_1
