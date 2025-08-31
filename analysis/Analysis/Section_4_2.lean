import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.2

This file is a translation of Section 4.2 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.2" rationals, `Section_4_2.Rat`, as formal differences `a // b` of
  integers `a b:ℤ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_2.PreRat`, which consists of formal differences without any equivalence imposed.)

- Field operations and order on these rationals, as well as an embedding of ℕ and ℤ.

- Equivalence with the Mathlib rationals `_root_.Rat` (or `ℚ`), which we will use going forward.

Note: here (and in the sequel) we use Mathlib's natural numbers `ℕ` and integers `ℤ` rather than
the Chapter 2 natural numbers and Section 4.1 integers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_2

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl := by
      intro a
      ring
    symm := by
      intro x y h
      rw [h]
    trans := by
      intro x y z hxy hyz
      suffices h : x.numerator * z.denominator * y.denominator= z.numerator * x.denominator * y.denominator
      field_simp [y.nonzero] at h
      exact h
      rw [mul_assoc, mul_comm z.denominator, ← mul_assoc, hxy, mul_assoc, mul_comm x.denominator, ← mul_assoc, hyz]
      ring
    }

@[simp]
theorem PreRat.eq (a b c d:ℤ) (hb: b ≠ 0) (hd: d ≠ 0) :
    (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

def PreRatZero : PreRat := ⟨ 0, 1, by decide ⟩

theorem PreRatZero.equiv (a : PreRat) : a ≈ PreRatZero ↔ a.numerator = 0 := by
  rw [PreRat.eq]
  simp [PreRatZero]

abbrev Rat := Quotient PreRat.instSetoid

/-- We give division a "junk" value of 0//1 if the denominator is zero -/
def Rat.formalDiv (a b:ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

@[simp]
lemma Rat.formalDiv_eq (a b : ℤ): Rat.formalDiv a b = Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩) := by rfl

infix:100 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Rationals) -/
@[grind]
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0): a // b = c // d ↔ a * d = c * b := by
  simp [hb, hd, Setoid.r]

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq_diff (n:Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quot.ind _ n; intro ⟨ a, b, h ⟩
  refine ⟨ a, b, h, ?_ ⟩
  simp [formalDiv, h]; rfl

/--
  Decidability of equality. Hint: modify the proof of `DecidableEq Int` from the previous
  section. However, because formal division handles the case of zero denominator separately, it
  may be more convenient to avoid that operation and work directly with the `Quotient` API.
-/
instance Rat.decidableEq : DecidableEq Rat := by
  intro a b
  have : ∀ (n:PreRat) (m: PreRat),
    Decidable (Quotient.mk PreRat.instSetoid n = Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    simp [Setoid.r]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Lemma 4.2.3 (Addition well-defined) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Setoid.r]
    grind
  )

/-- Definition 4.2.2 (Addition of rationals) -/
theorem Rat.add_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> grind

grind_pattern Rat.add_eq => (a // b) + (c // d)

/-- Lemma 4.2.3 (Multiplication well-defined) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp [Setoid.r, h1, h2, h1', h2'] at *
    grind
  )

/-- Definition 4.2.2 (Multiplication of rationals) -/
theorem Rat.mul_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> grind

grind_pattern Rat.mul_eq => (a // b) * (c // d)

/-- Lemma 4.2.3 (Negation well-defined) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by
    intro ⟨ a, b, h1 ⟩ ⟨ a', b', h2 ⟩ h3
    simp [Setoid.r, h1, h2] at *
    exact h3
  )

/-- Definition 4.2.2 (Negation of rationals) -/
@[grind]
theorem Rat.neg_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

/-- Embedding the integers in the rationals -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n:ℤ) // 1

instance Rat.instOfNat {n:ℕ} : OfNat Rat n where
  ofNat := (n:ℤ) // 1

@[grind]
theorem Rat.coe_Int_eq (a:ℤ) : (a:Rat) = a // 1 := rfl

theorem Rat.coe_Nat_eq (n:ℕ) : (n:Rat) = n // 1 := rfl

theorem Rat.of_Nat_eq (n:ℕ) : (ofNat(n):Rat) = (ofNat(n):Nat) // 1 := rfl

/-- intCast distributes over addition -/
@[norm_cast]
lemma Rat.intCast_add (a b:ℤ) : (a:Rat) + (b:Rat) = (a+b:ℤ) := by
  grind

@[norm_cast]
lemma Rat.natCast_add (a b:ℕ) : (a:Rat) + (b:Rat) = (a+b:ℕ) := by
  rw [show (a:Rat) = ((a:ℤ):Rat) by rfl, show (b:Rat) = ((b:ℤ):Rat) by rfl, Rat.intCast_add]
  norm_cast

/-- natCast distributes over successor -/
theorem Rat.natCast_succ (n: ℕ) : ((n + 1: ℕ): Rat) = (n: Rat) + 1 := by
  rw [show (1:Rat) = (1:ℕ) by rfl]
  norm_cast

@[simp, grind]
lemma Rat.div_zero (a : ℤ) : a // 0 = 0 // 1 := by rfl

lemma Rat.zero_div (a : ℤ): 0 // a = 0 // 1 := by
  obtain rfl | h := Decidable.em (a = 0) <;> grind

lemma Rat.intCast_mul (a b:ℤ) : (a:Rat) * (b:Rat) = (a*b:ℤ) := by
  grind

/-- intCast commutes with negation -/
lemma Rat.intCast_neg (a:ℤ) : - (a:Rat) = (-a:ℤ) := rfl

theorem Rat.coe_Int_inj : Function.Injective (fun n:ℤ ↦ (n:Rat)) := by
  intro a b h
  grind

lemma formalDiv_zero (a:ℤ) : a // 0 = 0 := by rfl

/--
  Whereas the book leaves the inverse of 0 undefined, it is more convenient in Lean to assign a
  "junk" value to this inverse; we arbitrarily choose this junk value to be 0.
-/
instance Rat.instInv : Inv Rat where
  inv := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ b // a) (by
    intro a b h
    obtain h1 | h2 := Classical.em (a ≈ PreRatZero)
    · have h3 : (b ≈ PreRatZero) := Setoid.trans (Setoid.symm h) h1
      rw [PreRatZero.equiv] at h1 h3
      grind [formalDiv_eq]

    · have h3 : ¬(b ≈ PreRatZero) := by
        by_contra h4
        have : a ≈ PreRatZero := Setoid.symm (Setoid.trans h4.symm h.symm)
        exact h2 this

      rw [PreRatZero.equiv] at h2 h3
      rw [eq _ _ h2 h3, mul_comm, ← h, mul_comm]
)

@[grind]
lemma Rat.inv_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a // b)⁻¹ = b // a := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

@[simp]
theorem Rat.inv_zero : (0:Rat)⁻¹ = 0 := rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.addGroup_inst : AddGroup Rat :=
AddGroup.ofLeftAxioms (by
  -- this proof is written to follow the structure of the original text.
  intro x y z
  obtain ⟨ a, b, hb , rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd , rfl ⟩ := eq_diff y
  obtain ⟨ e, f, hf , rfl ⟩ := eq_diff z
  have hbd : b*d ≠ 0 := Int.mul_ne_zero hb hd
  have hdf : d*f ≠ 0 := Int.mul_ne_zero hd hf
  have hbdf : b*d*f ≠ 0 := Int.mul_ne_zero hbd hf
  grind
)
 (by
  intro x
  obtain ⟨ a, b, hb , rfl ⟩ := eq_diff x
  rw [show (0:Rat) = 0 // 1 by rfl]
  grind
 ) (by
  intro a
  obtain ⟨ a, b, hb , rfl ⟩ := eq_diff a
  have : b * b ≠ 0 := by positivity
  rw [show (0:Rat) = 0 // 1 by rfl]
  grind
 )

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instAddCommGroup : AddCommGroup Rat where
  add_comm a b := by
    obtain ⟨ p, q, hb , rfl ⟩ := eq_diff a
    obtain ⟨ r, s, hd , rfl ⟩ := eq_diff b
    grind

@[grind]
lemma Rat.mul_comm (a b:Rat) : a * b = b * a := by
  obtain ⟨ p, q, hb , rfl ⟩ := eq_diff a
  obtain ⟨ r, s, hd , rfl ⟩ := eq_diff b
  grind

@[grind, simp]
lemma Rat.one_mul (a:Rat) : 1 * a = a := by
  obtain ⟨ p, q, hb , rfl ⟩ := eq_diff a
  rw [show (1:Rat) = 1 // 1 by rfl]
  grind

grind_pattern Rat.one_mul => 1 * a

-- example (a:Rat) : 1 * a = a := by grind

@[grind]
lemma Rat.mul_assoc (a b c:Rat) : (a * b) * c = a * (b * c) := by
  obtain ⟨ p, q, hb , rfl ⟩ := eq_diff a
  obtain ⟨ r, s, hs , rfl ⟩ := eq_diff b
  obtain ⟨ t, u, hu , rfl ⟩ := eq_diff c
  have hqs : q * s ≠ 0 := by positivity
  have hsu : s * u ≠ 0 := by positivity
  grind

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommMonoid : CommMonoid Rat where
  mul_comm := mul_comm
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one a := by
    rw [mul_comm]
    simp

lemma Rat.left_distrib (a b c:Rat) : a * (b + c) = a * b + a * c := by
  obtain ⟨ p, q, hq , rfl ⟩ := eq_diff a
  obtain ⟨ r, s, hs , rfl ⟩ := eq_diff b
  obtain ⟨ t, u, hu , rfl ⟩ := eq_diff c
  have hqs : q * s ≠ 0 := by positivity
  have hsu : s * u ≠ 0 := by positivity
  have hqu : q * u ≠ 0 := by positivity
  have hqsu : q * (s * u) ≠ 0 := by positivity
  have hqsqu : q * s * (q * u) ≠ 0 := by positivity
  grind

lemma Rat.zero_mul (a:Rat) : 0 * a = 0 := by
  obtain ⟨ p, q, hq , rfl ⟩ := eq_diff a
  rw [show (0:Rat) = 0 // 1 by rfl]
  grind

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommRing : CommRing Rat where
  left_distrib := left_distrib
  right_distrib a b c := by
    rw [mul_comm, left_distrib]
    grind
  zero_mul := zero_mul
  mul_zero a := by
    rw [mul_comm, zero_mul]
  mul_assoc := mul_assoc
  natCast_succ := natCast_succ

instance Rat.instRatCast : RatCast Rat where
  ratCast q := q.num // q.den

theorem Rat.natCast_eq (n:ℕ) : (n:Rat) = n // 1 := rfl

theorem Rat.ratCast_inj : Function.Injective (fun n:ℚ ↦ (n:Rat)) := by
  intro a b h
  dsimp at h
  rw [show (a:Rat) = a.num // a.den by rfl, show (b:Rat) = b.num // b.den by rfl] at h
  grind [Rat.eq_iff_mul_eq_mul, Rat.den_ne_zero]


theorem Rat.coe_Rat_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a/b:ℚ) = a // b := by
  set q := (a/b:ℚ)
  set num :ℤ := q.num
  set den :ℤ := (q.den:ℤ)
  have hden : den ≠ 0 := by simp [den, q.den_nz]
  change num // den = a // b
  rw [eq _ _ hden hb]
  qify
  have hq : num / den = q := Rat.num_div_den q
  rwa [div_eq_div_iff] at hq <;> simp [hden, hb]

/-- Default definition of division -/
instance Rat.instDivInvMonoid : DivInvMonoid Rat where

theorem Rat.div_eq (q r:Rat) : q/r = q * r⁻¹ := by rfl

@[grind]
lemma Rat.formalDiv_eq_zero_iff (a b : ℤ) : (a // b = 0 ↔ a = 0 ∨ b = 0) := by
  constructor
  intro h
  · rw [show (0:Rat) = 0 // 1 by rfl] at h
    obtain hb | hb := Decidable.em (b = 0) <;> grind
  · intro h
    obtain rfl | rfl := h
    rw [show (0:Rat) = 0 // 1 by rfl]
    obtain rfl | hb := Decidable.em (b = 0)
    simp [formalDiv_eq]
    grind
    rw [div_zero]
    rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instField : Field Rat where
  exists_pair_ne := by
    use 0, 1
    rw [show (0:Rat) = 0 // 1 by rfl, show (1:Rat) = 1 // 1 by rfl]
    grind
  mul_inv_cancel a ha := by
    obtain ⟨ p, q, hb , rfl ⟩ := eq_diff a
    have : p ≠ 0 := by
      have : ¬(p // q = 0) := by grind
      rw [formalDiv_eq_zero_iff] at this
      grind
    rw [show (1:Rat) = 1 // 1 by rfl]
    have : q * p ≠ 0 := by positivity
    grind
  inv_zero := rfl
  ratCast_def := by
    intro q
    set num := q.num
    set den := q.den
    have hden : (den:ℤ) ≠ 0 := by simp [den, q.den_nz]
    rw [← Rat.num_div_den q]
    convert coe_Rat_eq _ hden
    grind [coe_Nat_eq, div_eq]
  qsmul := _
  nnqsmul := _

example : (3//4) / (5//6) = 9 // 10 := by grind

def Rat.coe_int_hom : ℤ →+* Rat where
  toFun n := (n:Rat)
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := by grind
  map_mul' x y := by grind

/-- Definition 4.2.6 (positivity) -/
def Rat.IsPos (q:Rat) : Prop := ∃ a b:ℤ, a > 0 ∧ b > 0 ∧ q = a/b

/-- Definition 4.2.6 (negativity) -/
def Rat.IsNeg (q:Rat) : Prop := ∃ r:Rat, r.IsPos ∧ q = -r

lemma Rat.not_isPos_zero_div (a : ℤ) : ¬ (0 // a).IsPos := by
  intro h
  obtain ⟨ p, q, h1, h2, h3 ⟩ := h
  lift p to ℕ using by positivity
  lift q to ℕ using by positivity
  norm_cast at h3
  rw [natCast_eq, natCast_eq, div_eq, inv_eq _ (by positivity), mul_eq _ _ (by positivity) (by positivity)] at h3
  grind

lemma Rat.not_isPos_div_zero (a : ℤ) : ¬ (a // 0).IsPos := by grind [not_isPos_zero_div]

lemma Rat.test1
  (a b : ℤ)
  (h : (a // b).IsPos) (ha : 0 < a) (hb : b < 0) : False := by
  obtain ⟨ p, q, h1, h2, h3 ⟩ := h
  lift p to ℕ  using by positivity
  lift q to ℕ  using by positivity
  norm_cast at h3
  rw [natCast_eq, natCast_eq, div_eq, inv_eq _ (by positivity), mul_eq _ _ (by positivity) (by positivity)] at h3
  ring_nf at h3
  rw [eq _ _ (by omega) (by positivity)] at h3
  have h4 : 0 < a * q := by positivity
  have h5 : 0 * 0 < p * (-b) := by
    gcongr
    linarith
  linarith

lemma Rat.test2
  (a b : ℤ)
  (h : (a // b).IsPos) (ha : a < 0) (hb : 0 < b) : False := by
  obtain ⟨ p, q, h1, h2, h3 ⟩ := h
  lift p to ℕ using by positivity
  lift q to ℕ using by positivity
  norm_cast at h3
  rw [natCast_eq, natCast_eq, div_eq, inv_eq _ (by positivity), mul_eq _ _ (by positivity) (by positivity)] at h3
  ring_nf at h3
  rw [eq _ _ (by omega) (by positivity)] at h3
  have h4 : 0 < b * p := by positivity
  have h5 : 0 * 0 < q * (-a) := by
    gcongr
    linarith
  linarith


lemma Rat.isPos_div (a b : ℤ) : (a // b).IsPos ↔ (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by
  constructor
  · intro h
    obtain ha | rfl | ha : 0 < a ∨ 0 = a ∨ a < 0 := by grind
    obtain hb | rfl | hb : 0 < b ∨ 0 = b ∨ b < 0 := by grind
    · grind
    · exfalso
      exact not_isPos_div_zero a h
    · exfalso
      exact test1 a b h ha hb
    · exfalso
      exact not_isPos_zero_div b h
    obtain hb | rfl | hb : 0 < b ∨ 0 = b ∨ b < 0 := by grind
    · exfalso
      exact test2 a b h ha hb
    · exfalso
      exact not_isPos_div_zero a h
    · grind

  · intro h
    obtain h | h := h
    use a, b
    grind
    use (-a), (-b)
    constructor
    grind
    constructor
    grind
    rw [coe_Int_eq, coe_Int_eq, div_eq, inv_eq, mul_eq, eq]
    all_goals grind

lemma Rat.isNeg_div (a b : ℤ) : (a // b).IsNeg ↔ (a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0) := by
  sorry

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.trichotomous (x:Rat) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  rw [formalDiv_eq_zero_iff]
  grind [isPos_div, isNeg_div]


/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_pos (x:Rat) : ¬(x = 0 ∧ x.IsPos) := by sorry

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_neg (x:Rat) : ¬(x = 0 ∧ x.IsNeg) := by sorry

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_pos_and_neg (x:Rat) : ¬(x.IsPos ∧ x.IsNeg) := by sorry

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLT : LT Rat where
  lt x y := (x-y).IsNeg

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLE : LE Rat where
  le x y := (x < y) ∨ (x = y)

theorem Rat.lt_iff (x y:Rat) : x < y ↔ (x-y).IsNeg := by rfl
theorem Rat.le_iff (x y:Rat) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Rat.gt_iff (x y:Rat) : x > y ↔ (x-y).IsPos := by sorry
theorem Rat.ge_iff (x y:Rat) : x ≥ y ↔ (x > y) ∨ (x = y) := by sorry

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.trichotomous' (x y:Rat) : x > y ∨ x < y ∨ x = y := by sorry

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_lt (x y:Rat) : ¬ (x > y ∧ x < y):= by sorry

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_eq (x y:Rat) : ¬ (x > y ∧ x = y):= by sorry

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_lt_and_eq (x y:Rat) : ¬ (x < y ∧ x = y):= by sorry

/-- Proposition 4.2.9(b) (order is anti-symmetric) / Exercise 4.2.5 -/
theorem Rat.antisymm (x y:Rat) : x < y ↔ (y - x).IsPos := by sorry

/-- Proposition 4.2.9(c) (order is transitive) / Exercise 4.2.5 -/
theorem Rat.lt_trans {x y z:Rat} (hxy: x < y) (hyz: y < z) : x < z := by sorry

/-- Proposition 4.2.9(d) (addition preserves order) / Exercise 4.2.5 -/
theorem Rat.add_lt_add_right {x y:Rat} (z:Rat) (hxy: x < y) : x + z < y + z := by sorry

/-- Proposition 4.2.9(e) (positive multiplication preserves order) / Exercise 4.2.5 -/
theorem Rat.mul_lt_mul_right {x y z:Rat} (hxy: x < y) (hz: z.IsPos) : x * z < y * z := by sorry

/-- (Not from textbook) Establish the decidability of this order. -/
instance Rat.decidableRel : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- at this point, the goal is morally `Decidable(a//b ≤ c//d)`, but there are technical
    -- issues due to the junk value of formal division when the denominator vanishes.
    -- It may be more convenient to avoid formal division and work directly with `Quotient.mk`.
    cases (0:ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            apply isTrue
            sorry
          | isFalse h =>
            apply isFalse
            sorry
      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            sorry
          | isFalse h =>
            apply isFalse
            sorry
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) Rat has the structure of a linear ordering. -/
instance Rat.instLinearOrder : LinearOrder Rat where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_ge := sorry
  le_antisymm := sorry
  le_total := sorry
  toDecidableLE := decidableRel

/-- (Not from textbook) Rat has the structure of a strict ordered ring. -/
instance Rat.instIsStrictOrderedRing : IsStrictOrderedRing Rat where
  add_le_add_left := by sorry
  add_le_add_right := by sorry
  mul_lt_mul_of_pos_left := by sorry
  mul_lt_mul_of_pos_right := by sorry
  le_of_add_le_add_left := by sorry
  zero_le_one := by sorry

/-- Exercise 4.2.6 -/
theorem Rat.mul_lt_mul_right_of_neg (x y z:Rat) (hxy: x < y) (hz: z.IsNeg) : x * z > y * z := by
  sorry


/--
  Not in textbook: create an equivalence between Rat and ℚ. This requires some familiarity with
  the API for Mathlib's version of the rationals.
-/
abbrev Rat.equivRat : Rat ≃ ℚ where
  toFun := Quotient.lift (fun ⟨ a, b, h ⟩ ↦ a / b) (by
    sorry)
  invFun := fun n: ℚ ↦ (n:Rat)
  left_inv n := sorry
  right_inv n := sorry

/-- Not in textbook: equivalence preserves order -/
abbrev Rat.equivRat_order : Rat ≃o ℚ where
  toEquiv := equivRat
  map_rel_iff' := by sorry

/-- Not in textbook: equivalence preserves ring operations -/
abbrev Rat.equivRat_ring : Rat ≃+* ℚ where
  toEquiv := equivRat
  map_add' := by sorry
  map_mul' := by sorry

/--
  (Not from textbook) The textbook rationals are isomorphic (as a field) to the Mathlib rationals.
-/
def Rat.equivRat_ring_symm : ℚ ≃+* Rat := Rat.equivRat_ring.symm

end Section_4_2
