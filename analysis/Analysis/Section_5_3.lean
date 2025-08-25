import Mathlib.Tactic
import Analysis.Section_5_2
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Int.Log


/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- A class of Cauchy sequences that start at zero -/
@[ext]
class CauchySequence extends Sequence where
  zero : n₀ = 0
  cauchy : toSequence.IsCauchy

@[simp]
theorem CauchySequence.ext' {a b: CauchySequence} (h: a.seq = b.seq) : a = b := by
  apply CauchySequence.ext _ h
  rw [a.zero, b.zero]

/-- A sequence starting at zero that is Cauchy, can be viewed as a Cauchy sequence.-/
abbrev CauchySequence.mk' {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : CauchySequence where
  n₀ := 0
  seq := (a:Sequence).seq
  vanish := by aesop
  zero := rfl
  cauchy := ha

@[simp]
theorem CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    (mk' ha).toSequence = (a:Sequence) := rfl

instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe := fun a n ↦ a.toSequence (n:ℤ)

@[simp]
theorem CauchySequence.coe_to_sequence (a: CauchySequence) :
    ((a:ℕ → ℚ):Sequence) = a.toSequence := by
  apply Sequence.ext (by simp [Sequence.n0_coe, a.zero])
  ext n; by_cases h:n ≥ 0 <;> simp_all
  rw [a.vanish]; rwa [a.zero]

@[simp]
theorem CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
theorem Sequence.equiv_trans {a b c:ℕ → ℚ} (hab: Sequence.Equiv a b) (hbc: Sequence.Equiv b c) :
  Sequence.Equiv a c := by
  unfold Sequence.Equiv at *
  intro ε hε
  specialize hab (ε/2) (by positivity)
  specialize hbc (ε/2) (by positivity)
  rw [Rat.eventually_close_of_coe_coe] at hab hbc ⊢
  obtain ⟨ n₀, hab ⟩ := hab
  obtain ⟨ m₀, hbc ⟩ := hbc
  use max n₀ m₀
  intro n hn
  specialize hab n (le_of_max_le_left hn)
  specialize hbc n (le_of_max_le_right hn)
  rw [abs_le] at *
  constructor <;> linarith

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.Equiv a b
  iseqv := {
     refl := by
      intro a
      unfold Sequence.Equiv
      intro ε hε
      rw [Rat.eventually_close_of_coe_coe]
      simp
      use 0
      intro n h'
      positivity
     symm := by
      intro x y hxy ε hε
      specialize hxy ε (by positivity)
      rw [Rat.eventually_close_of_coe_coe] at *
      obtain ⟨ n₀, hxy ⟩ := hxy
      use n₀
      intro n hn
      rw [abs_sub_comm]
      exact hxy n hn
     trans := by
       intro _ _ _ hxy hyz
       exact Sequence.equiv_trans hxy hyz
  }

theorem CauchySequence.equiv_iff (a b: CauchySequence) : a ≈ b ↔ Sequence.Equiv a b := by rfl

/-- Every constant sequence is Cauchy -/
theorem Sequence.IsCauchy.const (a:ℚ) : ((fun _:ℕ ↦ a):Sequence).IsCauchy := by
  rw [IsCauchy.coe]
  intro ε hε
  simp [le_of_lt hε, Section_4_3.dist]

instance CauchySequence.instZero : Zero CauchySequence where
  zero := CauchySequence.mk' (a := fun _: ℕ ↦ 0) (Sequence.IsCauchy.const _)

abbrev Real := Quotient CauchySequence.instSetoid

open Classical in
/--
  It is convenient in Lean to assign the "dummy" value of 0 to `LIM a` when `a` is not Cauchy.
  This requires Classical logic, because the property of being Cauchy is not computable or
  decidable.
-/
noncomputable abbrev LIM (a:ℕ → ℚ) : Real :=
  Quotient.mk _ (if h : (a:Sequence).IsCauchy then CauchySequence.mk' h else (0:CauchySequence))

theorem LIM_def {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    LIM a = Quotient.mk _ (CauchySequence.mk' ha) := by
  rw [LIM, dif_pos ha]

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (a:Sequence).IsCauchy ∧ x = LIM a := by
  -- I had a lot of trouble with this proof; perhaps there is a more idiomatic way to proceed
  apply Quot.ind _ x; intro a; use (a:ℕ → ℚ)
  observe : ((a:ℕ → ℚ):Sequence) = a.toSequence
  rw [this, LIM_def (by convert a.cauchy)]
  refine ⟨ a.cauchy, ?_ ⟩
  congr; ext n; simp; replace := congr($this n); simp_all

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.LIM_eq_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a = LIM b ↔ Sequence.Equiv a b := by
  constructor
  . intro h; replace h := Quotient.exact h
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff] at h
  intro h; apply Quotient.sound
  rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]

theorem Real.LIM_ne_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a ≠ LIM b ↔ ¬ (Sequence.Equiv a b) := not_congr (Real.LIM_eq_LIM ha hb)

/--Lemma 5.3.6 (Sum of Cauchy sequences is Cauchy)-/
theorem Sequence.IsCauchy.add {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a + b:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  rw [coe] at *
  intro ε hε
  choose N1 ha using ha _ (half_pos hε)
  choose N2 hb using hb _ (half_pos hε)
  use max N1 N2
  intro j hj k hk
  have h1 := ha j ?_ k ?_ <;> try omega
  have h2 := hb j ?_ k ?_ <;> try omega
  simp [Section_4_3.dist] at *
  rw [←Rat.Close] at *
  convert Section_4_3.add_close h1 h2
  linarith

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Equiv a a') :
    Equiv (a + b) (a' + b) := by
  -- This proof is written to follow the structure of the original text.
  rw [equiv_def] at *
  peel 2 haa' with ε hε haa'
  rw [Rat.eventuallyClose_def] at *
  choose N haa' using haa'; use N
  simp [Rat.closeSeq_def] at *
  peel 5 haa' with n hn hN _ _ haa'
  simp [hn, hN] at haa' ⊢
  convert Section_4_3.add_close haa' (Section_4_3.close_refl (b n.toNat))
  simp

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Equiv b b') :
    Equiv (a + b) (a + b') := by simp_rw [add_comm]; exact add_equiv_left _ hbb'

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv {a b a' b':ℕ → ℚ} (haa': Equiv a a')
  (hbb': Equiv b b') :
    Equiv (a + b) (a' + b') :=
  equiv_trans (add_equiv_left _ haa') (add_equiv_right _ hbb')

/-- Definition 5.3.4 (Addition of reals) -/
noncomputable instance Real.add_inst : Add Real where
  add := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a + b)) (by
      intro a b a' b' haa' hbb'
      change LIM ((a:ℕ → ℚ) + (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) + (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . solve_by_elim [Sequence.add_equiv]
      all_goals apply Sequence.IsCauchy.add <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

/-- Definition 5.3.4 (Addition of reals) -/
theorem Real.LIM_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a + LIM b = LIM (a + b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.add ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos]

/-- Proposition 5.3.10 (Product of Cauchy sequences is Cauchy) -/
theorem Sequence.IsCauchy.mul {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a * b:Sequence).IsCauchy := by
  have : ∃ K:ℚ, K > 0 ∧ ∀ n:ℕ, |a n| ≤ K ∧ |b n| ≤ K := by
    have ha' := isBounded_of_isCauchy ha
    have hb' := isBounded_of_isCauchy hb
    rw [isBounded_iff_of_minimum 0] at ha' hb'
    obtain ⟨ M1, h1, h2 ⟩ := ha'
    obtain ⟨ M2, h3, h4 ⟩ := hb'
    rw [BoundedBy.coe] at h2 h4
    use max M1 M2
    constructor
    positivity
    intro n
    have : M1 ≤ max M1 M2 := le_max_left M1 M2
    specialize h2 n
    constructor
    linarith [le_max_left M1 M2]
    specialize h4 n
    linarith [le_max_right M1 M2]
  obtain ⟨ K, h5, h6 ⟩ := this
  intro ε hε
  rw [Rat.EventuallySteady.coe]

  rw [IsCauchy.coe] at ha hb
  obtain ⟨ N1, ha ⟩ := ha (ε/(2*K)) (by positivity)
  obtain ⟨ N2, hb ⟩ := hb (ε/(2*K)) (by positivity)
  use max N1 N2
  rw [Rat.Steady.coe_from_coe] at *
  intro n hn m hm
  simp only [sup_le_iff] at hn hm
  specialize ha n hn.1 m hm.1
  specialize hb n hn.2 m hm.2
  unfold Rat.Close at *
  dsimp
  unfold Section_4_3.dist at *
  calc
    _ = |a n * b n - a n * b m + a n * b m - a m * b m| := by congr; ring
    _ ≤ |a n * b n - a n * b m| + |a n * b m - a m * b m| := by
      have := abs_add (a n * b n - a n * b m) (a n * b m - a m * b m)
      ring_nf at *
      exact this
    _ = |a n * (b n - b m)| + |b m * (a n - a m)| := by
      congr <;> ring
    _ = |a n| * |b n - b m| + |b m| * |a n - a m| := by
      congr <;> rw [abs_mul]
    _ ≤ K * |b n - b m| + K * |a n - a m| := by
      gcongr
      exact (h6 n).1
      exact (h6 m).2
    _ ≤ K * (ε / (2 * K)) + K * (ε / (2 * K)) := by
      gcongr
    _ = (K * ε / K) := by
      ring
    _ = ε := by
      field_simp [h5]

/-- Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (hb : (b:Sequence).IsCauchy) (haa': Equiv a a') :
  Equiv (a * b) (a' * b) := by
  have hb := isBounded_of_isCauchy hb
  rw [isBounded_iff_of_minimum 0] at hb
  simp_rw [BoundedBy.coe] at hb
  obtain ⟨ K, hK, hB ⟩ := hb
  unfold Equiv at *
  intro ε hε
  simp_rw [Rat.eventually_close_of_coe_coe] at *
  specialize haa' (ε/K) (by positivity)
  obtain ⟨ N, haa' ⟩ := haa'
  use N
  intro n hn
  specialize haa' n hn
  dsimp
  calc
    _ = |(a n - a' n) * b n| := by congr; ring
    _ = |a n - a' n| * |b n| := by rw [abs_mul]
    _ ≤ (ε / K) * K := by
      gcongr
      exact hB n
    _ = ε := by field_simp [hK]

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ)  (ha : (a:Sequence).IsCauchy)  (hbb': Equiv b b') :
  Equiv (a * b) (a * b') := by simp_rw [mul_comm]; exact mul_equiv_left a ha hbb'

theorem Sequence.mul_equiv
{a b a' b':ℕ → ℚ}
(ha : (a:Sequence).IsCauchy)
(hb' : (b':Sequence).IsCauchy)
(haa': Equiv a a')
(hbb': Equiv b b') : Equiv (a * b) (a' * b') :=
  equiv_trans (mul_equiv_right _ ha hbb') (mul_equiv_left _ hb' haa')

/-- Definition 5.3.9 (Product of reals) -/
noncomputable instance Real.mul_inst : Mul Real where
  mul := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a * b)) (by
      intro a b a' b' haa' hbb'
      change LIM ((a:ℕ → ℚ) * (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) * (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . exact Sequence.mul_equiv (by rw [CauchySequence.coe_to_sequence]; exact a.cauchy) (by rw [CauchySequence.coe_to_sequence]; exact b'.cauchy) haa' hbb'
      all_goals apply Sequence.IsCauchy.mul <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

theorem Real.LIM_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a * LIM b = LIM (a * b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.mul ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos]

instance Real.instRatCast : RatCast Real where
  ratCast := fun q ↦
    Quotient.mk _ (CauchySequence.mk' (a := fun _ ↦ q) (Sequence.IsCauchy.const q))

theorem Real.ratCast_def (q:ℚ) : (q:Real) = LIM (fun _ ↦ q) := by rw [LIM_def]; rfl

/-- Exercise 5.3.3 -/
@[simp]
theorem Real.ratCast_inj (q r:ℚ) : (q:Real) = (r:Real) ↔ q = r := by
  constructor
  intro h
  rw [Real.ratCast_def, Real.ratCast_def] at h
  rw [Real.LIM_eq_LIM (Sequence.IsCauchy.const q) (Sequence.IsCauchy.const r)] at h
  rw [Sequence.equiv_iff] at h
  by_contra h'
  have : 0 < |q - r| := abs_sub_pos.mpr h'
  specialize h (|q - r|/2) (by positivity)
  obtain ⟨ N, h ⟩ := h
  specialize h N (by omega)
  linarith

  intro h
  rw [h]

instance Real.instOfNat {n:ℕ} : OfNat Real n where
  ofNat := ((n:ℚ):Real)

instance Real.instNatCast : NatCast Real where
  natCast n := ((n:ℚ):Real)

theorem Real.ofNat_eq (n:ℕ) : ofNat(n) = ((n:ℚ):Real) := rfl

theorem Real.natCast_eq (n:ℕ) : (n:Real) = ((n:ℚ):Real) := rfl

@[simp]
theorem Real.LIM.zero : LIM (fun _ ↦ (0:ℚ)) = 0 := by rw [←ratCast_def 0]; rfl

instance Real.instIntCast : IntCast Real where
  intCast n := ((n:ℚ):Real)

theorem Real.intCast_def (n:ℤ) : (n:Real) = ((n:ℚ):Real) := by
  norm_cast

/-- ratCast distributes over addition -/
theorem Real.ratCast_add (a b:ℚ) : (a:Real) + (b:Real) = (a+b:ℚ) := by
  rw [ratCast_def, ratCast_def, ratCast_def]
  rw [LIM_add (Sequence.IsCauchy.const a) (Sequence.IsCauchy.const b)]
  rw [LIM_eq_LIM]
  intro ε hε
  rw [Rat.eventually_close_of_coe_coe]
  use 0
  intro n hn
  simp
  positivity
  have : (fun (x:ℕ) ↦ a) + (fun x ↦ b) = fun x ↦ (a + b) := by
    ext i
    dsimp
  rw [this]
  exact Sequence.IsCauchy.const _
  exact Sequence.IsCauchy.const _

/-- ratCast distributes over multiplication -/
theorem Real.ratCast_mul (a b:ℚ) : (a:Real) * (b:Real) = (a*b:ℚ) := by
  rw [ratCast_def, ratCast_def, ratCast_def]
  rw [LIM_mul (Sequence.IsCauchy.const a) (Sequence.IsCauchy.const b)]
  rw [LIM_eq_LIM]
  intro ε hε
  rw [Rat.eventually_close_of_coe_coe]
  use 0
  intro n hn
  simp
  positivity
  have : (fun (x:ℕ) ↦ a) * (fun x ↦ b) = fun x ↦ (a * b) := by
    ext i
    dsimp
  rw [this]
  exact Sequence.IsCauchy.const _
  exact Sequence.IsCauchy.const _

noncomputable instance Real.instNeg : Neg Real where
  neg := fun x ↦ ((-1:ℚ):Real) * x

theorem neg_eq_mul (r:Real) : -r = (-1:ℚ) * r := by rfl

theorem Sequence.IsCauchy.neg (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) :
    ((-a:ℕ → ℚ):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe] at *
  intro ε hε
  obtain ⟨ N, ha ⟩ := ha ε hε
  use N
  intro j hj k hk
  unfold Section_4_3.dist at *
  simp
  specialize ha j hj k hk
  rw [abs_sub_comm] at ha
  ring_nf at *
  exact ha

/-- It may be possible to omit the Cauchy sequence hypothesis here. -/
theorem Real.neg_LIM (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) : -LIM a = LIM (-a) := by
  rw [neg_eq_mul, ratCast_def, LIM_mul (Sequence.IsCauchy.const _) ha]
  congr
  ext i
  simp

/-- ratCast commutes with negation -/
theorem Real.neg_ratCast (a:ℚ) : -(a:Real) = (-a:ℚ) := by
  rw [ratCast_def, ratCast_def]
  rw [neg_LIM]
  rw [LIM_eq_LIM]
  intro ε hε
  rw [Rat.eventually_close_of_coe_coe]
  simp [show 0 ≤ ε by positivity]
  exact Sequence.IsCauchy.const _
  exact Sequence.IsCauchy.const _
  exact Sequence.IsCauchy.const _

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.addGroup_inst : AddGroup Real :=
AddGroup.ofLeftAxioms (by
  intro a b c
  obtain ⟨ x, hx, hx' ⟩ := eq_lim a
  obtain ⟨ y, hy, hy' ⟩ := eq_lim b
  obtain ⟨ z, hz, hz' ⟩ := eq_lim c
  rw [hx', hy', hz']
  -- At this point, we have e₁ = e₂, where e₁ is some expression involving LIM
  -- Our strategy is to repeatedly push LIM "upwards" so that our goal becomes LIM e₁' = LIM e₂'
  -- can repeatedly push the LIM to the outermost, but we need to clear the side conditions
  have hxy := Sequence.IsCauchy.add hx hy
  have hyz := Sequence.IsCauchy.add hy hz
  repeat rw [LIM_add (by assumption) (by assumption)]
  ring_nf
) (by
  intro a
  obtain ⟨ x, hx, hx' ⟩ := eq_lim a
  rw [hx', ← LIM.zero]
  rw [LIM_add]
  congr
  ext i
  dsimp
  ring
  apply Sequence.IsCauchy.const
  exact hx
) (by
  intro a
  obtain ⟨ x, hx, hx' ⟩ := eq_lim a
  rw [hx', neg_LIM, LIM_add, ← LIM.zero]
  congr
  ext i
  dsimp
  ring
  rw [Sequence.IsCauchy.coe] at *
  intro ε hε
  specialize hx ε hε
  obtain ⟨ N, hx ⟩ := hx
  use N
  intro j hj k hk
  specialize hx j hj k hk
  unfold Section_4_3.dist at *
  simp
  rw [abs_sub_comm] at hx
  rw [show -x j + x k = x k - x j by ring]
  repeat exact hx
)

theorem Real.sub_eq_add_neg (x y:Real) : x - y = x + (-y) := rfl

theorem Sequence.IsCauchy.sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    ((a-b:ℕ → ℚ):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe] at *
  intro ε hε
  obtain ⟨ N1, ha ⟩ := ha (ε/2) (by positivity)
  obtain ⟨ N2, hb ⟩ := hb (ε/2) (by positivity)
  use max N1 N2
  intro j hj k hk
  specialize ha j (by omega) k (by omega)
  specialize hb j (by omega) k (by omega)
  unfold Section_4_3.dist at *
  rw [abs_le] at *
  dsimp
  constructor <;> linarith

theorem Real.LIM_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a - LIM b = LIM (a - b) := by
  rw [sub_eq_add_neg, neg_LIM b hb, LIM_add ha (Sequence.IsCauchy.neg b hb)]
  congr
  ring

/-- ratCast distributes over subtraction -/
theorem Real.ratCast_sub (a b:ℚ) : (a:Real) - (b:Real) = (a-b:ℚ) := by
  rw [ratCast_def, ratCast_def, ratCast_def]
  rw [Real.LIM_sub (Sequence.IsCauchy.const a) (Sequence.IsCauchy.const b)]
  rw [LIM_eq_LIM]
  intro ε hε
  rw [Rat.eventually_close_of_coe_coe]
  use 0
  intro n hn
  simp
  positivity
  have : (fun (x:ℕ) ↦ a) - (fun x ↦ b) = fun x ↦ (a - b) := by
    ext i
    dsimp
  rw [this]
  exact Sequence.IsCauchy.const _
  exact Sequence.IsCauchy.const _


/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instAddCommGroup : AddCommGroup Real where
  add_comm := by
    intro a b
    obtain ⟨ x, hx, hx' ⟩ := eq_lim a
    obtain ⟨ y, hy, hy' ⟩ := eq_lim b
    rw [hx', hy']
    rw [LIM_add (by assumption) (by assumption)]
    rw [LIM_add (by assumption) (by assumption)]
    ring_nf

theorem Real.mul_comm (a b:Real) : a * b = b * a := by
  obtain ⟨ x, hx, hx' ⟩ := eq_lim a
  obtain ⟨ y, hy, hy' ⟩ := eq_lim b
  rw [hx', hy']
  rw [LIM_mul (by assumption) (by assumption)]
  rw [LIM_mul (by assumption) (by assumption)]
  ring_nf

theorem Real.one_mul (a:Real) : (1:Real) * a = a := by
  obtain ⟨ x, hx, hx' ⟩ := eq_lim a
  rw [show (1:Real) = (1:ℚ) by norm_cast]
  rw [ratCast_def]
  rw [hx']
  rw [LIM_mul (Sequence.IsCauchy.const 1) hx]
  congr
  ext i
  simp

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommMonoid : CommMonoid Real where
  mul_comm := by
    intro a b
    exact mul_comm a b
  mul_assoc := by
    intro a b c
    obtain ⟨ x, hx, hx' ⟩ := eq_lim a
    obtain ⟨ y, hy, hy' ⟩ := eq_lim b
    obtain ⟨ z, hz, hz' ⟩ := eq_lim c
    have hxy := Sequence.IsCauchy.mul hx hy
    have hyz := Sequence.IsCauchy.mul hy hz
    rw [hx', hy', hz']
    rw [LIM_mul (by assumption) (by assumption)]
    rw [LIM_mul (by assumption) (by assumption)]
    rw [LIM_mul (by assumption) (by assumption)]
    rw [LIM_mul (by assumption) (by assumption)]
    ring_nf
  one_mul := by
    intro a
    exact one_mul a
  mul_one := by
    intro a
    rw [mul_comm]
    exact one_mul a

theorem Real.left_distrib (a b c:Real) : a * (b + c) = a * b + a * c := by
  obtain ⟨ x, hx, hx' ⟩ := eq_lim a
  obtain ⟨ y, hy, hy' ⟩ := eq_lim b
  obtain ⟨ z, hz, hz' ⟩ := eq_lim c
  have hxpy := Sequence.IsCauchy.add hx hy
  have hypz := Sequence.IsCauchy.add hy hz
  have hxty := Sequence.IsCauchy.mul hx hy
  have hxtz := Sequence.IsCauchy.mul hx hz
  have hytz := Sequence.IsCauchy.mul hy hz
  have hxyz := Sequence.IsCauchy.mul hx hypz
  rw [hx', hy', hz']
  rw [LIM_add (by assumption) (by assumption)]
  rw [LIM_mul (by assumption) (by assumption)]
  rw [LIM_mul (by assumption) (by assumption)]
  rw [LIM_mul (by assumption) (by assumption)]
  rw [LIM_add (by assumption) (by assumption)]
  ring_nf

theorem Real.LIM_eq_0 : (LIM fun _ ↦ 0) = 0 := by
  rw [show (0:Real) = (0:ℚ) by norm_cast, ratCast_def]

theorem Real.zero_mul (a:Real) : (0:Real) * a = 0 := by
  obtain ⟨ x, hx, hx' ⟩ := eq_lim a
  rw [hx']
  rw [← LIM_eq_0]
  rw [LIM_mul (Sequence.IsCauchy.const 0) hx]
  congr
  ext i
  simp


/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommRing : CommRing Real where
  left_distrib := by
    intro a b c
    exact left_distrib a b c
  right_distrib := by
    intro a b c
    rw [mul_comm, left_distrib]
    congr 1
    exact mul_comm c a
    exact mul_comm c b
  zero_mul := by
    intro a
    exact zero_mul a
  mul_zero := by
    intro a
    rw [mul_comm]
    exact zero_mul a
  mul_assoc := by
    intro a b c
    exact mul_assoc a b c
  natCast_succ := by
    intro n
    rw [Real.ofNat_eq]
    have : @NatCast.natCast Real instNatCast n = ((n:ℚ):Real) := by rfl
    rw [this]
    rw [Real.ratCast_add]
    norm_cast
  intCast_negSucc := by
    intro n
    have test' (z:ℤ) : IntCast.intCast z = (z:Real) := by norm_cast
    rw [test', Real.natCast_eq, Real.neg_ratCast]
    congr

abbrev Real.ratCast_hom : ℚ →+* Real where
  toFun := RatCast.ratCast
  map_zero' := by
    norm_cast
  map_one' := by
    norm_cast
  map_add' := by
    intro a b
    rw [ratCast_add]
  map_mul' := by
    intro a b
    rw [ratCast_mul]

/--
  Definition 5.3.12 (sequences bounded away from zero). Sequences are indexed to start from zero
  as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayZero (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c

theorem bounded_away_zero_def (a:ℕ → ℚ) : BoundedAwayZero a ↔
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c := by rfl

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := by use 1; simp

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 10^(-(n:ℤ)-1)) := by
  by_contra h
  obtain ⟨ c, h1, h2 ⟩ := h
  dsimp at h2
  obtain ⟨ c1, hc1 ⟩ := exists_nat_gt (-(Int.log 10 c))
  specialize h2 c1
  rw [abs_of_nonneg (by positivity)] at h2
  have : -(c1:ℤ) - 1 ≥ Int.log 10 c := by
    have : c ≥ (10:ℚ)^(Int.log 10 c) := by exact Int.zpow_log_le_self (by norm_num) h1
    have : (10:ℚ)^(-(c1:ℤ)-1) ≥ (10:ℚ)^(Int.log 10 c) := by linarith
    simp at this
    exact this
  linarith

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 1 - 10^(-(n:ℤ))) := by
  by_contra h
  obtain ⟨ c, h1, h2 ⟩ := h
  specialize h2 0
  simp at h2
  linarith

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ 10^(n+1)) := by
  use 1, by norm_num
  intro n; dsimp
  rw [abs_of_nonneg (by positivity), show (1:ℚ) = 10^0 by norm_num]
  gcongr <;> grind

/-- Examples 5.3.13 -/
example : ¬ ((fun (n:ℕ) ↦ (10:ℚ)^(n)):Sequence).IsBounded := by
  by_contra h
  rw [isBounded_iff_of_minimum 0] at h
  obtain ⟨ M, hM, hB ⟩ := h
  have : M > 0 := hM
  rw [Sequence.BoundedBy.coe] at hB
  obtain ⟨ M', h1 ⟩ := exists_nat_gt (Int.clog 10 M)
  specialize hB M'
  rw [abs_of_nonneg (by positivity)] at hB
  have hB : (10:ℚ)^(M':ℤ) ≤ M := by
    norm_cast
    norm_cast at hB

  have h2 : M ≤ (10:ℕ)^(Int.clog 10 M) := by
    apply Int.self_le_zpow_clog
    norm_num

  have h3 : (10:ℕ)^(Int.clog 10 M) < (10:ℚ)^(M':ℤ) := by
    rw [← show (10:ℚ) = (10:ℕ) by norm_cast]
    gcongr
    norm_num

  linarith

/-- Lemma 5.3.14 -/
theorem Real.boundedAwayZero_of_nonzero {x:Real} (hx: x ≠ 0) :
    ∃ a:ℕ → ℚ, (a:Sequence).IsCauchy ∧ BoundedAwayZero a ∧ x = LIM a := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ b, hb, rfl ⟩ := eq_lim x
  simp only [←LIM.zero, ne_eq] at hx
  rw [LIM_eq_LIM hb (by convert Sequence.IsCauchy.const 0), Sequence.equiv_iff] at hx
  simp at hx
  choose ε hε hx using hx
  choose N hb' using (Sequence.IsCauchy.coe _).mp hb _ (half_pos hε)
  choose n₀ hn₀ hx using hx N
  have how : ∀ j ≥ N, |b j| ≥ ε/2 := by sorry
  set a : ℕ → ℚ := fun n ↦ if n < n₀ then (ε/2) else b n
  have not_hard : Sequence.Equiv a b := by sorry
  have ha : (a:Sequence).IsCauchy := (Sequence.IsCauchy.equiv not_hard).mpr hb
  refine ⟨ a, ha, ?_, by rw [(LIM_eq_LIM ha hb).mpr not_hard] ⟩
  rw [bounded_away_zero_def]
  use ε/2, half_pos hε
  intro n; by_cases hn: n < n₀ <;> simp [a, hn, le_abs_self _]
  grind

/--
  This result was not explicitly stated in the text, but is needed in the theory. It's a good
  exercise, so I'm setting it as such.
-/
theorem Real.lim_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    LIM a ≠ 0 := by
  by_contra h
  obtain ⟨ c, h1, h2 ⟩ := ha
  rw [← LIM_eq_0] at h
  rw [LIM_eq_LIM ha_cauchy (by apply Sequence.IsCauchy.const)] at h
  specialize h (c/2) (by positivity)
  rw [Rat.eventually_close_of_coe_coe] at h
  obtain ⟨ N, h3 ⟩ := h
  specialize h3 N (by omega)
  specialize h2 N
  ring_nf at h3
  linarith


theorem Real.nonzero_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a) (n: ℕ) : a n ≠ 0 := by
   choose c hc ha using ha; specialize ha n; contrapose! ha; simp [ha, hc]

/-- Lemma 5.3.15 -/
theorem Real.inv_isCauchy_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    ((a⁻¹:ℕ → ℚ):Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  have ha' (n:ℕ) : a n ≠ 0 := nonzero_of_boundedAwayZero ha n
  rw [bounded_away_zero_def] at ha; choose c hc ha using ha
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at ha_cauchy ⊢
  intro ε hε; specialize ha_cauchy (c^2 * ε) (by positivity)
  choose N ha_cauchy using ha_cauchy; use N;
  peel 4 ha_cauchy with n hn m hm ha_cauchy
  calc
    _ = |(a m - a n) / (a m * a n)| := by congr; field_simp [ha' m, ha' n]; grind
    _ ≤ |a m - a n| / c^2 := by rw [abs_div, abs_mul, sq]; gcongr <;> solve_by_elim
    _ = |a n - a m| / c^2 := by rw [abs_sub_comm]
    _ ≤ (c^2 * ε) / c^2 := by gcongr
    _ = ε := by field_simp [hc]

/-- Lemma 5.3.17 (Reciprocation is well-defined) -/
theorem Real.inv_of_equiv {a b:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) (hb: BoundedAwayZero b)
  (hb_cauchy: (b:Sequence).IsCauchy) (hlim: LIM a = LIM b) :
    LIM a⁻¹ = LIM b⁻¹ := by
  -- This proof is written to follow the structure of the original text.
  set P := LIM a⁻¹ * LIM a * LIM b⁻¹
  have ha' := nonzero_of_boundedAwayZero ha
  have hb' := nonzero_of_boundedAwayZero hb
  have hainv_cauchy := Real.inv_isCauchy_of_boundedAwayZero ha ha_cauchy
  have hbinv_cauchy := Real.inv_isCauchy_of_boundedAwayZero hb hb_cauchy
  have haainv_cauchy := hainv_cauchy.mul ha_cauchy
  have habinv_cauchy := hainv_cauchy.mul hb_cauchy
  have claim1 : P = LIM b⁻¹ := by
    simp only [P, LIM_mul hainv_cauchy ha_cauchy, LIM_mul haainv_cauchy hbinv_cauchy]
    rcongr n; simp [ha' n]
  have claim2 : P = LIM a⁻¹ := by
    simp only [P, hlim, LIM_mul hainv_cauchy hb_cauchy, LIM_mul habinv_cauchy hbinv_cauchy]
    rcongr n; simp [hb' n]
  grind

open Classical in
/--
  Definition 5.3.16 (Reciprocation of real numbers).  Requires classical logic because we need to
  assign a "junk" value to the inverse of 0.
-/
noncomputable instance Real.instInv : Inv Real where
  inv x := if h: x ≠ 0 then LIM (boundedAwayZero_of_nonzero h).choose⁻¹ else 0

theorem Real.inv_def {a:ℕ → ℚ} (h: BoundedAwayZero a) (hc: (a:Sequence).IsCauchy) :
    (LIM a)⁻¹ = LIM a⁻¹ := by
  observe hx : LIM a ≠ 0
  set x := LIM a
  have ⟨ h1, h2, h3 ⟩ := (boundedAwayZero_of_nonzero hx).choose_spec
  simp [instInv, hx, -Quotient.eq]
  exact inv_of_equiv h2 h1 h hc h3.symm

@[simp]
theorem Real.inv_zero : (0:Real)⁻¹ = 0 := by simp [Inv.inv]

theorem Real.self_mul_inv {x:Real} (hx: x ≠ 0) : x * x⁻¹ = 1 := by
  obtain ⟨s, h1, h2, h3⟩ := Real.boundedAwayZero_of_nonzero hx
  have isCauchy_s_inv := inv_isCauchy_of_boundedAwayZero h2 h1
  rw [h3, inv_def h2 h1, LIM_mul h1 isCauchy_s_inv]
  obtain ⟨ c, hc, ha ⟩ := h2
  rw [show (1:Real) = LIM (fun n ↦ 1) by rw [LIM_def (Sequence.IsCauchy.const 1)]; rfl, Real.LIM_eq_LIM]
  intro ε hε
  rw [Rat.eventually_close_of_coe_coe]
  use 0
  intro n hn
  specialize ha n
  dsimp
  have : s n ≠ 0 := by
    by_contra h
    rw [h] at ha
    norm_num at ha
    linarith
  simp [this]
  linarith
  exact Sequence.IsCauchy.mul h1 isCauchy_s_inv
  exact Sequence.IsCauchy.const 1

theorem Real.inv_mul_self {x:Real} (hx: x ≠ 0) : x⁻¹ * x = 1 := by
  rw [mul_comm]
  exact self_mul_inv hx

lemma BoundedAwayZero.const {q : ℚ} (hq : q ≠ 0) : BoundedAwayZero fun _ ↦ q := by
  use |q|; simp [hq]

theorem Real.inv_ratCast (q:ℚ) : (q:Real)⁻¹ = (q⁻¹:ℚ) := by
  by_cases h : q = 0
  . rw [h, ← show (0:Real) = (0:ℚ) by norm_cast]; norm_num; norm_cast
  simp_rw [ratCast_def, inv_def (BoundedAwayZero.const h) (by apply Sequence.IsCauchy.const)]; congr

/-- Default definition of division -/
noncomputable instance Real.instDivInvMonoid : DivInvMonoid Real where

theorem Real.div_eq (x y:Real) : x/y = x * y⁻¹ := rfl

noncomputable instance Real.instField : Field Real where
  exists_pair_ne := by
    use 0, 1
    by_contra h
    rw [show (0:Real) = (0:ℚ) by norm_cast] at h
    rw [show (1:Real) = (1:ℚ) by norm_cast] at h
    rw [ratCast_inj] at h
    norm_num at h
  mul_inv_cancel := by
    intro a ha
    exact self_mul_inv ha
  inv_zero := inv_zero
  ratCast_def := by
    intro q

    rw [ratCast_def]
    rw [natCast_eq, ratCast_def]
    rw [intCast_def, ratCast_def]
    sorry
  qsmul := _
  nnqsmul := _

theorem Real.mul_right_cancel₀' {x y z:Real} (hz: z ≠ 0) (h: x * z = y * z) : x = y := by
  have : (x * z) * z⁻¹ = (y * z) * z⁻¹ := by congr
  rw [show x * z * z⁻¹ = x * (z * z⁻¹) by ring] at this
  rw [show y * z * z⁻¹ = y * (z * z⁻¹) by ring] at this
  rw [self_mul_inv hz] at this
  ring_nf at this
  exact this

theorem Real.mul_right_cancel₀ {x y z:Real} (hz: z ≠ 0) (h: x * z = y * z) : x = y := by
  field_simp [hz] at h
  exact h


theorem Real.mul_right_nocancel : ¬ ∀ (x y z:Real), (hz: z = 0) → (x * z = y * z) → x = y := by
  intro h
  specialize h 1 2 0 (by rfl) (by norm_num)
  rw [show (1:Real) = (1:ℚ) by norm_cast] at h
  rw [show (2:Real) = (2:ℚ) by norm_cast] at h
  rw [ratCast_inj] at h
  norm_num at h

/-- Exercise 5.3.4 -/
theorem Real.equiv_of_bounded {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hab: Sequence.Equiv a b) :
    (b:Sequence).IsBounded := by
      unfold Sequence.Equiv at hab
      rwa [Sequence.bounded_of_close (hab 1 (by norm_num))] at ha

/--
  Same as `Sequence.IsCauchy.harmonic` but reindexing the sequence as a₀ = 1, a₁ = 1/2, ...
  This form is more convenient for the upcoming proof of Theorem 5.5.9.
-/
theorem Sequence.IsCauchy.harmonic' : ((fun n ↦ 1/((n:ℚ)+1): ℕ → ℚ):Sequence).IsCauchy := by
  rw [coe]; intro ε hε; choose N h1 h2 using (mk _).mp harmonic ε hε
  use N.toNat; intro j _ k _; specialize h2 (j+1) _ (k+1) _ <;> try omega
  simp_all

/-- Exercise 5.3.5 -/
theorem Real.LIM.harmonic : LIM (fun n ↦ 1/((n:ℚ)+1)) = 0 := by
  rw [← LIM_eq_0, LIM_eq_LIM (Sequence.IsCauchy.harmonic') (Sequence.IsCauchy.const 0)]
  unfold Sequence.Equiv
  intro ε hε
  rw [Rat.eventually_close_of_coe_coe]
  obtain ⟨ N, hN ⟩ := exists_nat_ge ε⁻¹
  use N
  intro n hn
  ring_nf
  rw [abs_of_nonneg (by positivity)]
  rw [show  ε = (ε⁻¹)⁻¹ by field_simp [hε]]
  gcongr
  rify at *
  linarith


end Chapter5
