import Mathlib



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
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2
      simp at h1 h2 ⊢
      have h3 := congrArg₂ (· + ·) h1 h2
      simp at h3
      omega
    }

@[simp]
theorem PreInt.equiv (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

/--
(a+b) —— (b+c) ≃ (a+d) —— (d+c)
-/
example (a b c d: ℕ) : (⟨ a + b, b + c ⟩ : PreInt) ≈ (⟨ a + d, d + c ⟩ : PreInt) := by
  rw [PreInt.equiv]
  omega

example : 3 + 5 = 5 + 3 := rfl

def five_minus_three : PreInt := ⟨ 5, 3 ⟩
def six_minus_four : PreInt := ⟨ 6, 4 ⟩
def six_minus_three : PreInt := ⟨ 6, 3 ⟩
example : five_minus_three ≈ six_minus_four := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ) : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
@[simp high, grind]
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp at *
    omega
)

/-- Note: the operator precedence is parsed as (a —— b) + (c —— d)  -/
@[simp, grind]
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

theorem Int.add_comm : ∀ a b: Int, a + b = b + a := by
    intro a b
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    simp
    omega

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp high]
theorem Int.natCast_inj (n m:ℕ) :
    (n : Int) = (m : Int) ↔ n = m := by
      simp only [natCast_eq, eq, add_zero]

@[grind]
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  constructor
  intro h
  rw [show (0 : Int) = ((0 : Nat) : Int) by rfl] at h
  rw [natCast_inj] at h
  exact h
  intro h
  rw [h]
  simp


/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    intro a b h
    dsimp
    rw [Int.eq]
    whnf at h
    linarith
  )

@[simp]
theorem Int.neg_eq (a b:ℕ) : -(a——b) = b——a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n


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
  grind
) (by
  intro a
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  rw [show (0 : Int) = 0 —— 0 by rfl]
  simp
) (by
  intro a
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  simp only [neg_eq, add_eq, eq_0']
  omega
)

instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := add_comm

instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

lemma Int.pos_iff_gt_0 {a : Int} : a.IsPos → 0 < a := by
  intro h
  rcases h with ⟨ w, hw ⟩
  constructor
  · use w
    grind
  · by_contra h
    have := cast_eq_0_iff_eq_0 -- grind fails when I remove this
    grind

structure RealIsometry where
  f : ℝ → ℝ
  is_isometry : ∀ x y, |f x - f y| = |x - y|

def RealIsometry.identity : RealIsometry where
  f := id
  is_isometry := by simp

def reflection (c : ℝ) : RealIsometry where
  f := fun x ↦ 2 * c - x
  is_isometry := by
    intro x y
    rw [abs_sub_comm]
    congr 1
    ring

def translation (d : ℝ) : RealIsometry where
  f := fun x ↦ x + d
  is_isometry := by
    intro x y
    congr 1
    ring

def RealIsometry.comp (a : RealIsometry) (b : RealIsometry) : RealIsometry where
  f := a.f ∘ b.f
  is_isometry := by
    intro x y
    rw [Function.comp_apply, Function.comp_apply]
    rw [a.is_isometry, b.is_isometry]

def RealIsometry.inv (a : RealIsometry) : RealIsometry where
  f := fun x ↦ a.f x
  is_isometry := by sorry


instance : Group RealIsometry where
  one := RealIsometry.identity
  mul a b := RealIsometry.comp a b
  inv a := reflection (a.f 0)
  mul_assoc a b c := by sorry
  one_mul a := by sorry
  mul_one a := by sorry
  inv_mul_cancel:= sorry

class AffinePlane (X : Type) where
  IsLine : Set X → Prop
  a1 : ∀ P Q, P ≠ Q → (∃! l : Set X, IsLine l ∧ P ∈ l ∧ Q ∈ l)
  a2 : ∀ P l, IsLine l → P ∉ l → ∃! m, P ∈ m ∧ IsLine m ∧ (m = l ∨ (m ∩ l) = ∅)


/-- A topology on `X`. -/
class TopSpace (X : Type) where
  IsOpen : Set X → Prop
  isOpen_univ : IsOpen (⊤ : Set X)
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  isOpen_sUnion : ∀ s : Set (Set X), (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

class FinTopSpace (n : Nat) where
  IsOpen : Finset (Fin n) → Prop
  isOpen_univ : IsOpen (⊤ : Finset (Fin n))
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  isOpen_sUnion : ∀ s : Finset (Finset (Fin n)), (∀ t ∈ s, IsOpen t) → IsOpen (⋃ s)

instance S1 : TopSpace (Fin 2) where
  IsOpen s := true
  isOpen_univ := by simp
  isOpen_sUnion := by simp
  isOpen_inter := by simp

example
  (I : Fin 2)
: I = 0 ∨ I = 1 := by
  revert I
  decide

example
  (I : Finset (Fin 2))
: I = {} ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  revert I
  decide

example
  (I : Set (Set (Fin 2)))
  (h : ∀ t ∈ I, t = ⊥ ∨ t = ⊤)
: I = {} ∨ I = {⊤} ∨ I = {⊥} ∨ I = {⊥, ⊤} := by
  have : I ∈ Set.powerset { ⊥, ⊤ } := by
    intro s hs
    specialize h s hs
    obtain rfl | rfl := h <;> simp
  have h' : (Set.powerset { ⊥, ⊤ } : Set (Set (Set (Fin 2)))) = {⊥, {⊥}, {⊤}, {⊥, ⊤}} := by
    sorry
  rw [h'] at this
  sorry

example
  (X : Type)
  (I : Set (Set X))
  (h : ∀ t ∈ I, t = ⊥ ∨ t = ⊤)
: I = {} ∨ I = {⊤} ∨ I = {⊥} ∨ I = {⊥, ⊤} := by
  sorry
example
  (I : Set (Fin 2))
: I = {} ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  obtain ⟨I, rfl⟩ := Fintype.finsetEquivSet.surjective I
  simp_rw [Equiv.apply_eq_iff_eq_symm_apply]
  simpa using by decide +revert

example
  (I : Set (Fin 2))
: I = {} ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  have := Fintype.finsetEquivSet.surjective I
  obtain ⟨I', h⟩ := this
  rw [← h]
  simp_rw [Equiv.apply_eq_iff_eq_symm_apply]
  simp
  clear h I
  fin_cases I'
  <;> decide


theorem enumerate (I : Set (Set (Fin 2))) :
    I = {} ∨
    I = {{}} ∨ I = {{0}} ∨ I = {{1}} ∨ I = {{0, 1}} ∨
    I = {{}, {0}} ∨ I = {{}, {1}} ∨ I = {{}, {0, 1}} ∨
    I = {{0}, {1}} ∨ I = {{0}, {0, 1}} ∨ I = {{1}, {0, 1}} ∨
    I = {{}, {0}, {1}} ∨ I = {{}, {0}, {0, 1}} ∨ I = {{}, {1}, {0, 1}} ∨
    I = {{0}, {1}, {0, 1}} ∨
    I = {{}, {0}, {1}, {0, 1}} := by
  obtain ⟨I, rfl⟩ := (Fintype.finsetEquivSet.trans (Equiv.Set.congr Fintype.finsetEquivSet)).surjective I
  simp_rw [Equiv.apply_eq_iff_eq_symm_apply]
  simpa [Set.image_insert_eq] using by decide +revert

instance S4 : TopSpace (Fin 2) where
  IsOpen s := s = ⊥ ∨ s = ⊤
  isOpen_univ := by simp

  isOpen_inter u v hu hv := by
    obtain hu | hu := hu <;> obtain hv | hv := hv <;> simp [hu, hv]

  isOpen_sUnion I h := by
    have := enumerate I
    obtain hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI := this
    <;> simp_all [h, hI]

instance IncludedPoint (X : Type) (x : X) : TopSpace X where
  IsOpen s := s = ⊥ ∨ x ∈ s
  isOpen_univ := by simp

  isOpen_inter u v hu hv := by
    obtain hu | hu := hu <;> obtain hv | hv := hv <;> simp [hu, hv]

  isOpen_sUnion I h := by
    simp [h]
    by_cases h' : ((∀ s ∈ I, s = ∅))
    . left
      exact h'
    . simp at h'
      obtain ⟨ y, hy ⟩ := h'
      right
      use y
      constructor
      . exact hy.1
      . specialize h y hy.1
        simp_all


/-- A topology on `X`. -/
class TopSpace' (X : Type) where
  open_sets : Set (Set X)
  isOpen_univ : ⊤ ∈ open_sets
  isOpen_inter : ∀ s t, s ∈ open_sets → t ∈ open_sets → (s ∩ t) ∈ open_sets
  isOpen_sUnion : ∀ s : Set (Set X), (∀ t ∈ s, t ∈ open_sets) → (⋃₀ s) ∈ open_sets

instance S7 : TopSpace (Fin 3) where
  IsOpen s := s = ⊥ ∨ 0 ∈ s
  isOpen_univ := by simp

  isOpen_inter u v hu hv := by
    obtain hu | hu := hu <;> obtain hv | hv := hv <;> simp [hu, hv]

  isOpen_sUnion I h := by
    simp [h]
    by_cases h' : ((∀ s ∈ I, s = ∅))
    . left
      exact h'
    simp at h'
    obtain ⟨ x, hx ⟩ := h'
    right
    use x
    constructor
    . exact hx.1
    specialize h x hx.1
    simp [hx] at h
    exact h


instance S7' : TopSpace' (Fin 3) where
  open_sets := { ⊥ } ∪ { s | 0 ∈ s }
  isOpen_univ := by simp
  isOpen_inter u v hu hv := by
    obtain hu | hu := hu <;> obtain hv | hv := hv <;> simp_all
  isOpen_sUnion I h := by sorry



theorem set_univ : (Set.univ : Set (Fin 2)) = {1, 0} := by
  ext x
  simp
  fin_cases x <;> simp

instance sierpinsky_1 : TopSpace (Fin 2) where
  IsOpen s := s = ⊥ ∨ s = ⊤ ∨ s = {0}
  isOpen_univ := by simp

  isOpen_inter u v hu hv := by
    obtain hu | hu | hu := hu <;> obtain hv | hv := hv <;> simp [hu, hv] <;> tauto

  isOpen_sUnion I h := by
    have := enumerate I
    obtain hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI := this
    <;> simp_all [h, hI]
    <;> { right; rw [set_univ] }

def TopSpace.IsCoarser {X : Type} (T₁ T₂: TopSpace X) : Prop := ∀ x, (T₁.IsOpen x → T₂.IsOpen x)

example : S4.IsCoarser S1 := by
  intro x hx
  unfold TopSpace.IsOpen at *
  unfold S1 S4 at *
  dsimp at *

#check TopologicalSpace.IsTopologicalBasis

-- The discrete topology on a type `X` is the topology where every subset is open.
instance Discrete (X : Type) : TopSpace X where
  IsOpen s := true
  isOpen_univ := by rfl
  isOpen_inter u v hu hv := by rfl
  isOpen_sUnion I h := by rfl

-- The indiscrete topology on a type `X` is the topology where the only open sets are the empty set and the whole space.
instance Indiscrete (X : Type) : TopSpace X where
  IsOpen s := s = ⊥ ∨ s = ⊤
  isOpen_univ := by simp

  isOpen_inter u v hu hv := by
    obtain hu | hu := hu <;> obtain hv | hv := hv <;> simp [hu, hv]

  isOpen_sUnion I h := by
    have : ⊤ ∈ I ∨ ¬ (⊤ ∈ I) := by exact Classical.em (⊤ ∈ I)
    obtain hI | hI := this
    . right
      have : ⊤ ⊆ ⋃₀ I := by exact Set.subset_sUnion_of_subset I ⊤ (fun ⦃a⦄ a ↦ a) hI
      exact Eq.symm (Set.Subset.antisymm this fun ⦃a⦄ a ↦ trivial)
    . left
      have : ∀ t ∈ I, t = ⊥ := by
        by_contra h'
        apply hI
        rw [not_forall] at h'
        simp_rw [Classical.not_imp] at h'
        obtain ⟨ w, h1, h2 ⟩ := h'
        specialize h w h1
        have : w = ⊤ := by tauto
        rwa [this] at h1
      simp only [Set.bot_eq_empty, Set.sUnion_eq_empty]
      intro s hs
      specialize this s hs
      exact this



#synth UniformSpace ℝ

#check UniformSpace


example (I : Finset (Fin 2)) : I = {} ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  decide +revert

example (I : Finset (Fin 1)) : I = {} ∨ I = {0} := by
  decide +revert

example (I : Finset (Finset (Fin 1))) :
  I = {} ∨ I = {{}} ∨ I = {{0}} ∨ I = {{}, {0}} := by
  decide +revert

example (I : Finset (Finset (Fin 2))) :
    I = {} ∨
    I = {{}} ∨ I = {{0}} ∨ I = {{1}} ∨ I = {{0, 1}} ∨
    I = {{}, {0}} ∨ I = {{}, {1}} ∨ I = {{}, {0, 1}} ∨
    I = {{0}, {1}} ∨ I = {{0}, {0, 1}} ∨ I = {{1}, {0, 1}} ∨
    I = {{}, {0}, {1}} ∨ I = {{}, {0}, {0, 1}} ∨ I = {{}, {1}, {0, 1}} ∨
    I = {{0}, {1}, {0, 1}} ∨
    I = {{}, {0}, {1}, {0, 1}} := by
  decide +revert

example (I : Set (Finset (Fin 2))) :
    I = {} ∨
    I = {{}} ∨ I = {{0}} ∨ I = {{1}} ∨ I = {{0, 1}} ∨
    I = {{}, {0}} ∨ I = {{}, {1}} ∨ I = {{}, {0, 1}} ∨
    I = {{0}, {1}} ∨ I = {{0}, {0, 1}} ∨ I = {{1}, {0, 1}} ∨
    I = {{}, {0}, {1}} ∨ I = {{}, {0}, {0, 1}} ∨ I = {{}, {1}, {0, 1}} ∨
    I = {{0}, {1}, {0, 1}} ∨
    I = {{}, {0}, {1}, {0, 1}} := by
  obtain ⟨I, rfl⟩ := Fintype.finsetEquivSet.surjective I
  simp_rw [Equiv.apply_eq_iff_eq_symm_apply]
  simpa using by decide +revert

example (I : Set (Set (Fin 2))) :
    I = {} ∨
    I = {{}} ∨ I = {{0}} ∨ I = {{1}} ∨ I = {{0, 1}} ∨
    I = {{}, {0}} ∨ I = {{}, {1}} ∨ I = {{}, {0, 1}} ∨
    I = {{0}, {1}} ∨ I = {{0}, {0, 1}} ∨ I = {{1}, {0, 1}} ∨
    I = {{}, {0}, {1}} ∨ I = {{}, {0}, {0, 1}} ∨ I = {{}, {1}, {0, 1}} ∨
    I = {{0}, {1}, {0, 1}} ∨
    I = {{}, {0}, {1}, {0, 1}} := by
  obtain ⟨I, rfl⟩ := (Fintype.finsetEquivSet.trans (Equiv.Set.congr Fintype.finsetEquivSet)).surjective I
  simp_rw [Equiv.apply_eq_iff_eq_symm_apply]
  simpa [Set.image_insert_eq] using by decide +revert



structure Point where
  x : ℝ
  y : ℝ

instance Point.instSetoid : Setoid Point where
  r a b := a.x = b.x
  iseqv := {
    refl := by
      intro ⟨a, b⟩
      dsimp
    symm := by
      intro ⟨a, b⟩ ⟨c, d⟩ h
      linarith
    trans := by
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2
      simp at h1 h2 ⊢
      exact h1.trans h2
    }
