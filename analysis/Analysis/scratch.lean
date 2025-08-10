import Mathlib

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
