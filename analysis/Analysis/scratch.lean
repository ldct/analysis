import Mathlib

structure Struct where
  n₀ : ℤ

instance Struct.instCoe : Coe (ℕ → ℕ) Struct where
  coe := fun a ↦ {
    n₀ := a 0
  }

abbrev zero (a: Struct) : Prop :=
  a.n₀ = 0

lemma isZero_of_coe (a:ℕ → ℕ)
  : zero (a:Struct) ↔ 1 = 1 := by sorry

example : zero ((fun _:ℕ ↦ 3):Struct) := by
  rw [isZero_of_coe (fun _:ℕ ↦ 3)]

example : zero ((fun _:ℕ ↦ 3):Struct) := by
  rw [isZero_of_coe _]
