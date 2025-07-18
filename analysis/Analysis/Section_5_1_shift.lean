import Mathlib.Tactic
import Analysis.Section_5_1

namespace Chapter5

def Sequence.shift (a : Sequence) (d : ℤ) : Sequence :=
  mk' (a.n₀ - d) (fun i ↦ a (i + d))

lemma Sequence.shift_eval (a : Sequence) (n m : ℤ) :
  (a.shift n) m = a (m + n) := by
  simp [shift]
  intro h
  exact Eq.symm (a.vanish _ (by omega))

lemma Sequence.BoundedBy.ofShift (a : Sequence) (n : ℤ) (M : ℚ) :
  a.BoundedBy M → (a.shift n).BoundedBy M := by
  intro h m
  have := bound_nonneg a M h
  simp [shift]
  unfold BoundedBy at h
  obtain h1 | h2 := Decidable.em (a.n₀ ≤ m + n)
  · simp [h1]
    simp [h (m+n)]
  · simp [h2, bound_nonneg a M h]

lemma Sequence.normalForm_of_0start (s : Sequence) (hs : s.n₀ = 0): ∃ a : (ℕ → ℚ), a = (s:Sequence) := by
  use (fun n ↦ s n)
  ext i
  · rw [n0_coe, hs]
  obtain h | h := Decidable.em (0 ≤ i)
  · simp [h]
  · simp [h, s.vanish i (by omega)]

/--
Every sequence s can be written as a.shift d for some a : (ℕ → ℚ) and d : ℤ.
-/
lemma Sequence.normalForm (s : Sequence) : ∃ a : (ℕ → ℚ), ∃ d, s = (a:Sequence).shift d := by
  sorry

lemma Sequence.IsCauchy.shift {s : Sequence}  (d : ℤ) : (s.shift d).IsCauchy ↔ s.IsCauchy := by
  sorry

lemma Sequence.IsBounded.shift {s : Sequence}  (d : ℤ) : (s.shift d).IsBounded ↔ s.IsBounded := by
  constructor
  · intro h
    obtain ⟨ M, hM, hB ⟩ := h
    use M
    constructor
    . exact hM

    intro i
    unfold BoundedBy at hB
    specialize hB (i - d)
    simp [shift_eval] at hB
    exact hB

  intro h
  obtain ⟨ M, hM, hB ⟩ := h
  use M
  constructor
  . exact hM
  intro i
  simp [shift_eval]
  specialize hB (i + d)
  exact hB

lemma Sequence.isBounded_coe_of_isCauchy_coe {s : (ℕ → ℚ)} (h: (s:Sequence).IsCauchy) : (s:Sequence).IsBounded := by
  sorry

/-- Lemma 5.1.15 (Cauchy sequences are bounded) / Exercise 5.1.1 -/
lemma Sequence.isBounded_of_isCauchy' {s:Sequence} (h: s.IsCauchy) : s.IsBounded := by
  obtain ⟨ a, d, rfl ⟩ := normalForm s
  rw [IsCauchy.shift, IsBounded.shift] at *
  exact isBounded_coe_of_isCauchy_coe h
