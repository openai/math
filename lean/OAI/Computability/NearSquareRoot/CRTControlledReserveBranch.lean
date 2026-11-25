import OAI.Computability.NearSquareRoot.InterchangeBQuestBranch

/-! # Dispatch on an address width encoded on the input tape -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveSmall

open IntegerMultiplication.Code NearSquareRoot.Space

/-- Read the flag prepared on tape and enter the corresponding fixed program.
Both programs receive the original input, with a shared space bound. -/
theorem boundedWidthBranch {I : Type*} (K : ℕ) (k V T : I → ℕ) (input output : I → Tree)
    (room : ∀ i, V i ≤ T i)
    (flag : BoundedTask V V input (fun i => .fork (.atom (decide (K < k i))) (input i)))
    (low : BoundedTask (fun i : {i // k i ≤ K} => T i) (fun i => V i)
      (fun i => input i) (fun i => output i))
    (high : BoundedTask (fun i : {i // K < k i} => T i) (fun i => V i)
      (fun i => input i) (fun i => output i)) : BoundedTask T V input output := by
  obtain ⟨scan,C,prepare⟩ := flag
  obtain ⟨left,L,small⟩ := low
  obtain ⟨right,H,large⟩ := high
  let D := C+L+H+10
  have capacity (w : ℕ) : C*(w+1)+(L+H)*(w+1)+10 ≤ D*(w+1) := by
    simp only [D, Nat.add_mul]
    omega
  refine ⟨Space.dispatch scan left right, D, ?_⟩
  intro i env stack base hs
  let cap := base+D*(V i+1)
  let depth := D*(V i+1)
  have enough := capacity (V i)
  have prep := (prepare i env stack base hs).mono (Nat.mul_le_mul_left C (Nat.succ_le_succ (room i)))
    (show base + C*(V i+1) ≤ cap by dsimp [cap]; omega) le_rfl
  have body : BoundedFits env (bif decide (K < k i) then right else left)
      (pile 0 (input i) stack) (pile 0 (output i) stack) ((L+H)*(T i+1)) cap depth := by
    by_cases h : K < k i
    · simp only [h, decide_true, Bool.cond_true]
      have run := large ⟨i,h⟩ env stack base hs
      dsimp only at run
      have bound w := Nat.mul_le_mul_right (w+1) (Nat.le_add_left H L)
      exact run.mono (bound _) (by dsimp [cap]; have := bound (V i); omega)
        (by dsimp [depth]; have := bound (V i); omega)
    · simp only [h, decide_false, Bool.cond_false]
      have run := small ⟨i,Nat.le_of_not_gt h⟩ env stack base hs
      dsimp only at run
      have bound w := Nat.mul_le_mul_right (w+1) (Nat.le_add_right L H)
      exact run.mono (bound _) (by dsimp [cap]; have := bound (V i); omega)
        (by dsimp [depth]; have := bound (V i); omega)
  exact (prep.dispatch body (by dsimp [depth]; omega)).mono (capacity (T i)) le_rfl le_rfl

end Controlled.ReserveSmall

end NearSquareRoot
end Computability
end OAI
