import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomBlend
import OAI.Computability.NearSquareRoot.ScheduleRegisterWitness

/-! # Common-register witnesses for the finite-series and narrow transpose primitives -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open Space RegisterWitness

variable {I K : Type}

theorem finite_cell_checked [DecidableEq K] (s : Series K) (v : I → K → Tree) (k : K) :
    let p := stackRun (fun _ => s) v
    Bounded 3 (fun i => (p i).count) (fun i => (p i).count) p (fun i => v i k) := by
  refine ⟨cellCommand (s.explore.idxOf k), cell_within _, 91, fun i env r base hr => ?_⟩
  exact (finite_cell_bounded s (v i) k env r base hr).mono (by dsimp [stackRun]; omega)
    (by dsimp [stackRun]; omega) (by dsimp [stackRun]; omega)

theorem column_checked {A : I → Type} [DecidableEq K] (cols : Series K)
    (rows : (i : I) → Series (A i)) (v : (i : I) → A i → K → Tree) (k : K) :
    let p := stackRun rows (fun i => stripe cols ∘ v i)
    Bounded 3 (fun i => (p i).count) (fun i => (p i).count)
      p (stackRun rows (fun i a => v i a k)) := by
  refine ⟨columnCommand (cols.explore.idxOf k), column_within _, 192, fun i env r base hr => ?_⟩
  exact (column_bounded cols (rows i) (v i) k env r base hr).mono (by dsimp [stackRun]; omega)
    (by dsimp [stackRun]; omega) (by dsimp [stackRun]; omega)

/-- P192's finite outer series is fixed in each program. Its inner record
series and all tree values vary with the runtime instance. -/
theorem unlay_checked {A : I → Type} [DecidableEq K] (cols : Series K)
    (rows : (i : I) → Series (A i)) (v : (i : I) → A i → K → Tree) :
    let p := stackRun rows (fun i => stripe cols ∘ v i)
    Bounded 3 (fun i => (cols.count + 1) * ((p i).count + 1))
      (fun i => (p i).count + cols.count) p
      (stackRun (fun _ => cols) (fun i k => stripe (rows i) fun a => v i a k)) := by
  refine ⟨transposeCommand cols, transpose_within _, 253, fun i env r base hr => ?_⟩
  have h := transpose_bounded cols (rows i) (v i) env r base hr
  apply h.mono
  · dsimp only [stackRun]
    rw [Nat.mul_assoc]
    omega
  · dsimp only [stackRun]
    omega
  · dsimp only [stackRun]
    omega

/-- Both dimensions vary at runtime for the inverse. The input includes the
empty-row scaffold that P192 supplies to its inverse narrow transpose. -/
theorem lay_checked {A B : I → Type} (cols : (i : I) → Series (B i))
    (rows : (i : I) → Series (A i)) (v : (i : I) → A i → B i → Tree) :
    let p := fun i => Tree.fork (stripe (cols i) (fun k => stripe (rows i) (fun a => v i a k)))
      (stripe (rows i) (fun _ => .atom false))
    Bounded 4 (fun i => ((cols i).count + 1) * ((p i).count + 1))
      (fun i => (p i).count) p (stackRun rows (fun i => stripe (cols i) ∘ v i)) := by
  refine ⟨blendCommand, blend_within, 401, fun i env r base hr => ?_⟩
  have h := blend_bounded (cols i) (rows i) (v i) env r base hr
  apply h.mono
  · dsimp only
    rw [Nat.mul_assoc]
    omega
  · dsimp only
    omega
  · dsimp only
    omega

/-- Assemble finitely many already bounded fields using the largest temporary
allowance of a single field. The output remains present until return. -/
theorem finite_series_checked {R : ℕ} (hR : 3 ≤ R) (s : Series K)
    (input : I → Tree) (v : I → K → Tree) (t : I → K → ℕ) (S : I → ℕ)
    (fields : ∀ k, Bounded R (fun i => t i k) S input (fun i => v i k)) :
    let out := stackRun (fun _ => s) v
    Bounded R (fun i => costSum (fun k => (input i).count + 1 + (t i k + 1)) s.explore
      + (input i).count + 1) (fun i => (input i).count + (out i).count + S i + 1) input out := by
  classical
  choose op hOp C hC using fields
  let M := costSum C s.explore
  have bound (k : K) : C k ≤ M :=
    List.single_le_sum (l := s.explore.map C) (fun _ _ => Nat.zero_le _)
      _ (List.mem_map_of_mem (s.complete k))
  refine ⟨seriesCommand op s.explore, series_within hR op _ hOp, M + 100,
    fun i env r base hr => ?_⟩
  have run := series_bounded op (input i) (v i) (fun k => C k * (t i k + 1))
    (M * (S i + 1)) (fun k E deck b hd => (hC k i E deck b hd).mono le_rfl
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (bound k)) _) (Nat.mul_le_mul_right _ (bound k)))
    s.explore env r base hr
  rw [← stripe_simple] at run
  apply run.mono
  · let V := (input i).count
    let u k := V + 1 + (t i k + 1)
    have sum := costSum_le (s := s.explore) (t := fun k => 45 * V + C k * (t i k + 1) + 7)
      (u := fun k => (M + 60) * u k) (fun k _ => by
        have h := Nat.mul_le_mul_right (t i k + 1) (bound k)
        dsimp [u]
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one] at *
        omega)
    rw [costSum_mul] at sum
    change costSum _ s.explore + 60 * V + 10 ≤ (M + 100) * (costSum u s.explore + V + 1 + 1)
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one] at *
    dsimp only [V] at sum ⊢
    omega
  · dsimp only [stackRun]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  · dsimp only [stackRun]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
