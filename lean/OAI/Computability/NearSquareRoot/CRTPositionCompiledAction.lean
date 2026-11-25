import OAI.Computability.NearSquareRoot.CRTPositionEvaluation
import OAI.Computability.NearSquareRoot.CRTPositionTableAction

/-! # Correctness and setup cost of the serialized bit-position schedule -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionPreparation

set_option synthInstance.maxSize 5000

open IntegerMultiplication.Code Reflections

/-- Execute the two serialized rounds on a word. Applying the second reflected
lookup first gives the pullback along the original position permutation. -/
def execute {k : ℕ} (code : RoundCode × RoundCode) (w : Fin k → Bool) : Fin k → Bool :=
  executeRound @runTables code.1 (executeRound @runTables code.2 w)

/-- The returned instructions, interpreted without access to the original
permutation, carry every address bit to its specified position. -/
theorem execute_compilePositions {k : ℕ} (p : Equiv.Perm (Fin k)) (w : Fin k → Bool) :
    execute (compilePositions (table p)) w = w ∘ p := by
  have firstInv : Function.Involutive (first p) := forwardMirror_involutive p
  have secondInv : Function.Involutive (second p) := shiftedMirror_involutive p
  have good {m : ℕ} (v : Equiv.Perm (Fin (3*m))) (hv : Function.Involutive v) (z : Fin (3*m) → Bool) :=
    runTables_value v hv z
  rw [compilePositions_value]
  change executeRound @runTables (roundSpec (first p) firstInv)
    (executeRound @runTables (roundSpec (second p) secondInv) w) = _
  rw [executeRound_value @runTables (@good) (second p) secondInv w,
      executeRound_value @runTables (@good) (first p) firstInv]
  funext x
  exact congrArg (fun q : Equiv.Perm (Fin k) => w (q x)) (factor p)

/-- The two occurrences of the six-pair schedule use 72 directed XOR layers.
Each diagonal pair uses nine and each off-diagonal pair uses three. -/
theorem xor_count :
    2 * (FixedSchedule.pairs.map (fun q => if q.1 = q.2 then 9 else 3)).sum = 72 := by decide

theorem tail_count {k : ℕ} (p : Equiv.Perm (Fin k)) :
    let code := compilePositions (table p)
    code.1.2.length + code.2.2.length ≤ 4 := by
  simp only [compilePositions_value,roundSpec,List.length_map]
  have a := TailTable.three_chunks_count (first p)
  have b := TailTable.three_chunks_count (second p)
  omega

/-- Uniform polynomial-time preparation and exact bit action for every width,
including the empty layout and widths not divisible by three. -/
theorem compiled_route {X : Type} (k : X → ℕ) (p : (x : X) → Equiv.Perm (Fin (k x))) :
    Task.BT k (fun x => send (table (p x))) (fun x => send (compilePositions (table (p x)))) ∧
    ∀ x (w : Fin (k x) → Bool), execute (compilePositions (table (p x))) w = w ∘ p x := by
  exact ⟨poly_compilePositions.on (show Dom k (fun x => size (table (p x))) from
    ⟨2,2,fun x => table_size (p x)⟩),fun x => execute_compilePositions (p x)⟩

end Controlled.PositionPreparation

end NearSquareRoot
end Computability
end OAI
