import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxDigitRows
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxDigitRun

/-! # Effective finite-control digit multipliers with physical time and space bounds -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack

open IntegerMultiplication CommonAlphabet
open IntegerMultiplication.Code (Cmd)

/-- The same computably numbered controls and public transition rules run each
certified multiplication body on the staged literal digit tapes. -/
theorem digit_family {R : ℕ} (hR : 0 < R) (p : ℕ → Cmd) (eff : Effective ltr p)
    (bound : ∀ j, CommonRegisters.Within R (p j)) (T : ℕ → ℕ → ℕ) (S C : ℕ → ℕ)
    (z : ℕ → MultiplicationInput → List Bool)
    (body : ∀ j, MultiplicationBody (p j) (T j) (S j) (C j) (z j))
    (product : ∀ j i, (z j i).length = 2*i.width ∧
      bitValue (z j i) = bitValue i.operands.1 * bitValue i.operands.2) :
    let cmd j := multiplyWrap (p j)
    let states j := digitNum R (cmd j)
    let entry j := digitEntry R (cmd j)
    let machine j := digitMachine hR (cmd j) (within_multiplyWrap hR (bound j))
    Computable (fun j => (states j).size) ∧ Computable (fun j => ((states j).equiv (entry j)).val) ∧
    Generator.EffectiveRows Numbering.publicLetter (digitIndexNum R) states machine ∧
    (∀ j, ∃ E : ℕ, 0 < E ∧ StagingCall.Computes (machine j) (entry j) (digitProduct (z j))
      (fun n => E*(T j n+n+1)) (fun n => E*(n+1))) ∧
    ∀ j (a : ChunkTask.EqualWords), (digitProduct (z j) a.val).length = 2*a.val.1.length ∧
      bitValue (digitProduct (z j) a.val) = bitValue a.val.1 * bitValue a.val.2 := by
  obtain ⟨size,start,rows⟩ := digitRows hR (fun j => multiplyWrap (p j)) (effective_multiplyWrap eff)
    (fun j => within_multiplyWrap hR (bound j))
  exact ⟨size,start,rows,fun j => digit_computes hR (bound j) (body j) (fun i => (product j i).1),
    fun j => digitProduct_spec (product j)⟩

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
