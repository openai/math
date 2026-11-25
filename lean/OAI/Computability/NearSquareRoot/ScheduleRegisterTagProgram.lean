import OAI.Computability.NearSquareRoot.ScheduleRegisterTagFold
import OAI.Computability.NearSquareRoot.ScheduleRegisterTagCodedEffective
import OAI.Computability.NearSquareRoot.ScheduleRegisterAlignEffectiveTable

/-! # Assembling the generated parity-table command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterTagProgram
open IntegerMultiplication Code GeneratorSyntax EffectiveTask Filter RegisterTagCoded

abbrev value (p : P) :=
  KernelScaleStream.tag (KernelComputableSelector.test (p.1+1) p.2.1 p.2.2)

abbrev TableFamily (R : ℕ) := Family (P := P) R
  (fun p f => ((p.1+1)*f+1)*2^((p.1+1)*f)) (fun p f => send (tally ((p.1+1)*f)))
  (fun p f => send ((KernelSelector.addressColumns p.1 f).map (value p)))

theorem fromTables (tick : Effective ltr (fun p => RegisterTable.command (table p)))
    (finish : Effective ltr (fun p => RegisterTable.command (finishTable p))) :
    ∀ᶠ R : ℕ in atTop, TableFamily R := by
  have scan := RegisterTagFold.aligned Prod.fst state stateTree seed step
    (fun p s => send (tally (result p s))) seed_tree
  filter_upwards [eventually_ge_atTop 2,scan,EffectiveColumns.tabulateColumnLookup] with R hR hs ht
  apply ht Prod.fst Computable.fst value
  apply hs
  · refine ⟨_,tick,fun p => ⟨within_step hR p,RegisterTable.cost (table p),fun u env r => ?_⟩⟩
    simpa only [Nat.zero_add,Nat.mul_one] using run_step p u.2 u.1 env r
  · refine ⟨_,finish,fun p => ⟨within_finish hR p,RegisterTable.cost (finishTable p),fun s env r => ?_⟩⟩
    simpa only [Nat.zero_add,Nat.mul_one] using run_finish p s env r

/-- One computable family emits the whole parity-tag table procedure, with one
absolute register cutoff across every mask vector, test count and arity. -/
theorem generate : ∀ᶠ R : ℕ in atTop, TableFamily R :=
  fromTables effective_step effective_finish

end RegisterTagProgram

end NearSquareRoot
end Computability
end OAI
