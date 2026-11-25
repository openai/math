import OAI.Computability.BorderVNP.PackedFrozenNamedEmit

/-! # Gate count and bit values under reindexing of the frozen node's output -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

open VPVNP.VerifierNetwork

variable {I Old New : Type} {fi : Fintype I} {fo : Fintype Old} [fn : Fintype New]
    (f : @Frame I Old fi fo) (wire : New → Old)

/-- Selecting the chronological format's output wires preserves the gate count. -/
@[simp] theorem keepPins_size : @Frame.size I New fi fn (keepPins f wire) = @Frame.size I Old fi fo f :=
  @Frame.select_size I Old New fi fo fn f wire

/-- The selected wire is the computed bit of the actual emitter, using its source enumeration. -/
theorem keepPins_eval (x : I → Bool) :
    @Frame.eval I New fi fn (keepPins f wire) x = (@Frame.eval I Old fi fo f x) ∘ wire :=
  funext (@Frame.select_eval I Old New fi fo fn f wire x)

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

end BorderVNP
end Computability
end OAI
