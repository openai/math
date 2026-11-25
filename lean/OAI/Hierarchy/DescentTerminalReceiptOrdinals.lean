import OAI.Hierarchy.DescentTerminalPrimitiveReceipts

namespace OAI
/-! # Transport of the eight observed fields along equal birth ordinals -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalChronologicalBooks DescentKernelHistory DescentTerminalRecipeRows
open DescentTerminalPrintedFields DescentTerminalLeafDigits DescentTerminalScalarHeader
open scoped Classical
noncomputable section
variable {q t H N A:ℕ} {site:Site} {r:∀v:Fin site.nodes,Recipe (Fin t) (Fin (site.arity v))}
  {earlier later:Birth r} {hH:∀v,Fintype.card (r v).Hidden≤H} {hN:∀v,Fintype.card (r v).Node≤N}
  {hA:∀v j,(r v).arity j≤A} {v:Fin site.nodes} {data:Key H N A→ℕ}

/-- Identical ordinal ranks for the living names and gates preserve all eight
native field readbacks. This applies even when the raw numerical names differ. -/
theorem PrimitiveReceipts.of_ordinals (proof_:PrimitiveReceipts (q:=q) site r earlier hH hN hA v data)
    (hidden:∀x,ordinal (earlier.hidden v) x=ordinal (later.hidden v) x)
    (nodes:∀u,ordinal (earlier.atom v) u=ordinal (later.atom v) u) :
    PrimitiveReceipts (q:=q) site r later hH hN hA v data := by
  refine ⟨proof_.ports,proof_.live,proof_.hidden,proof_.nodes,?_,?_,?_,?_⟩
  · intro j
    simpa only [←hidden j] using proof_.width j
  · intro u
    simpa only [←nodes u] using proof_.role u
  · intro u
    simpa only [←nodes u] using proof_.arity u
  · intro u j
    simpa only [←nodes u,←hidden] using proof_.operand u j

end
end Hierarchy.DescentTerminalVertexFields

end OAI
