import OAI.Hierarchy.DescentResetWindowCompare

namespace OAI
/-! # A bounded authentic source ticket for every positive post-reset window -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open Computability.BorderVNP.Crossing DescentCompiler DescentColonies DescentPhysicalOrder DescentPacking
open DescentSharedCableNames DescentSharedCableNames.Siblings DescentParallelBase
open DescentStageEdgeReceipt DescentCableUnbundling
open scoped Classical BigOperators
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "cnt" => fun e=>(coarse).graph.width e/(Z).unit
local notation "world" => (Z).orderedOrdinary T birth
local notation "tape" => (Z).nativeResetEdges T vertexCode birth
local notation "index" => (tape).order.trans Fin.valEmbedding
local notation "dense" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "groups" => S.groupCount (i+1)
local notation "rawSite" => B.raw.siteFrom (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groups)) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw index S B.valid rawSite
local notation "renameEdge" => DescentPhysicalOrder.rename sparse
local notation "next" => B.reblock.result
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "stream'" => Stage.stream A ord
local notation "board" => Stage.source A ord
local notation "wt" => weight B
local notation "grains" => emit B
local notation "piece'" => piece B
local notation "base'" => first B


theorem head_grains (e : (coarse).graph.Edge) (live : 0<wt e) :
    0<B.raw.grainCount (rawHead B e live) := by
  let r₀:=rawHead B e live
  have shape : (A).grainCount (renameEdge r₀)=B.raw.grainCount r₀ := by
    change (PhysicalRename.graph (world).graph hop renameEdge).width (renameEdge r₀)/((A).z*G.b)=
      (world).graph.width r₀/(B.raw.z*G.b)
    rw [PhysicalRename.width,B.next.grain,B.grain]
  let grain:=grains ⟨e,⟨0,live⟩⟩
  have active : 0<(A).grainCount grain.1:=Nat.zero_lt_of_lt grain.2.isLt
  rw [show grain.1=renameEdge r₀ from (head_emit B e live).1,shape] at active
  exact active

/-- The source name is a real bounded incidence of the unrenamed
post-normalization tape containing every retained or newly born grain. -/
def sourceTicket (e : (coarse).graph.Edge) (live : 0<wt e) : Fin B.raw.cap :=
  Stage.outgoing B.raw index S B.valid ⟨rawHead B e live,head_grains B e live⟩

theorem sourceTicket_lt (e f : (coarse).graph.Edge) (he : 0<wt e) (hf : 0<wt f)
    (same : (coarse).graph.src e=(coarse).graph.src f) :
    sourceTicket B e he<sourceTicket B f hf ↔
      ((Z).installedResetOrdinal T vertexCode birth e).val<((Z).installedResetOrdinal T vertexCode birth f).val := by
  have heads : (world).graph.src (rawHead B e he)=(world).graph.src (rawHead B f hf):=
    (head_fields B e he).2.2.1.trans (same.trans (head_fields B f hf).2.2.1.symm)
  exact (Stage.outgoing_lt B.raw index S B.valid ⟨_,head_grains B e he⟩ ⟨_,head_grains B f hf⟩ heads).trans
    (prefix_lt B e f he hf)

theorem earlier_tickets (e f : (coarse).graph.Edge) (he : 0<wt e) (hf : 0<wt f) :
    (blocks B).first e<(blocks B).first f ↔
      rawSite ((coarse).graph.src e)<rawSite ((coarse).graph.src f) ∨
      rawSite ((coarse).graph.src e)=rawSite ((coarse).graph.src f) ∧ sourceTicket B e he<sourceTicket B f hf := by
  rw [first_before B e f he hf]
  constructor <;> rintro (lt|⟨same,lt⟩)
  · exact Or.inl lt
  · exact Or.inr ⟨same,(sourceTicket_lt B e f he hf ((rawSite).injective same)).mpr lt⟩
  · exact Or.inl lt
  · exact Or.inr ⟨same,(sourceTicket_lt B e f he hf ((rawSite).injective same)).mp lt⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
