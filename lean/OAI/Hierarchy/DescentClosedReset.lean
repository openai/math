import OAI.Hierarchy.DescentResetRateData
import OAI.Hierarchy.DescentReached
import OAI.Hierarchy.DescentEpochReset
import OAI.Hierarchy.DescentNamedReset

namespace OAI
/-! # A physical reset receipt for the reached parent -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentColonies DescentFineTerminals DescentResetInvoice DescentBaseProfile
open DescentRotor DescentMixedRouter DescentHostDegree
open LinearAlgebra.SpectralBooks ThreeFlat
open Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z w hist : ℕ}

structure ClosedReset {W : MarkedWorld F d P bits} {D n h C f g cut tail : ℕ}
    (input : Reached W G q ε S k i z D w hist)
    (ctl : ResetRates G S k D n h C f g cut tail) where
  count : W.graph.Edge→ℕ
  count_eq : count=input.placement.grainCount
  fit : ∀e,W.graph.width e=count e*(z*G.b)
  order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)
  order_eq : order=input.order
  reset : ResetInput (W.granular count (z*G.b) fit) (q*w) ε h C (GroupStage.depthBound D n f g)
  terminals : reset.Terminals
  age : i < S.length
  commonDepth : terminals.commonDepth = S.groupWidth k tail i
  keyWidth : reset.k = S.groupWidth k tail i + k
  tickets : reset.placement.OrderedTickets (DescentOrderedReset.grains W count order)
  unit : reset.unit=z*G.b
  dimension : reset.n=n
  width : reset.width=ctl.bitsR
  graph : HEq reset.graph ctl.board
  frame : reset.SourceFrame terminals (fun v=>(input.placement.pos v).2) (StarKeys.filled W.graph
    input.placement.pos input.placement.block (S.resetInputDigits ctl.base ctl.radix i)) input.placement.hub g
  roster : ResetInput.SourceFrame.Roster reset terminals (fun v=>(input.placement.pos v).2)
    (StarKeys.filled W.graph input.placement.pos input.placement.block (S.resetInputDigits ctl.base ctl.radix i))
    input.placement.hub g frame (input.vertex.trans Fin.valEmbedding) input.placement.mutual n f (w*(z*G.b)*input.placement.cap)
    w (quota S.rounds) (fun a b j=>(pairLoad (W.countWorld count) (fun v=>(input.placement.pos v).2)
      (StarKeys.filled W.graph input.placement.pos input.placement.block (S.resetInputDigits ctl.base ctl.radix i))
      (w*(z*G.b)) a b j:ℝ)) input.placement.degree (input.placement.resetLoad (S.resetInputDigits ctl.base ctl.radix i))
  raw : GroupStage (reset.orderedOrdinary terminals (DescentOrderedReset.grains W count order)) G q ε
    (Fin (S.groupCount (i+1))) ↥(reset.commonNames terminals) k
  rawGeometry :
    let digits := S.resetOutputDigits ctl.base ctl.radix age commonDepth
    raw.pos = reset.groupPosition terminals digits ∧ raw.block = reset.groupBlock terminals digits
  rawHub : raw.hub=reset.commonTag terminals
  valid : raw.StateBounds S (i+1)
  grain : raw.z=z
  wire : raw.wire=w
  atoms : raw.hist=hist
  degree : raw.degree=3
  capacity : raw.cap=2^g*input.placement.cap

namespace ClosedReset
variable {W : MarkedWorld F d P bits} {D n h C f g cut tail : ℕ}
variable {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
variable (B : ClosedReset input ctl)
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "key" => DescentOrderedReset.grains W B.count B.order

def reblock : Normalize (B.reset.orderedReentry B.terminals key) :=
  B.reset.namedReset B.terminals vertex key B.raw B.valid

theorem cuts : Normalize.CutsEqual B.reset.unit B.reblock :=
  (B.reset.namedCuts B.terminals vertex key B.raw B.valid _).2 ⟨rfl,trivial⟩

def next : Reached B.reblock.result G q ε S k (i+1) z 3 w hist := by
  have sc := B.reset.namedScalars B.terminals vertex key B.raw B.valid
  exact ⟨_,B.reset.namedPlacement B.terminals vertex key B.raw B.valid,
    B.reset.namedBounds B.terminals vertex key B.raw B.valid,sc.1.trans B.grain,sc.2.1.trans B.wire,
    sc.2.2.1.trans B.atoms,sc.2.2.2.trans B.degree,B.reset.namedOrder B.terminals vertex key B.raw B.valid,
    B.reset.denseHostRank B.terminals vertex,fun _=>B.reset.namedEdges B.terminals vertex key B.raw B.valid,
    fun _=>B.reset.namedSites B.terminals vertex key B.raw B.valid⟩

theorem next_hub : B.next.placement.hub=B.reset.commonTag B.terminals :=
  (B.reset.namedHub B.terminals vertex key B.raw B.valid).trans B.rawHub

def factor (_B : ClosedReset input ctl) := 2^g

include B in
theorem next_capacity : B.next.placement.cap=2^g*input.placement.cap :=
  (B.reset.namedCapacity B.terminals vertex key B.raw B.valid).trans B.capacity

end ClosedReset

end
end Hierarchy.DescentSixParty

end OAI
