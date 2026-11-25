import OAI.Hierarchy.ProbeFixedSelectorCircuit
import OAI.Hierarchy.ProbeNativePacketAmounts

namespace OAI
/-! # The fixed signed circuit on the actual selected counter words -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Fin.CommRing

variable {F E A : Type} [Field F] [Fintype E] [Fintype A] {k rows d w extra : ℕ}
    [Nonempty (Fin k)] {edge : E→Chord k} {req : A→E} {P : Probe.Packet F edge req}
    {b : Batch (P.terms+extra) d} {s : Calendar.StockCommit} {mem : Memory w}
    {layout : PortPlan s b mem rows} {j : Fin rows}

omit [Nonempty (Fin k)] in
/-- The accepted row's public histogram pins are the actual native field
bits at the same selected candidate register, including a padded alphabet. -/
theorem NativePacketRow.physical_counters (R : NativePacketRow P extra b layout j) (digits : ℕ) :
    (fun (t : Fin P.terms) (u : Fin digits)=>
      ((b.field (t.castAdd extra)).eval mem (j.val:Word w)).val.testBit u.val)=
      Probe.SelectorShelf.bits R.h digits := by
  funext t u
  simp [R.fields,Probe.SelectorShelf.bits,padHistogram]

open Probe LinearAlgebra.SpectralBooks
open ThreeFlat Routing Diagonal MotifBinaryPacking TraceCircuit

/-- At the chosen row the fixed trivalent site reads the live public wires
at that very same ordinal. -/
theorem NativePacketRow.terminal_signed_site {B : Type} [Fintype B]
    (R : NativePacketRow P extra b layout j) (rt : Fin k) (G : PortGraph (Fin k) B)
    (i : Fin k) (p : (portGraph k).Port i)
    (fit : b.copies*P.selectorBits≤G.chordWidths (fun _=>b.copies*P.selectorBits) p.val.1)
    (x : State (P.inputWidths b.copies) i)
    (z : State (P.outputWidths R.h+G.chordWidths (fun _=>b.copies*P.selectorBits)) i) :
    let q:=G.chordWidths (fun _=>b.copies*P.selectorBits)
    let yz:=splitPortState (P.outputWidths R.h) q i z
    let c:=BroadcastPins.candidate q i p yz.2 (b.copies*P.selectorBits)
    let digits:=Nat.clog 2 (b.copies+1)
    let pub:=(fun (t : Fin P.terms) (u : Fin digits)=>
      ((b.field (t.castAdd extra)).eval mem (j.val:Word w)).val.testBit u.val)
    let wordBits:=(blocks b.copies P.selectorBits).symm ((word _).symm c)
    P.broadcastMatrix rt b.copies G R.h i x z=
      TypedWiring.value (BroadcastPins.network F q i p fit) (BroadcastPins.read q i yz.2)*
        ((SelectorShelf.network F (NativeHistogram.alphabet_pos P) b.copies P.selectorBits digits).eval
          (SelectorShelf.pins wordBits pub)*
         TypedWiring.value (SiteHardware.typedSite P i b.copies) (P.rawSiteView R.h i c x yz.1)) := by
  dsimp only
  rw [R.physical_counters]
  exact P.fixed_signed_site rt G R.h i p fit x z


end Hierarchy.ProtocolRAM.Calendar.StockCommit
end

end OAI
