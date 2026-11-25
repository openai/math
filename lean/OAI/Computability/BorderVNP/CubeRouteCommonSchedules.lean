import OAI.Computability.BorderVNP.CubeRouteCanonicalWriters
import OAI.Computability.BorderVNP.CubeRoutePackedExteriorLayouts

/-! # Common native writer receipts at the actual joint public return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube LocalRow CubeArena CubeHeaderInstall Crossing Physical MeanChoice LabelIndex
open BorderVNP.TeamContraction BorderVNP.Routing BorderVNP.RoutingISA.Transmission

/-- Canonicalize every received eleven-stage writer receipt on the exact nine-stage prefix of
its own run. Directory, symbol owner and receiving-cell agreement follow from the original
placements and the two native label passes. All processor states and trace words are retained. -/
theorem packed_returned_writers {R w D : ℕ} {T : Type*} (team : T → Fin (R+1)) (ref : T) (a : CubeArena.Layout) (frame controls : ℕ) (axis : Fin (a.n+1))
    (pub : T → Arg → Word w) (mac : T → TeamOpcode.Macros w 8)
    (banks afterLabels : T → Bank w) (mem selected : T → Memory w)
    (trace : T → List (TeamRAM.Event w))
    (f : T → BroadcastFrame) (old : T → Fin 81 → Word w)
    (fresh profile gates outputs bits off ell : ℕ) (raw : List Bool)
    (pins : ∀ u, BootPins (pub u) (f u) (jointFields (a.extension (old u)) fresh profile gates outputs bits off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) raw (mem u))
    (fit : ∀ u, LabelPrefixFits (pub u 0).val w (readings (mem u)))
    (labelRun : ∀ u, Runs (pub u) (mac u) (.seq LabelIndex.directoryProgram NativeIntervals.prepare)
      (banks u) (mem u) (trace u) (afterLabels u) (selected u))
    (count : ∀ u, readings (mem u) ((pub u 0).val+11)=a.cells) (room : a.stop < 2^w)
    (rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ) (axes : a.header.a=a.n+1) (positive : 0 < a.header.d)
    {P : Type*} {pinWidth : P → ℕ} (N : Network D P pinWidth) (cell : N.Site → Fin a.cells)
    {A : Type*} [Fintype A] (recv : A → Fin a.cells) (width : A → ℕ)
    (directory : Packing.Directory.Layout) (pp lp : T → ℕ → ℕ × ℕ)
    {I : Type*} [Fintype I] (hostCell : I → Fin a.cells) (id : I ↪ ℕ) (bitsAt : I → ℕ)
    (placed : ∀ u, Packing.Directory.BankPlacement directory (pp u) (lp u) I hostCell id bitsAt)
    (keys : ∀ u k, (placed u).key k=(placed ref).key k) (bounds : directory.DestinationBounds)
    (ports : T → Pins.Layout) (preTicks : T → ℕ) (pass : T → Prop) (regs : T → Bank w) (memOut : T → Memory w)
    (events : T → List (TeamRAM.Event w)) (who : ∀ u, (f u).team=(team u).val) :
    let dir := fun u => LabelIndex.layout (pub u 0).val (readings (mem u))
    let cells := fun u => finCongr ((count u).symm : a.cells=(dir u).cells)
    let input := fun u => powerHeaderImage a (f u).dst (readings (selected u))
    let group := fun u (g : Fin a.header.d) => TeamNative.owner R ((weightLayout a frame axis.val).weight (input u)) g.val
    let owner := fun u => a.receivingOwner frame axis R (input u)
    ∀ (edges : ∀ u, N.CrossingEdge cell ↪ Fin (dir u).cableCount) (data : ∀ u, A ↪ Fin (dir u).deliveryCount),
      (∀ u, RowPlacement (networkRows N cell recv width) (fromTables (dir u) (readings (mem u)) (fit u).endpoints)
        (cells u) ((edges u).sumMap (data u))) →
      (∀ u, TestRun (pub u) (mac u) (.block (beforeWriters a.n (Tally.selectorWidth a.n a.K a.h))) (banks u)
        (mem u) (preTicks u) (pass u) (fun z => WriterSources a frame controls (f u).team R ⟨axis,rows⟩ (group u)
          (readings (pub u)) (input u) (readings (mem u)) z.mem w)) →
      ∀ H : ∀ u, WriterHistory a.n (Tally.selectorWidth a.n a.K a.h) (pub u) (mac u) (banks u) (mem u)
        (events u) (regs u) (memOut u),
      (∀ u, ReturnedWriters a directory (pp u) (lp u) (owner u) ⟨axis,rows⟩ (group u) (ports u) (H u)) →
      ∀ u, pass u ∧ ReturnedWriters a directory (pp ref) (lp ref) (owner ref) ⟨axis,rows⟩ (group ref) (ports u) (H u) := by
  intro dir cells input group owner edges data labelPlace before H done
  have post u := (before u).sound (H u).prefixRun
  have owners := packed_exterior_owners team ref a frame controls axis pub mac banks afterLabels mem selected trace
    (fun u => readings (H u).dataInput) f old fresh profile gates outputs bits off ell raw pins fit labelRun count
    room rows axes positive N cell recv width edges data labelPlace (fun u => (post u).2.1)
    (fun u => by rw [← who u]; exact (post u).2.2)
  intro u
  exact ⟨(post u).1,(done u).congr_tables ((placed u).directory_eq (placed ref) (keys u) bounds) (placed ref)
    bounds (owners u).2 (owners u).1⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
