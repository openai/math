import OAI.Computability.BorderVNP.FiniteEvaluatorSignedRouteInvalid
import OAI.Computability.BorderVNP.FiniteEvaluatorSignedLookupWriter
import OAI.Computability.BorderVNP.CubeRouteCompleteSchedule

/-! # Finite-field cube operands at the real public writer and transmission

The checked group schedule and its two directory images locate every live
scanner word. The data writer preserves those words and publishes its own
count. The same history retains the field lookup pointers from the signed
reference packet, even when its common rows have yet to be validated.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM RoutingISA BorderVNP.Cube BorderVNP.Cube.Physical DiagonalTallyPacketEmit

/-- Public declaration, scanner and signed field operands at the input of
one team's common row writer, indexed by its true data record count. -/
structure SharedCubeWords (task : SignedTaskArena.Layout) {R : ℕ}
    (decl : LengthDeclaration task.cube.n task.cube.header.d) (group : Fin task.cube.header.d → Fin (R+1))
    (team : ℕ) (pub : Arg → ℕ) (src : ℕ → ℕ) (dataCount : ℕ) : Prop where
  symbols : SymbolFrame (task.cube.sharedRows (pub 0) decl.1.val dataCount) src task.cube.header.blocks
    task.cube.K task.cube.h decl group
  scanner : task.cube.ScannerWords (pub 0) team decl.1.val (fun x => (group x).val) pub src decl.2
  lookup : ∀ visits, LookupPointers (task.lookupFrame visits) task.after.ids (pub 0) src
  fields : ∀ f, CubeConstants.Fields
    (CubeConstants.inArena f task.cube.stop task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s)
    (pub 0) (CubeConstants.idBase task.cube.stop task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s) src

end TeamContraction

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally TeamContraction DiagonalTallyPacketEmit
open LocalRow PackedHistoryCircuit Transmission
open private public_image_word from OAI.Computability.BorderVNP.CubeScatterWriterSources

variable {w R : ℕ} (task : SignedTaskArena.Layout) (old : Fin 81 → Word w) (D : Packing.Directory.Layout)
variable (origin edges cells raw team subtotal fresh profile gates outputs bits off ell : ℕ)
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {r t : Bank w} {m mt : Memory w}
variable {es : List (TeamRAM.Event w)} {frame : BroadcastFrame} {copy : List Bool} {pins : Pins.Layout}
variable {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)}
variable (decl : LengthDeclaration task.cube.n task.cube.header.d) (group : Fin task.cube.header.d → Fin (R+1))
local notation "width" => selectorWidth task.cube.n task.cube.K task.cube.h
local notation "ext" => signedProfileExtension task old D origin edges cells raw team subtotal fresh profile gates outputs bits off ell

/-- The true writer history on the signed packet supplies the scanner words,
the reference symbol frame, and all four field installer pointers on the
same intermediate memory just after the data records were emitted. -/
theorem WriterHistory.shared_cube_words (history : WriterHistory task.cube.n width pub mac r m es t mt)
    (emitted : ReturnedWriters task.cube D pp lp owner decl group pins history)
    (boot : BootPins pub frame ext copy m) (space : task.after.packed ≤ 2^w)
    (primary : (pub 0).val+112 ≤ task.cube.header.header) (axes : task.cube.header.a=task.cube.n+1)
    (controls who : ℕ) (input : ℕ → ℕ) {ticks : ℕ} {pass : Prop}
    (certificate : TestRun pub mac (.block (beforeWriters task.cube.n width)) r m ticks pass
      (fun z => WriterSources task.cube (pub 0).val controls who R decl group (readings pub) input (readings m) z.mem w)) :
    SharedCubeWords task decl group who (readings pub) (readings history.sharedInput) (D.directory pp lp).length := by
  have ready := emitted.emission.demand.ready
  have records := emitted.emission.demand.records
  have pointers f visits := history.signed_lookup_fields task old D origin edges cells raw team subtotal fresh profile gates
    outputs bits off ell f visits boot space primary controls R decl.1 input _ certificate ready records
  refine ⟨?_,?_,fun visits => (pointers (task.lookupFrame visits) visits).1,fun f => (pointers f 0).2⟩
  · rw [history.dataImage ready]
    exact emitted.emission.symbols
  · obtain ⟨scheduled,cellImage,scanner,cell,pair⟩ := ((certificate.sound history.prefixRun).2).2
    rw [history.dataImage ready]
    apply scanner.transfer axes primary
    intro addr low other
    exact public_image_word task.cube (readings scheduled) pub (task.cube.cellWriter (pub 0).val controls decl.1)
      (task.cube.pairWriter (pub 0).val) _ cellImage history.dataInput cell pair rfl rfl records addr low other

end RoutingISA.Evaluator

namespace TeamContraction.SharedCubeSource

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing BorderVNP.Cube BorderVNP.Cube.Physical
open FiniteEvaluator DiagonalTallyPacketEmit
open private deck_room from OAI.Computability.BorderVNP.FiniteEvaluatorSignedLookupPointers

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {delivery : ReturnedDelivery G pin ext wire D pp lp owner origin stride H pins} {F : Type*} [Fintype F]

/-- Assemble the source of the route inverse from the individual writer images,
the calibrated public transmission table and the single signed allocation. -/
noncomputable def ofWriterWords (task : SignedTaskArena.Layout) (decl : LengthDeclaration task.cube.n task.cube.header.d)
    (group : Fin task.cube.header.d → Fin (R+1)) (table : TableEntry task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s → F)
    (ids : task.id=CubeDeck.entry table) (src : Fin (R+1) → ℕ → ℕ) (anchor : Fin (R+1)) (frame dataCount : ℕ)
    (common : ∀ u, readings (H u).pub 0=frame)
    (tab : delivery.table=task.cube.table frame (dataCount+task.cube.header.d.choose 2))
    (room : ∀ u, task.cube.ReplayRoom w (readings (H u).pub 0))
    (wide : CubeDeck.minimumWidth F task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s ≤ w)
    (space : task.after.packed ≤ 2^w)
    (words : ∀ u, SharedCubeWords task decl group u.val (readings (H u).pub) (src u) dataCount) :
    SharedCubeSource delivery (task.cube.sharedRows frame decl.1.val dataCount) src task.cube decl group table := by
  have deck : CubeConstants.arenaEnd task.cube.stop task.id < 2^w := by
    simpa only [CubeConstants.arenaEnd,CubeConstants.ids,List.length_ofFn] using deck_room task space
  exact ⟨anchor,task.lookupFrame 0,dataCount+task.cube.header.d.choose 2,common anchor ▸ (words anchor).symbols,rfl,rfl,
    room,fun u => (common u).symm ▸ tab,fun u => (common u).symm,fun u => (words u).scanner,wide,
    ids ▸ deck,fun u => (words u).fields _⟩

end TeamContraction.SharedCubeSource

end BorderVNP
end Computability
end OAI
