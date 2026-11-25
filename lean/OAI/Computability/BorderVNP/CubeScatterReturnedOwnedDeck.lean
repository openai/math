import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedDirectory
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeBanksAllocation
import OAI.Computability.BorderVNP.CubeRouteWriterReadback

/-! # Genuine field-deck contents and allocated lookup pointers at the owned entry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator
open private detOfUnsigned from OAI.Computability.BorderVNP.CubeISALocalRowFrame

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
variable {group : Fin ar.header.d → Fin (R+1)} {T : TeamRows.Returns (Fin (R+1)) ar w}
variable {template : Frame} {count : ℕ} {F : Type*} [Fintype F]
variable (table : TableEntry ar.n ar.b ar.h ar.K ar.s → F)

/-- The actual natural-word installer in the route-to-owned handoff determines the fixed
lookup words, independently of the number of packet vertices on this team. -/
theorem OwnedHandoff.installed_words {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ}
    (handoff : OwnedHandoff f g src ar decl group template id count T)
    (u : Fin (R+1)) (lookupFrame : Frame) :
    CubeDeck.WordsAt lookupFrame ar.stop id (readings (T.input u)) := by
  let layout := CubeConstants.inArena template ar.stop ar.n ar.b ar.h ar.K ar.s
  let base := CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s
  let hist := H u
  obtain ⟨_,installed⟩ := handoff.install u
  have test := CubeConstants.install_run hist.pub hist.macros hist.history.val.2.1 hist.history.val.2.2
    layout base id (handoff.fits u) (handoff.fields u)
  have det := detOfUnsigned _ (CubeConstants.install_unsigned id).1
  have image := ((test.asTest det).sound installed).2
  have values := CubeConstants.image_values layout id (readings hist.history.val.2.2) (handoff.fits u) rfl rfl
  have deck : CubeDeck.WordsAt template ar.stop id (readings (T.input u)) := by
    change readings (T.input u) = CubeConstants.image layout base id (readings hist.history.val.2.2) at image
    rw [image]; exact ⟨values.1,values.2.1,values.2.2.1,values.2.2.2⟩
  exact CubeDeck.WordsAt.preserve template ar.stop id deck lookupFrame (fun _ _ _ => rfl)

/-- Read back the finite field framing from its actual native initializer. -/
theorem OwnedHandoff.installed_deck
    (handoff : OwnedHandoff f g src ar decl group template (CubeDeck.entry table) count T)
    (u : Fin (R+1)) (lookupFrame : Frame) :
    CubeDeck.At table lookupFrame ar.stop (readings (T.input u)) := handoff.installed_words u lookupFrame

omit [Fintype F] in
/-- Transfer a physical primary frame word through the shared writer, real transmission,
and native constant installation. The emitter publishes its count at slot thirteen. -/
theorem SharedWriters.owned_input_word (writer : SharedWriters f g src) {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ}
    (handoff : OwnedHandoff f g src ar decl group template id count T) (u : Fin (R+1))
    (j : ℕ) (bounded : j < 112) (separate : j ≠ 13) :
    readings (T.input u) (readings (T.pub u) 0+j) = src u (readings (T.pub u) 0+j) := by
  rw [handoff.pub]
  let frame := readings (H u).pub 0
  have before : frame+j < ar.header.header := (Nat.add_lt_add_left bounded frame).trans_le (handoff.room u).primary
  obtain ⟨_,install⟩ := handoff.install u
  let l := ar.scanner frame u.val decl.1.val ar.rowSelectorBits
  have cell : frame+j ∈ TeamRowSources.source l ar.powerBase ar.n :=
    TeamRowSources.primary (l := l) bounded
  have installed := TeamHistory.install_scanner_source (H u) ar u.val decl.1.val ar.rowSelectorBits template id
    (handoff.room u).primary (handoff.room u).axes (handoff.fits u) (handoff.fields u) install _ cell
  have old := writer.returned_static ar frame count (handoff.table u) u (frame+j)
    (before.trans_le (Evaluator.secondary_le_records ar)) (by rw [handoff.frame]; exact Nat.add_left_cancel.mt separate)
  exact (congrArg Fin.val installed).trans old

/-- Five scalar lookups determined by the allocation of the task and operand arrays.
The pointer to the actual owned triples and the four installed deck pointers are
provided separately by the returned route and the native constant initializer. -/
structure LookupPointers (frame : Frame) (dst base : ℕ) (m : ℕ → ℕ) : Prop where
  descriptors : m (base+45) = frame.descriptors
  destination : m (base+71) = dst
  references : m (base+80) = frame.refs
  width : m (base+83) = frame.width
  vertices : m (base+84) = frame.vertices

/-- The actual constant installer and real sender metadata provide all boot conditions
for reading the recovered field cube in the owned scanner's memory. -/
theorem SharedWriters.owned_word_boot {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} (writer : SharedWriters f g src)
    (handoff : OwnedHandoff f g src ar decl group template id count T)
    (u : Fin (R+1)) (frame : Frame) (dst : ℕ)
    (triples : frame.triples = ar.vertexBase) (recipe : frame.recipes = ar.stop+2)
    (zero : frame.zeroAddr = ar.stop) (one : frame.oneAddr = ar.stop+1) :
    let pub := T.pub u
    let mem := T.input u
    LookupPointers frame dst (readings pub 0) (src u) →
      CubeDeck.WordsAt frame ar.stop id (readings mem) ∧
      Frame.resident {frame with count := readings mem (readings pub 0+46)} (readings pub) (readings mem) ∧
      readings mem (readings pub 0+47) = CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s ∧
      readings mem (readings pub 0+71) = dst := by
  intro pub mem ptr
  have got (j : ℕ) (bound : j < 112) (other : j ≠ 13) := writer.owned_input_word handoff u j bound other
  let hist := H u
  let fr := readings hist.pub 0
  obtain ⟨_,install⟩ := handoff.install u
  have prev (j : ℕ) (bound : j < 112) : readings mem (readings pub 0+j) = readings hist.history.val.2.2 (fr+j) := by
    have cell : fr+j ∈ TeamRowSources.source (ar.scanner fr u.val decl.1.val ar.rowSelectorBits) ar.powerBase ar.n :=
      TeamRowSources.primary (l := ar.scanner fr u.val decl.1.val ar.rowSelectorBits) bound
    have preserved := TeamHistory.install_scanner_source hist ar u.val decl.1.val ar.rowSelectorBits template id
      (handoff.room u).primary (handoff.room u).axes (handoff.fits u) (handoff.fields u) install _ cell
    dsimp only [pub]; rw [handoff.pub]; exact congrArg Fin.val preserved
  obtain ⟨z,o,rec,ids⟩ := handoff.fields u
  have vertex : src u (readings pub 0+78) = ar.vertexBase := by
    dsimp only [pub]; rw [handoff.pub]; exact (handoff.source u).triples
  exact ⟨handoff.installed_words u frame,⟨rfl,(got 78 (by decide) (by decide)).trans (vertex.trans triples.symm),
    (prev 79 (by decide)).trans (rec.trans recipe.symm),(got 80 (by decide) (by decide)).trans ptr.references,
    (got 45 (by decide) (by decide)).trans ptr.descriptors,(prev 81 (by decide)).trans (z.trans zero.symm),
    (prev 82 (by decide)).trans (o.trans one.symm),(got 83 (by decide) (by decide)).trans ptr.width,
    (got 84 (by decide) (by decide)).trans ptr.vertices⟩,(prev 47 (by decide)).trans ids,
    (got 71 (by decide) (by decide)).trans ptr.destination⟩

/-- Physical lookup pointers and deck for the field-framed specialization. -/
theorem SharedWriters.owned_lookup_boot (writer : SharedWriters f g src)
    (handoff : OwnedHandoff f g src ar decl group template (CubeDeck.entry table) count T)
    (u : Fin (R+1)) (frame : Frame) (dst : ℕ)
    (triples : frame.triples = ar.vertexBase) (recipe : frame.recipes = ar.stop+2)
    (zero : frame.zeroAddr = ar.stop) (one : frame.oneAddr = ar.stop+1) :
    let pub := T.pub u
    let mem := T.input u
    LookupPointers frame dst (readings pub 0) (src u) →
      CubeDeck.At table frame ar.stop (readings mem) ∧
      Frame.resident {frame with count := readings mem (readings pub 0+46)} (readings pub) (readings mem) ∧
      readings mem (readings pub 0+47) = CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s ∧
      readings mem (readings pub 0+71) = dst :=
  writer.owned_word_boot handoff u frame dst triples recipe zero one

end TeamContraction

end BorderVNP
end Computability
end OAI
