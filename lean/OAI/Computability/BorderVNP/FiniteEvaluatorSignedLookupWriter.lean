import OAI.Computability.BorderVNP.CubeRouteJointPacket
import OAI.Computability.BorderVNP.CubeRoutePinnedEntry
import OAI.Computability.BorderVNP.FiniteEvaluatorSignedLookupPointers

/-! # Signed field lookup operands at the actual routing writer

The chosen joint reference spells the signed task arena's five field lookup
words and four fixed table pointers. The verified nine-stage public prefix
retains these low frame cells. The data compiler then writes the descriptor
rows and publishes their count, giving the pointer words on the actual input
of the shared writer and at the returned transmission.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally PackedHistoryCircuit
open LocalRow TeamContraction DiagonalTallyPacketEmit Transmission

variable {w width : ℕ} (task : SignedTaskArena.Layout) (old : Fin 81 → Word w)
variable (D : Packing.Directory.Layout) (origin edges cells raw team subtotal fresh profile gates outputs bits off ell : ℕ)
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {f : BroadcastFrame} {copy : List Bool}
variable {r t : Bank w} {m mt : Memory w} {es : List (TeamRAM.Event w)}
local notation "ext" => signedProfileExtension task old D origin edges cells raw team subtotal fresh profile gates outputs bits off ell
local notation "boot" => ExtendedFrame.installed m (Fin.val (pub 0)) (task.extension raw team subtotal old)
local notation "idBase" => CubeConstants.idBase task.cube.stop task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s

private theorem joint_operand (pins : BootPins pub f ext copy m)
    (j : ℕ) (field : j ∈ [45,71,80,83,84,47,79,81,82]) :
    readings m ((pub 0).val+j) = readings boot ((pub 0).val+j) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at field
  have fit : j-31 < 81 := by omega
  let i : Fin 81 := ⟨j-31,fit⟩
  have place : (pub 0).val+31+i.val=(pub 0).val+j := by dsimp [i]; omega
  have actual := (pins.extension i).trans (signedProfileExtension_lookupWord task old D origin edges cells raw team subtotal
    fresh profile gates outputs bits off ell i (by dsimp only [i]; simp only [List.mem_cons,List.not_mem_nil,or_false]; omega))
  exact congrArg Fin.val (place ▸ actual.trans (ExtendedFrame.installed_at m (pub 0).val _ i).symm)

variable (H : WriterHistory task.cube.n width pub mac r m es t mt)

/-- The primary frame words at the true shared writer entry equal those in the
original signed packet. The prefix certificate is checked on this history's
actual prefix, followed by its real data descriptor writer. -/
theorem WriterHistory.signed_lookup_fields (template : Frame) (visits : ℕ)
    (pins : BootPins pub f ext copy m) (room : task.after.packed ≤ 2^w)
    (primary : (pub 0).val+112 ≤ task.cube.header.header)
    (controls R : ℕ) (axis : Fin (task.cube.n+1)) (input : ℕ → ℕ) (P : (ℕ → ℕ) → Prop)
    {ticks : ℕ} {ok : Prop} (cert : TestRun pub mac (.block (beforeWriters task.cube.n width)) r m ticks ok
      (fun z => NativeEntry task.cube (pub 0).val controls axis R input (readings m) z.mem ∧ P z.mem))
    (ready : DataReady pub H.dataInput)
    (records : (DataWriter.layout (readings pub) (readings H.dataInput)).output=task.cube.records) :
    LookupPointers (task.lookupFrame visits) task.after.ids (pub 0).val (readings H.sharedInput) ∧
      CubeConstants.Fields (CubeConstants.inArena template task.cube.stop task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s)
        (pub 0).val idBase (readings H.sharedInput) := by
  have native := (cert.sound H.prefixRun).2.1
  have before (j : ℕ) (field : j ∈ [45,71,80,83,84,47,79,81,82]) :
      readings H.sharedInput ((pub 0).val+j)=readings boot ((pub 0).val+j) := by
    have bounds : j<112 ∧ j≠13 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at field
      omega
    have low := (Nat.add_lt_add_left bounds.1 (pub 0).val).trans_le primary
    have keep : H.sharedInput ((pub 0).val+j)=H.dataInput ((pub 0).val+j) := by
      rw [H.dataImage ready,DataWriter.publish,Function.update_of_ne (Nat.add_left_cancel.mt bounds.2),
        Packing.Directory.ISA.putWords_outside _ _ _ _ (Or.inl (records ▸ low.trans_le (secondary_le_records task.cube)))]
    exact (congrArg Fin.val keep).trans ((native.low _ low).trans
      (joint_operand task old D origin edges cells raw team subtotal fresh profile gates outputs bits off ell pins j field))
  have lookup := task.lookupPointers_at_boot visits (pub 0).val raw team subtotal m old room
  obtain ⟨zero,one,rec,ids⟩ := task.constantFields_at_boot template (pub 0).val raw team subtotal m old room
  refine ⟨lookup.transfer (fun j hj => before j ?_), (before 81 (by decide)).trans zero,(before 82 (by decide)).trans one,
    (before 79 (by decide)).trans rec,(before 47 (by decide)).trans ids⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj ⊢
  tauto

end RoutingISA.Evaluator

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube DiagonalTallyPacketEmit

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext wire D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ}

/-- The shared writer and returned transmission retain the actual four signed
table pointers in the memory where the native installer starts. -/
theorem SharedWriters.returned_constant_fields (writer : SharedWriters f g src) (a : CubeArena.Layout)
    (frame count : ℕ) (tab : f.table = a.table frame count) (primary : frame+112 ≤ a.header.header)
    (fr : g.frame = frame) (template : Frame) (idBase : ℕ) (u : Fin (R+1))
    (fields : CubeConstants.Fields template frame idBase (src u)) :
    CubeConstants.Fields template frame idBase (readings (H u).history.val.2.2) := by
  have keep (j : ℕ) (lo : j<112) (diff : j≠13) := writer.returned_static a frame count tab u (frame+j)
    (((Nat.add_lt_add_left lo frame).trans_le primary).trans_le (Evaluator.secondary_le_records a))
    (by rw [fr]; exact Nat.add_left_cancel.mt diff)
  exact ⟨(keep 81 (by decide) (by decide)).trans fields.1,(keep 82 (by decide) (by decide)).trans fields.2.1,
    (keep 79 (by decide) (by decide)).trans fields.2.2.1,(keep 47 (by decide) (by decide)).trans fields.2.2.2⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
