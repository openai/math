import OAI.Computability.BorderVNP.FiniteProfilePublication
import OAI.Computability.BorderVNP.CubeRouteEmitterInputs

/-! # Slotted writer operands on the true finite-field processor's prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open PackedHistoryCircuit Packing RoutingOutputs

private theorem pin_frame_of_core {w : ℕ} (B : PacketOperands) (other : Arg → Word w)
    (m : Memory w) (fitted : B.Fits w)
    (read : ∀ j : Fin 31, m (((B.bank other) 0).val+j.val)=(B.bank other) (Fin.ofNat 32 (j.val+1))) :
    Pins.Frame B.layout (readings (B.bank other)) (readings m) := by
  let pub := B.bank other
  have atWord (j : ℕ) (hj : j<31) : frameField (readings pub) (readings m) j = frameField
      (fun _ => 0) (operand pub) j := by
    simpa only [frameField,readings,operand,Nat.zero_add,pub] using congrArg Fin.val (read ⟨j,hj⟩)
  have p := (B.packetFrame other fitted).pins
  exact ⟨(atWord 0 (by decide)).trans p.team,(atWord 1 (by decide)).trans p.teams,
    (atWord 2 (by decide)).trans p.processors,(atWord 3 (by decide)).trans p.literal,
    (atWord 4 (by decide)).trans p.link,(atWord 21 (by decide)).trans p.ibase,
    (atWord 22 (by decide)).trans p.hbase,(atWord 23 (by decide)).trans p.width,
    (atWord 24 (by decide)).trans p.starbase⟩

variable {R r lit link inner n w o nt ng : ℕ} {Edge : Type} {Q Γ : Type} {K : Type*} [Field K]
variable (G : Wiring R r lit 0 link inner n Edge) (L : Routing.WireLayout (R+1) r link) (u : Fin (R+1))
variable (ext : Exterior R r link → Bool) (bank : Bank w)
variable (lib : Fin 8 → TeamSite.Macro Q Γ nt ng) (ret : FieldProcessor.Returns Q Γ K nt 8) (fuel : ℕ)

set_option maxRecDepth 5000 in
/-- Read the actual pin frame, five native schedule pointers and three writer
pointers on the intermediate private-placement memory of any finite exterior.
Only the immutable scalar choices are common between different exteriors. -/
theorem FrontReceipt.slotted_frame (task : SignedTaskArena.Layout) (D : Directory.Layout)
    (other : Arg → Word w) (extra : Fin 81 → Word w) (start pinClock fresh origin gap : ℕ)
    (headerBits : List Bool) (words : Fin o → ℕ) :
    let A := ProfileArena.arena G L ([] : List (Word w))
    let B := ProfileArena.operands G L ([] : List (Word w)) extra Fin.elim0 start u
    let params := core (withDemandBase (task.routeBank A.frame other) A.next) origin task.cube.cables task.cube.cells
    let pub := B.bank params
    let fields := G.processorFields u Fin.elim0 ext A.ibase A.hbase A.dense
    let pl := privateLayout A.frame origin task.cube.cables task.cube.cells D.entries D.description gap
    B.Fits w → A.next ≤ fresh → A.next ≤ origin → A.next < 2^w → task.cube.stop < 2^w →
    (extra 41).val=task.cube.hostDirectory →
    ∀ (z : Returns profileFront pub (TeamSiteEvents.macros lib fuel) bank (processorMemory fields w)),
      FrontReceipt G u ext A.ibase A.hbase A.dense L.header A.broadcastBase pub bank lib ret fuel z A.copied extra
        headerBits pinClock fresh origin words →
      ∀ placed : Memory w, pl.Image (readings z.val.2.2) D.entries (readings placed) →
      Pins.Frame B.layout (readings pub) (readings placed) ∧
      (∀ count, TablePointers (task.cube.table A.frame count) (readings placed)) ∧
      readings placed ((pub 0).val+8)=A.next ∧ readings placed ((pub 0).val+12)=task.cube.records ∧
      readings placed ((pub 0).val+72)=task.cube.hostDirectory := by
  intro A B params pub fields pl fitted freshLo originLo nextFit cubeFit host z receipt placed place
  have frame : (pub 0).val=A.frame := B.frameBase_word _ fitted
  have broadcast : A.frame+112 ≤ A.broadcastBase := by change A.frame+112 ≤ A.frame+112+A.copied; omega
  have lo : A.broadcastBase+L.header=A.ibase := rfl
  have endLo : A.ibase+A.count ≤ A.next := by change A.ibase+A.count ≤ A.ibase+A.count+A.count; omega
  have high : A.ibase ≤ A.hbase := Nat.le_add_right ..
  obtain ⟨_,hw,he⟩ := receipt.route_sources G u ext A.ibase A.hbase A.dense L.header A.broadcastBase pub bank
    lib ret fuel (frame ▸ broadcast) (by omega) (by omega) (endLo.trans freshLo)
  have low (j : ℕ) (hj : j<112) : placed ((pub 0).val+j) = z.val.2.2 ((pub 0).val+j) := by
    apply Fin.ext
    apply private_before_ends place
    dsimp only [bases]; omega
  have ordinary (j : Fin 31) := (low j.val (by have := j.isLt; omega)).trans (hw j)
  have pointers (c : ℕ) : TablePointers (task.cube.table A.frame c) (readings placed) := by
    apply pinnedTablePointers task B A.frame c other origin task.cube.cables task.cube.cells placed cubeFit
    intro i hi
    have lt : i<31 := by simp at hi; omega
    have raw := ordinary ⟨i,lt⟩
    rw [frame] at raw
    convert raw using 1
    simp at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> rfl
  have raw : (pub 9).val=A.next := Nat.mod_eq_of_lt nextFit
  have rawAt := congrArg Fin.val (ordinary (8 : Fin 31))
  have hostAt := congrArg Fin.val (he (41 : Fin 81))
  change (z.val.2.2 ((pub 0).val+31+41)).val=(extra 41).val at hostAt
  refine ⟨pin_frame_of_core B params placed fitted ordinary,pointers,rawAt.trans raw,?_,?_⟩
  · rw [frame]; exact (pointers 0).records
  · exact (congrArg Fin.val (low 72 (by decide))).trans (by rw [←host]; exact hostAt)

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
