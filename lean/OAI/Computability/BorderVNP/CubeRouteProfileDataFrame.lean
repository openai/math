import OAI.Computability.BorderVNP.CubeRouteProfileInputs
import OAI.Computability.BorderVNP.CubeRoutePinnedFrame
import OAI.Computability.BorderVNP.CubeISAHeaderInstallExtension
import OAI.Computability.BorderVNP.PackedRoutingDemandHeader

/-! # Actual scalar operands at private placement and demand publication

The pin layout, raw-delivery base and scheduler-record pointer arrive through
the ordinary public bank. The cell directory arrives through the selected
extended packet. Private placement writes above the complete boot frame.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open Packing Packing.RoutingOutputs DiagonalResidueRAM GeometryAdvice CubeHeaderInstall

variable {w d : ℕ}

/-- The demand writer uses public argument nine while the routing table occupies
other arguments. The same public bank can therefore be used for both pinned-frame
theorems, in either allocation order. -/
theorem routeBank_withDemandBase (task : SignedTaskArena.Layout) (frame base : ℕ) (other : Arg → Word w) :
    task.routeBank frame (withDemandBase other base) = withDemandBase (task.routeBank frame other) base := by
  funext j
  by_cases same : j = 9
  · subst j
    change withDemandBase other base 9 = withDemandBase (task.routeBank frame other) base 9
    simp [withDemandBase]
  · simp [SignedTaskArena.Layout.routeBank,withDemandBase,Function.update_of_ne same]

/-- Slot 72 is the host-directory pointer in the genuine joint geometry and cube
extension. Both overlay stages leave its cube-arena operand in place. -/
theorem joint_hostWord (ar : CubeArena.Layout) (old : Fin 81 → Word w)
    (fresh profile gates outputs width off ell : ℕ) (fit : ar.hostDirectory < 2^w) :
    (jointFields (ar.extension old) fresh profile gates outputs width off ell ar.header.d ar.n
      ar.header.blocks ar.b ar.h ar.s (41 : Fin 81)).val = ar.hostDirectory := by
  unfold jointFields
  rw [Allocation.fields_other _ _ _ _ _ _ _ _ 41 (by decide),
    pinFields_other _ _ _ _ _ _ _ _ 41 (by decide)]
  change (TeamTapeInputEmit.word w ar.hostDirectory).val = ar.hostDirectory
  exact Nat.mod_eq_of_lt fit

/-- The signed tally allocator also forwards this cube operand in its reference
extension. Both stored unsigned words represent the same physical address. -/
theorem signed_hostWord (task : SignedTaskArena.Layout) (old : Fin 81 → Word w)
    (raw team subtotalWidth : ℕ) (fit : task.cube.hostDirectory < 2^w) :
    (task.extension raw team subtotalWidth old (41 : Fin 81)).val = task.cube.hostDirectory := by
  change (TeamTapeInputEmit.word w ((TeamTapeInputEmit.word w task.cube.hostDirectory).val)).val = _
  exact (Nat.mod_eq_of_lt (Fin.isLt _)).trans (Nat.mod_eq_of_lt fit)

/-- The pack-history routing, private-directory and geometry overlays preserve the
underlying host word in the literal selected by the signed startup. -/
theorem routed_hostWord (old : Fin 81 → Word w) (D : Directory.Layout)
    (origin edges cells live fresh reserve gates outputs width off ell : ℕ) :
    Allocation.fields (controlsExtension (directoryFields old D) origin edges cells D.entries live)
      fresh reserve gates outputs width off ell (41 : Fin 81) = old 41 := by
  rw [Allocation.fields_other _ _ _ _ _ _ _ _ 41 (by decide),
    controlsExtension_other _ _ _ _ _ _ 41 (by decide),extension_other _ _ _ _ _ 41 (by decide)]
  rfl

/-- The four data compiler inputs at the returned private-slot memory. The selected
substitution and broadcast have already run. Their writes cannot change the ordinary
pin fields or the three physical directory pointers. -/
theorem slotted_dataFrame (task : SignedTaskArena.Layout) (start : StartupArena)
    (team : Fin start.teams) (slot : ℕ) (packet : ReferencePacket w d) (other : Arg → Word w)
    (origin edges cells entries desc gap : ℕ) {f : BroadcastFrame} {A : AdviceLayout} {bits : List Bool}
    {z : Bank w} {saved profile slotted : Memory w} (guess : ℕ → Bool)
    (room : start.next ≤ origin) (nextFit : start.next < 2^w) (outFit : task.cube.records < 2^w)
    (host : (packet.extension (41 : Fin 81)).val = task.cube.hostDirectory) :
    let B := start.operands team slot packet
    let args := core (withDemandBase (task.routeBank start.frame other) start.next) origin edges cells
    let pub := B.bank args
    B.Fits w → ∀ {F : Pins.ProcessorFields B.layout},
      JointHeader.BootHeaderState F f A packet pub bits z saved →
      (∀ j < start.next, profile j = Pins.preparedMemory B.layout guess saved B.layout.count j) →
      (privateLayout start.frame origin edges cells entries desc gap).Image (readings profile) entries (readings slotted) →
      Pins.Frame B.layout (readings pub) (readings slotted) ∧
      readings slotted (start.frame+8) = start.next ∧ readings slotted (start.frame+12) = task.cube.records ∧
      readings slotted (start.frame+72) = task.cube.hostDirectory := by
  intro B args pub fit F boot resident place
  have base : (pub 0).val = start.frame := B.frameBase_word args fit
  obtain ⟨ordinary,extended⟩ := resident_frames start team slot packet guess base boot resident
  have low := (routeInput_room start team slot packet F).2.1
  have kept (k : ℕ) (hk : k < 112) : slotted (start.frame+k) = profile (start.frame+k) :=
    Fin.ext (private_before_ends place _ (by dsimp [bases]; omega))
  have written (i : Fin 31) : slotted ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1)) := by
    have h := kept i.val (by have := i.isLt; omega)
    rw [← base] at h
    exact h.trans (ordinary i)
  have frameEq (i : ℕ) (hi : i < 31) :
      frameField (readings pub) (readings slotted) i = frameField (readings pub) (readings saved) i :=
    congrArg Fin.val ((written ⟨i,hi⟩).trans (boot.core ⟨i,hi⟩).symm)
  have field8 := written 8
  have field12 := written 12
  have field72 := extended (41 : Fin 81)
  rw [base] at field8 field12 field72
  refine ⟨(boot.frame.congr frameEq).pins,?_,?_,?_⟩
  · refine (congrArg Fin.val field8).trans ?_
    change (B.bank args 9).val = start.next
    rw [B.bank_passthrough args 9 (by decide) (by decide)]
    change (withDemandBase _ start.next 9).val = start.next
    rw [withDemandBase,Function.update_self,word_val _ _ nextFit]
  · refine (congrArg Fin.val field12).trans ?_
    change (B.bank args 13).val = task.cube.records
    rw [B.bank_passthrough args 13 (by decide) (by decide)]
    change (withDemandBase (task.routeBank start.frame other) start.next 13).val = _
    rw [withDemandBase,Function.update_of_ne (by decide : (13 : Arg) ≠ 9)]
    exact Nat.mod_eq_of_lt outFit
  · have h : profile (start.frame+72) = packet.extension 41 := by simpa only [Nat.add_assoc,show 31+(41 : Fin 81).val = 72 by decide] using field72
    exact (congrArg Fin.val ((kept 72 (by decide)).trans h)).trans host

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
