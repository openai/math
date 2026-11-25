import OAI.Computability.BorderVNP.CubeRouteJointPacket
import OAI.Computability.BorderVNP.PackedSparseArgumentControls

/-! # All 37 signed-task control words in the actual published directory state

The real geometry output has 28 primary controls followed by nine sparse
argument controls. The reference-packet extension points to that output and
the directory reserves its compact demand stream below it.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM VerifierNetwork RoutingISA GeometryFrameEncoding ParseBatchSort
open Packing RoutingOutputs TeamContraction ProcessorSlots Diagonal.ExternalSew.FieldExport

variable {w d : ℕ}

/-- The native signed profile return retains the pointer encoded in its own reference
packet. The pointer addresses the same geometry controls as the literal circuit. -/
theorem BootResidence.selected_controlPointer (a : StartupArena) (u : Fin a.teams) (slot : ℕ)
    (packet : ReferencePacket w d) (task : SignedTaskArena.Layout) (old : Fin 81 → Word w)
    (D : Directory.Layout) (origin edges cells raw team subtotalWidth fresh profile gates outputs width off ell : ℕ)
    {F : Pins.ProcessorFields (a.operands u slot packet).layout} {f : BroadcastFrame} {A : AdviceLayout}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {bits : List Bool} {bank : Bank w}
    {initial after : Memory w} {k : ℕ} {g : Fin k → Bool}
    (path : BootResidence (F := F) a u slot packet f A pub mac bits initial bank g after)
    (base : (pub 0).val = a.frame)
    (selected : packet.extension = signedProfileExtension task old D origin edges cells raw team subtotalWidth
      fresh profile gates outputs width off ell)
    (fit : controlsBase origin edges cells D.entries (D.teams*D.sites) < 2^w) :
    readings after (a.frame+92) = controlsBase origin edges cells D.entries (D.teams*D.sites) := by
  obtain ⟨_,_,_,_,boot,resident⟩ := path
  have ext := (resident_frames a u slot packet (Pins.extendGuess g) base boot resident).2 (61 : Fin 81)
  rw [base,Nat.add_assoc,show 31+(61 : Fin 81).val = 92 by decide,selected] at ext
  exact (congrArg Fin.val ext).trans (signedProfileExtension_controlPointer task old D _ _ _ _ _ _ _ _ _ _ _ _ _ fit)

/-- The entire 37-word control vector lies before the cube header placed at the
end of the signed geometry allocation. The output arity is the true cable prefix,
directory columns, private markers, controls and the remaining geometry words. -/
theorem taskControls_before_header (fresh profile gates width wordSize edges cells entries live remaining : ℕ) :
    let outputs := edges*3+(RoutingOutputs.count edges cells entries live+
      ((cells+(entries+cells))+(28+(9+remaining))))
    let origin := GeometryAdvice.Allocation.dest fresh profile gates outputs width
    controlsBase origin edges cells entries live+37 ≤
      GeometryAdvice.Allocation.stop fresh profile gates outputs width wordSize := by
  intro outputs origin
  have used : controlsBase origin edges cells entries live+37+remaining = origin+outputs := by
    dsimp [outputs,controlsBase,bases,RoutingOutputs.count]
    omega
  unfold GeometryAdvice.Allocation.stop GeometryAdvice.Allocation.packed GeometryAdvice.Allocation.dense
  change _ ≤ origin+outputs+_+_
  omega

/-- A common control vector at all absolute positions from zero through 36. -/
noncomputable def allTaskControls (task : SignedTaskArena.Layout) (bits : ℕ)
    (fits : ∀ i : Fin 37, task.controls i.val < 2^bits) (i : Fin 37) : Fin (2^bits) :=
  ⟨task.controls i.val,fits i⟩

/-- The literal circuit emits the caller's full allocated task geometry. Both contiguous
parts survive demand publication. This includes the two cell-bank words, the four
bundle ordinal operands, the sparse report bases and the fragment directory controls. -/
theorem profile_published_taskControls {S Z : Type*} [Fintype S] [Fintype Z]
    {s edges n cells e k b o origin frame next gap : ℕ} {profile placed : Memory w}
    (D : Directory.Layout) (task : SignedTaskArena.Layout) (fits : ∀ i : Fin 37, task.controls i.val < 2^b)
    (F : CellAddressCircuit.Fields s edges n cells e k b (S ⊕ Bool)) (hk : k ≤ b)
    (old : Fin D.entries → Fin s) (ports : Fin (D.teams*D.sites) → Fin n)
    (rest : VerifierNetwork.Frame (S ⊕ Bool) (Outputs o b)) (source : VerifierNetwork.Frame Z S) (input : Z → Bool)
    (width : b ≤ w) (lower : frame+112 ≤ next) (room : next+7*D.candidates ≤ origin)
    (place : (privateLayout frame origin edges cells D.entries D.description gap).Image
      (readings profile) D.entries (readings placed))
    (pointer : readings profile (frame+92) = controlsBase origin edges cells D.entries (D.teams*D.sites)) :
    let c := allTaskControls task b fits
    let head := fun i : Fin 28 => c (i.castAdd 9)
    let tail := fun i : Fin 9 => c (Fin.natAdd 28 i)
    let t := bases origin edges cells D.entries
    let rows := D.directory (Directory.ISA.placement (readings placed) t.privatePairs)
      (Directory.ISA.placement (readings placed) t.livePairs)
    let mem := readings (Directory.ISA.publish placed frame next rows)
    let addr := controlsBase origin edges cells D.entries (D.teams*D.sites)
    (∀ i, readings profile (origin+i.val) = value (fun j =>
      (controlEmitter F hk old ports (withControls tail rest) source head).eval input (i,j))) →
      mem (frame+92) = addr ∧ ∀ i : Fin 37, mem (addr+i.val) = task.controls i.val := by
  intro c head tail t rows mem addr out
  obtain ⟨primary,extra,_⟩ := sparse_argument_controls F hk old ports rest source head tail input origin profile width out
  obtain ⟨ptr,_⟩ := directoryPublished_controls D _ _ (fun i => task.controls i.val) lower room place pointer primary
  refine ⟨ptr,?_⟩
  have len : 7*rows.length ≤ 7*D.candidates := Nat.mul_le_mul_left 7 (D.directory_length_le _ _)
  have keep (i : Fin 37) : mem (addr+i.val) = readings profile (addr+i.val) :=
    congrArg Fin.val (directoryPublished_control (live := D.teams*D.sites) rows place lower (by omega) i.val)
  intro i
  rw [keep i]
  refine Fin.addCases (m := 28) (n := 9) (motive := fun j => readings profile (addr+j.val) = task.controls j.val)
    (fun j => primary j) (fun j => ?_) i
  have e : readings profile (addr+28+j.val) = task.controls (28+j.val) := extra j
  simpa only [Fin.val_natAdd,Nat.add_assoc] using e

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
