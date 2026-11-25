import OAI.Computability.BorderVNP.PackedHistoryRoutingFrame
import OAI.Computability.BorderVNP.PackedHistoryGeometryExecute
import OAI.Computability.BorderVNP.PackedRoutingChooserHeader
import OAI.Computability.BorderVNP.PackedCableColumns
import OAI.Computability.BorderVNP.TransmissionReceivedFields

/-! # Physical routing sources on the chosen profile return

The signed startup initializes the processor words, substitution bank and
broadcast operands. These three source regions lie below the true geometry
scratch and delivery directory. The private placement and publication stages
preserve them while writing the compact delivery count in field nine.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA TeamContraction ProcessorSlots Packing
open private PinClear.read from OAI.Computability.BorderVNP.PackedHistoryPreparedInput

variable {w d : ℕ} {P : Pins.Layout}

/-- Physical inputs for one team at the routing scheduler entry. -/
structure ProfileRouteInputs (F : Pins.ProcessorFields P) (f : BroadcastFrame)
    (pub : Arg → Word w) (guess : ℕ → Bool) (m : Memory w) : Prop where
  physical : F.ContainsInput m
  substituted : Pins.SubstitutionAt P guess m
  broadcast : f.At (readings pub) (readings m)

variable {f : BroadcastFrame} {pub : Arg → Word w} {guess : ℕ → Bool} {m after : Memory w}

/-- Agreement on the original input, frozen index and seven broadcast words suffices
to transfer the actual routing sources, independently of the other frame fields. -/
theorem ProfileRouteInputs.congr {F : Pins.ProcessorFields P} (src : ProfileRouteInputs F f pub guess m)
    (input : ∀ a < F.header.length, after a = m a)
    (pins : ∀ j < P.count, after (P.ibase+j) = m (P.ibase+j))
    (frame : ∀ k ∈ [0,1,2,3,4,5,25], after ((pub 0).val+k) = m ((pub 0).val+k)) :
    ProfileRouteInputs F f pub guess after := by
  refine ⟨fun a ha => (input a ha).trans (src.physical a ha),fun j hj => (pins j hj).trans (src.substituted j hj),?_⟩
  have eq (k : ℕ) (hk : k ∈ [0,1,2,3,4,5,25]) :
      frameField (readings pub) (readings after) k = frameField (readings pub) (readings m) k :=
    congrArg Fin.val (frame k hk)
  simpa only [BroadcastFrame.At,eq 0 (by decide),eq 1 (by decide),eq 2 (by decide),
    eq 3 (by decide),eq 4 (by decide),eq 5 (by decide),eq 25 (by decide)] using src.broadcast

/-- A prepared native memory retains the original input and seven broadcast operands
and has exactly the selected pin array. This form applies also to a finite profile
startup that reads the broadcast without installing a reference packet. -/
theorem profileRouteInputs_of_prepared {F : Pins.ProcessorFields P} {fresh : ℕ}
    (input : F.ContainsInput m) (frame : f.At (readings pub) (readings m)) (sep : Pins.Separated P)
    (inputClear : PinClear P 0 F.header.length) (frameClear : PinClear P (pub 0).val 112)
    (tapeRoom : F.header.length ≤ fresh) (frameRoom : (pub 0).val+112 ≤ fresh)
    (pinRoom : P.ibase+P.count ≤ fresh)
    (resident : ∀ j < fresh, after j = Pins.preparedMemory P guess m P.count j) :
    ProfileRouteInputs F f pub guess after := by
  refine ⟨?_,?_,?_⟩
  · intro x hx
    have keep := PinClear.read inputClear guess m x hx
    rw [Nat.zero_add] at keep
    exact (resident x (hx.trans_le tapeRoom)).trans (keep.trans (input x hx))
  · intro j hj
    exact (resident _ (by omega)).trans (Pins.preparedMemory_substitute P guess m sep le_rfl hj)
  · have keep (k : ℕ) (hk : k < 112) :
        frameField (readings pub) (readings after) k = frameField (readings pub) (readings m) k :=
      congrArg Fin.val ((resident ((pub 0).val+k) (by omega)).trans (PinClear.read frameClear guess m k hk))
    simpa only [BroadcastFrame.At,keep 0 (by decide),keep 1 (by decide),keep 2 (by decide),
      keep 3 (by decide),keep 4 (by decide),keep 5 (by decide),keep 25 (by decide)] using frame

variable (a : StartupArena) (team : Fin a.teams) (slot : ℕ) (packet : ReferencePacket w d)
local notation "L" => PacketOperands.layout (a.operands team slot packet)

/-- The original processor tapes end exactly at the boot frame, and the entire
substitution bank and 112-word frame precede the first available scratch word. -/
theorem routeInput_room (F : Pins.ProcessorFields L) :
    F.header.length = a.frame ∧ a.frame+112 ≤ a.next ∧
      a.frame+112 ≤ (L).ibase ∧ (L).ibase+(L).count ≤ a.next := by
  have stride : (L).stride = a.stride := by
    change a.literal+(a.teams-1)*a.link+a.literal = 2*a.literal+(a.teams-1)*a.link
    omega
  refine ⟨by rw [F.header_length,stride]; rfl,?_⟩
  change a.frame+112 ≤ a.frame+112+a.copied+a.header+a.count+a.count ∧
    a.frame+112 ≤ a.frame+112+a.copied+a.header ∧
    a.ibase+a.count ≤ a.ibase+a.count+a.count
  omega

private theorem pinSeparated : Pins.Separated L := by
  have stride : (L).stride = a.stride := by
    change a.literal+(a.teams-1)*a.link+a.literal = 2*a.literal+(a.teams-1)*a.link
    omega
  apply Pins.Separated.of_intervals
  · rw [stride]
    change a.frame ≤ a.frame+112+a.copied+a.header
    omega
  · rw [stride]
    change a.frame ≤ a.frame+112+a.copied+a.header+a.count
    omega
  · exact .inl le_rfl

variable {F : Pins.ProcessorFields (a.operands team slot packet).layout}
variable {A : AdviceLayout} {bits : List Bool} {z : Bank w} {saved : Memory w}

/-- At any true geometry return, the signed boot and concrete prepared-memory
residence recover all three routing inputs for exactly that path's pin choices. -/
theorem profileRouteInputs_of_boot (base : (pub 0).val = a.frame)
    (boot : JointHeader.BootHeaderState F f A packet pub bits z saved)
    (resident : ∀ j < a.next, after j = Pins.preparedMemory L guess saved (L).count j) :
    ProfileRouteInputs F f pub guess after := by
  obtain ⟨input,fr,_,last⟩ := routeInput_room a team slot packet F
  have clear := arena_pin_clear a team slot packet
  exact profileRouteInputs_of_prepared boot.input boot.frame.broadcast (pinSeparated a team slot packet)
    (F.header_length ▸ clear.1) (base ▸ clear.2.1) (by omega) (base ▸ fr) last resident

/-- The low-memory part of the actual chosen-profile path certificate contains its
boot return and its own native substitution choices. -/
theorem BootResidence.routeInputs {k : ℕ} {mac : TeamOpcode.Macros w 8} {bank : Bank w}
    {initial : Memory w} {g : Fin k → Bool} (base : (pub 0).val = a.frame)
    (path : BootResidence (F := F) a team slot packet f A pub mac bits initial bank g after) :
    ProfileRouteInputs F f pub (Pins.extendGuess g) after := by
  obtain ⟨_,_,_,_,boot,resident⟩ := path
  exact profileRouteInputs_of_boot a team slot packet base boot resident

/-- The actual geometry interpreter supplies residence directly from its protected
prefix when run on the memory returned by native pin preparation. -/
theorem GeometryReturn.routeInputs {o fresh dest clock : ℕ} {output : Fin o → ℕ}
    {mac : TeamOpcode.Macros w 8} {s t : Bank w} {trace : List (TeamRAM.Event w)}
    (base : (pub 0).val = a.frame) (boot : JointHeader.BootHeaderState F f A packet pub bits z saved)
    (geo : GeometryReturn pub mac s (Pins.preparedMemory L guess saved (L).count) fresh dest clock output trace t after)
    (lower : a.next ≤ fresh) : ProfileRouteInputs F f pub guess after :=
  profileRouteInputs_of_boot a team slot packet base boot fun j hj => geo.preserved j (hj.trans_le lower)

/-- After the real private placement and directory publication, every word below
the first delivery record survives except the field where publication stores the count. -/
theorem directoryPublished_low {frame origin edges cells entries desc gap next : ℕ}
    {before placed : Memory w} (rows : List Directory.Row)
    (place : (RoutingOutputs.privateLayout frame origin edges cells entries desc gap).Image
      (readings before) entries (readings placed)) (room : next ≤ origin)
    (x : ℕ) (hx : x < next) (other : x ≠ frame+9) :
    Directory.ISA.publish placed frame next rows x = before x := by
  rw [CableTriples.published_outside placed frame next rows x other (Or.inl hx)]
  apply Fin.ext
  exact RoutingOutputs.private_before_ends place x (by dsimp [RoutingOutputs.bases]; omega)

/-- All physical source predicates hold on the memory from which the native
public group schedule starts. The delivery rows may have arbitrary contents. -/
theorem ProfileRouteInputs.atPublishedDirectory {origin edges cells entries desc gap : ℕ}
    {placed : Memory w} (src : ProfileRouteInputs F f pub guess m) (base : (pub 0).val = a.frame)
    (rows : List Directory.Row) (place : (RoutingOutputs.privateLayout a.frame origin edges cells entries desc gap).Image
      (readings m) entries (readings placed)) (room : a.next ≤ origin) :
    ProfileRouteInputs F f pub guess (Directory.ISA.publish placed a.frame a.next rows) := by
  obtain ⟨input,fr,ib,last⟩ := routeInput_room a team slot packet F
  apply src.congr
  · intro x hx
    rw [input] at hx
    exact directoryPublished_low rows place room x (by omega) (by omega)
  · intro j hj
    exact directoryPublished_low rows place room _ (by omega) (by omega)
  · intro k hk
    rw [base]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    exact directoryPublished_low rows place room _ (by omega) (by omega)

/-- The compact demand stream is compiled from the real placements at the end of the
private pass. This specializes the low-source proof to the exact pre-schedule state
published by the physical profile path. -/
theorem BootResidence.demandInputs {k origin edges cells gap : ℕ} {mac : TeamOpcode.Macros w 8}
    {bank : Bank w} {initial placed : Memory w} {g : Fin k → Bool}
    (base : (pub 0).val = a.frame) (D : Directory.Layout)
    (path : BootResidence (F := F) a team slot packet f A pub mac bits initial bank g after)
    (place : (RoutingOutputs.privateLayout a.frame origin edges cells D.entries D.description gap).Image
      (readings after) D.entries (readings placed)) (reserve : a.next+7*D.candidates ≤ origin) :
    let tables := RoutingOutputs.bases origin edges cells D.entries
    let rows := D.directory (Directory.ISA.placement (readings placed) tables.privatePairs)
      (Directory.ISA.placement (readings placed) tables.livePairs)
    ProfileRouteInputs F f pub (Pins.extendGuess g) (Directory.ISA.publish placed a.frame a.next rows) := by
  intro tables rows
  exact (path.routeInputs a team slot packet base).atPublishedDirectory a team slot packet base rows place (by omega)

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
