import OAI.Computability.BorderVNP.TransmissionPacketWords
import OAI.Computability.BorderVNP.RoutingISAExtendedFrame

/-! # Public scalar fields of the three-stage literal packet startup -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins

/-- The ordinary public parameter at the specified zero-based frame field. -/
def operand {w : ℕ} (pub : Arg → Word w) (i : ℕ) : ℕ := readings pub (Fin.ofNat 32 (i+1))

/-- The joint startup needs only broadcast geometry, pin geometry and the three scalar
fields of each gather/decoder. The same field can occur in two of the shared layouts. -/
structure PacketFrame (L : Layout) (f : BroadcastFrame) (A : AdviceLayout)
    (words w : ℕ) (pub : Arg → ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Physical input and broadcast directory. -/
  broadcast : f.At pub mem
  /-- Physical pin and scratch arrays. -/
  pins : Frame L pub mem
  /-- One bit per processor, with its designated literal position. -/
  advice : A.At pub mem
  /-- Packet base, packed entry-prefix length and word width. -/
  extension : ExtendedFrame.Loaded pub mem A.dst words w

/-- The entire joint startup frame is preserved by agreement on its first 31 cells. -/
theorem PacketFrame.congr {L : Layout} {f : BroadcastFrame} {A : AdviceLayout} {words w : ℕ}
    {pub pub' : Arg → ℕ} {mem mem' : ℕ → ℕ}
    (h : PacketFrame L f A words w pub mem)
    (eq : ∀ i < 31, frameField pub' mem' i = frameField pub mem i) :
    PacketFrame L f A words w pub' mem' := by
  constructor
  · simpa only [BroadcastFrame.At, eq _ (by decide : 0 < 31), eq _ (by decide : 1 < 31),
      eq _ (by decide : 2 < 31), eq _ (by decide : 3 < 31), eq _ (by decide : 4 < 31),
      eq _ (by decide : 5 < 31), eq _ (by decide : 25 < 31)] using h.broadcast
  · obtain ⟨t,ts,p,l,k,ib,hb,width,star⟩ := h.pins
    constructor <;> rw [eq _ (by decide)] <;> assumption
  · simpa only [AdviceLayout.At,eq _ (by decide : 26 < 31),eq _ (by decide : 27 < 31),
      eq _ (by decide : 28 < 31)] using h.advice
  · simpa only [ExtendedFrame.Loaded,eq _ (by decide : 28 < 31),eq _ (by decide : 29 < 31),
      eq _ (by decide : 30 < 31)] using h.extension

/-- Each installed ordinary field is the actual next public scalar operand. -/
theorem boot_field {w : ℕ} (pub : Arg → Word w) (mem : Memory w) (i : ℕ) (hi : i < 31) :
    frameField (readings pub) (readings (bootMemory pub mem 31)) i =
      frameField (fun _ => 0) (operand pub) i := by
  have word : bootMemory pub mem 31 ((pub 0).val+i) = pub (Fin.ofNat 32 (i+1)) := by
    unfold bootMemory
    split
    · apply congrArg pub
      apply Fin.ext
      simp only [Fin.val_ofNat, Nat.add_sub_cancel_left, Nat.mod_eq_of_lt (by omega : i+1 < 32)]
    · rename_i h
      exact False.elim (h (by omega))
  simpa only [frameField, Nat.zero_add, operand, readings] using congrArg Fin.val word

/-- The shared stride and number of input sites agree in the broadcast and pin layouts. -/
theorem PacketFrame.input_extent {L : Layout} {f : BroadcastFrame} {A : AdviceLayout}
    {words w : ℕ} {pub : Arg → ℕ} {mem : ℕ → ℕ} (h : PacketFrame L f A words w pub mem) :
    L.processors * L.stride = f.processors * f.stride := by
  obtain ⟨_,ts,p,l,k,_,_⟩ := h.broadcast
  rw [← h.pins.processors,p,Layout.stride,Layout.offset,← h.pins.literal,l,←h.pins.teams,ts,←h.pins.link,k,
    BroadcastFrame.stride]
  congr 1
  omega

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
