import OAI.Computability.BorderVNP.TransmissionJointPacket

/-! # Constructing the actual 32-operand boot bank for the signed site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins

/-- Ordinary boot operands reserved by the physical input, packet and broadcast routines.
The caller supplies the public words of every other evaluator stage independently. -/
structure PacketOperands where
  /-- Physical dimensions and pin-array bases. -/
  layout : Layout
  /-- Base of the common scalar frame. -/
  frameBase : ℕ
  /-- Common header width. -/
  header : ℕ
  /-- Address of the team's common-broadcast copy. -/
  broadcastBase : ℕ
  /-- Source offset, count, and destination of the one-bit-per-processor copy. -/
  advice : AdviceLayout
  /-- Number of residue-entry words preceding the 81 extended-frame words. -/
  entryWords : ℕ

/-- Shared physical geometry as used by the common-header reader. -/
def PacketOperands.broadcast (B : PacketOperands) : BroadcastFrame :=
  ⟨B.layout.team,B.layout.teams,B.layout.processors,B.layout.literal,B.layout.link,B.header,B.broadcastBase⟩

/-- Operand zero is the frame base. Operand `i+1` initializes frame word `i`.
Unclaimed operands preserve their supplied caller values. -/
def PacketOperands.value (B : PacketOperands) (w : ℕ) : ℕ → Option ℕ
  | 0 => some B.frameBase
  | 1 => some B.layout.team
  | 2 => some B.layout.teams
  | 3 => some B.layout.processors
  | 4 => some B.layout.literal
  | 5 => some B.layout.link
  | 6 => some B.header
  | 22 => some B.layout.ibase
  | 23 => some B.layout.hbase
  | 24 => some B.layout.width
  | 25 => some B.layout.starbase
  | 26 => some B.broadcastBase
  | 27 => some B.advice.offset
  | 28 => some B.advice.count
  | 29 => some B.advice.dst
  | 30 => some B.entryWords
  | 31 => some w
  | _ => none

/-- The finite list of scalars encoded by the packet allocator. -/
def PacketOperands.values (B : PacketOperands) (w : ℕ) : List ℕ :=
  [B.frameBase,B.layout.team,B.layout.teams,B.layout.processors,B.layout.literal,B.layout.link,B.header,
    B.layout.ibase,B.layout.hbase,B.layout.width,B.layout.starbase,B.broadcastBase,
    B.advice.offset,B.advice.count,B.advice.dst,B.entryWords,w]

/-- A single word-fit condition on the ordinary scalar values is sufficient for the encoder. -/
def PacketOperands.Fits (B : PacketOperands) (w : ℕ) : Prop := ∀ x ∈ B.values w, x < 2^w

/-- Actual finite bank read by the native processor's public operand decoder. -/
def PacketOperands.bank {w : ℕ} (B : PacketOperands) (other : Arg → Word w) (i : Arg) : Word w :=
  (B.value w i.val).elim (other i) (TeamTapeInputEmit.word w)

/-- Every unclaimed operand retains the exact original word, even if its contents happen
to equal one of the packet values. -/
theorem PacketOperands.bank_other {w : ℕ} (B : PacketOperands) (other : Arg → Word w) (i : Arg)
    (unclaimed : B.value w i.val = none) : B.bank other i = other i := by
  simp [PacketOperands.bank,unclaimed]

/-- Scalar operands 7 through 21 belong entirely to the independent routing stages. -/
theorem PacketOperands.bank_passthrough {w : ℕ} (B : PacketOperands) (other : Arg → Word w)
    (i : Arg) (lo : 7 ≤ i.val) (hi : i.val ≤ 21) : B.bank other i = other i := by
  apply B.bank_other
  generalize he : i.val = j at lo hi ⊢
  interval_cases j <;> rfl

private theorem read_claim {w x : ℕ} (B : PacketOperands) (other : Arg → Word w) (i : Arg)
    (claim : B.value w i.val = some x) (hx : x < 2^w) : readings (B.bank other) i = x := by
  simp [readings,PacketOperands.bank,claim,TeamTapeInputEmit.word, Nat.mod_eq_of_lt hx]

/-- The concrete bank supplies the true frame-base address. -/
theorem PacketOperands.frameBase_word {w : ℕ} (B : PacketOperands) (other : Arg → Word w) (room : B.Fits w) :
    readings (B.bank other) 0 = B.frameBase :=
  read_claim B other 0 rfl (room _ (by simp [PacketOperands.values]))

/-- The concrete encoding of all required scalar values discharges the pure public-frame
premise of the boot/gather/install theorem. -/
theorem PacketOperands.packetFrame {w : ℕ} (B : PacketOperands) (other : Arg → Word w) (room : B.Fits w) :
    PacketFrame B.layout B.broadcast B.advice B.entryWords w (fun _ => 0) (operand (B.bank other)) := by
  have h (i : Arg) (x : ℕ) (claim : B.value w i.val = some x) (mem : x ∈ B.values w) :
      readings (B.bank other) i = x := read_claim B other i claim (room _ mem)
  constructor
  · unfold BroadcastFrame.At
    repeat' apply And.intro
    all_goals (apply h _ _ rfl; simp [PacketOperands.values,PacketOperands.broadcast])
  · constructor
    all_goals (apply h _ _ rfl; simp [PacketOperands.values])
  · unfold AdviceLayout.At
    repeat' apply And.intro
    all_goals (apply h _ _ rfl; simp [PacketOperands.values])
  · unfold ExtendedFrame.Loaded
    repeat' apply And.intro
    all_goals (apply h _ _ rfl; simp [PacketOperands.values])

variable {R r reg w a : ℕ}

/-- Install the allocator on the ordinary 32 public operands of each real team's
site literal. The logical caps, prescribed initial registers and advice stay available. -/
def SiteData.withOperands (S : SiteData R r reg 32 w a) (B : Fin (R+1) → PacketOperands) :
    SiteData R r reg 32 w a :=
  { S with publicWords := fun u => (B u).bank (S.publicWords u) }

/-- Choosing the public operands and the separate distributed literal bit commutes exactly. -/
theorem SiteData.withOperands_withPacket {d : ℕ} (S : SiteData R r reg 32 w a)
    (B : Fin (R+1) → PacketOperands) (pack : Fin (R+1) → ReferencePacket w d) :
    (S.withOperands B).withPacket pack = (S.withPacket pack).withOperands B := rfl

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
