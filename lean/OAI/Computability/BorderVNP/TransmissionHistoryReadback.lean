import OAI.Computability.BorderVNP.TransmissionImageReturns
import OAI.Computability.BorderVNP.TransmissionLastWrite

/-! # The values seen by the cells after transmission

The scheduler correspondence associates each returning history with its unique
permitted local word. A remote delivery compares the source in the sender's prefix
memory with the physically routed link word. A remote shared interval has two
receiving endpoints. A co-located interval makes one guess for both writes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

/-- The inputs, native return and corresponding finite local choice word on one team.
The readback rules for two teams can thus use distinct memories and actual registers. -/
structure TeamHistory (w : ℕ) where
  /-- The directory popped by this team. -/
  rows : ℕ → Range w
  /-- Native public arguments. -/
  pub : Arg → Word w
  /-- Private routines of the surrounding processor. -/
  macros : TeamOpcode.Macros w 8
  /-- Memory at the start of transmission. -/
  initial : Memory w
  /-- Initial native registers. -/
  start : Bank w
  /-- The concrete returning trace, register bank and final memory. -/
  history : TableReturn pub macros start initial
  /-- The locally guessed word recovered from the return. -/
  word : SenderWords rows pub initial
  /-- The word is the return's actual chronological stream of guesses. -/
  stream : history.val.1.flatMap TeamRAM.Event.choices = List.ofFn word.val
  /-- The final memory is the checked directory fold. -/
  output : history.val.2.2 = tableMemory rows (directoryFrame pub initial 0) pub initial
    (decodeChoices rows (directoryFrame pub initial 0) (List.ofFn word.val)) (directoryFrame pub initial 13).val

namespace TeamHistory

variable {w : ℕ}

/-- Associate any native return with its word, using the checked scheduled equivalence
and its effect equations. In particular the equivalence may be the one supplied by
`image_sender_equiv` on the actual scheduler output. -/
def ofEquiv (rows : ℕ → Range w) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (E : SenderWords rows pub m ≃ TableReturn pub macros s m)
    (effects : ∀ b, (E b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b.val ∧
      (E b).val.2.2 = tableMemory rows (directoryFrame pub m 0) pub m
        (decodeChoices rows (directoryFrame pub m 0) (List.ofFn b.val)) (directoryFrame pub m 13).val)
    (z : TableReturn pub macros s m) : TeamHistory w where
  rows := rows
  pub := pub
  macros := macros
  initial := m
  start := s
  history := z
  word := E.symm z
  stream := by simpa using (effects (E.symm z)).1
  output := by simpa using (effects (E.symm z)).2

/-- The executing team as loaded from the physical frame. -/
abbrev team (h : TeamHistory w) := directoryFrame h.pub h.initial 0

/-- Number of rows the native loop actually scans. -/
abbrev count (h : TeamHistory w) := (directoryFrame h.pub h.initial 13).val

/-- Row and slot-indexed bits of the finite locally shared assignment. -/
abbrev bits (h : TeamHistory w) := decodeChoices h.rows h.team (List.ofFn h.word.val)

/-- Physical memory on entry to the indicated range. -/
abbrev before (h : TeamHistory w) (i : ℕ) := tableMemory h.rows h.team h.pub h.initial h.bits i

/-- The endpoint word at an actual bit-handling load, using the prefix memory after
all earlier rows and all earlier offsets of the current range. -/
def linkWord (h : TeamHistory w) (i : ℕ) (mode : Role) (peer : Reg) (j : ℕ) : Word w :=
  let mem := bitMemory h.rows h.team h.pub h.initial h.bits i mode j
  mem (endpointNat peer h.pub ((h.rows i).bitBank h.team j) mem)

/-- Read a consumer input in the actual final memory at its last addressed write. -/
theorem readback (h : TeamHistory w) {i mode j a}
    (write : LastWrite h.rows h.team h.count i mode j a) :
    h.history.val.2.2 a = mode.payload h.pub ((h.rows i).bitBank h.team j)
      (bitMemory h.rows h.team h.pub h.initial h.bits i mode j) (h.bits i j) := by
  rw [h.output]
  exact write.readback h.pub h.initial h.bits

/-- Local data delivery copies its live source directly to the final consumer slot. -/
theorem local_data (h : TeamHistory w) {i j a}
    (write : LastWrite h.rows h.team h.count i .dataHere j a) :
    let mem := bitMemory h.rows h.team h.pub h.initial h.bits i .dataHere j
    h.history.val.2.2 a = mem ((h.rows i).source + Fin.ofNat _ j).val :=
  h.readback write

/-- Both consumers of a co-located shared wire receive the one guessed bit at its
offset. The two destination addresses may coincide. -/
theorem local_shared (h : TeamHistory w) {i j a b}
    (left : LastWrite h.rows h.team h.count i .sharedHere j a)
    (right : LastWrite h.rows h.team h.count i .sharedHere j b) :
    h.history.val.2.2 a = (if h.bits i j then 1 else 0) ∧
      h.history.val.2.2 b = (if h.bits i j then 1 else 0) :=
  ⟨h.readback left, h.readback right⟩

/-- For a remote data row, the physical comparison on the sender forces equality
with its prescribed source. Equality of the two relay endpoints transfers the value
to the receiving cell's actual final slot. -/
theorem remote_data (sender receiver : TeamHistory w) {i j dst}
    (senderRow : i < sender.count) (senderBit : j < (sender.rows i).width.val)
    (sending : (sender.rows i).selected sender.team = some (some .sendData))
    (received : LastWrite receiver.rows receiver.team receiver.count i .receiveB j dst)
    (wire : sender.before i ((sender.rows i).senderAddress sender.pub (sender.before i) j) =
      receiver.linkWord i .receiveB 9 j) :
    receiver.history.val.2.2 dst = sender.before i ((sender.rows i).source.val+j) := by
  have check := sender.word.property i senderRow sending j senderBit
  calc
    _ = receiver.linkWord i .receiveB 9 j := receiver.readback received
    _ = _ := wire.symm.trans check.symm

/-- The two remote receiving cells of a shared wire read equal final inputs
when their true physical link words agree. -/
theorem remote_shared (left right : TeamHistory w) {i j a b}
    (toA : LastWrite left.rows left.team left.count i .receiveA j a)
    (toB : LastWrite right.rows right.team right.count i .receiveB j b)
    (wire : left.linkWord i .receiveA 10 j = right.linkWord i .receiveB 9 j) :
    left.history.val.2.2 a = right.history.val.2.2 b :=
  (left.readback toA).trans (wire.trans (right.readback toB).symm)

end TeamHistory
end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
