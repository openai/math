import OAI.Computability.BorderVNP.TransmissionJointHeaderBoot
import OAI.Computability.BorderVNP.TransmissionPinsComplete

/-! # Geometry input survives the substituted-index choices at evaluation startup

The pin stage writes the substituted-index interval and the live copy on the lead team. The
geometry evaluator reads the original processor fields, the common copied header and the boot
frame. Separation of those three intervals preserves the geometry input for every guessed index.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA TeamContraction ProcessorSlots JointHeader

/-- The boot state words read by the geometry evaluator, independent of transient registers. -/
structure ProfileOperands {w d : ℕ} {L : Pins.Layout} (P : Pins.ProcessorFields L) (f : BroadcastFrame)
    (A : AdviceLayout) (rp : ReferencePacket w d) (pub : Arg → Word w) (bits : List Bool) (mem : Memory w) : Prop where
  /-- Original time-zero words on the physical processor tapes. -/
  input : P.ContainsInput mem
  /-- Ordinary scalar frame supplying the broadcast dimensions. -/
  frame : PacketFrame L f A rp.entry.length w (readings pub) (readings mem)
  /-- Extension fields decoded from the reader's actual reference packet. -/
  extension : ∀ i : Fin 81, mem ((pub 0).val+31+i.val) = rp.extension i
  /-- The common exterior header copied word by word. -/
  header : FlatAt mem f.dst bits

/-- The ordinary boot and broadcast-copy postcondition supplies exactly these inputs. -/
theorem ProfileOperands.from_boot {w d : ℕ} {L : Pins.Layout} {P : Pins.ProcessorFields L} {f A rp pub bits bank mem}
    (h : BootHeaderState (w := w) (d := d) P f A rp pub bits bank mem) : ProfileOperands P f A rp pub bits mem :=
  ⟨h.input,h.frame,h.extension,h.header⟩

/-- A physical interval is disjoint from the two writable pin banks. The live-copy bank
needs only the number of genuine pin positions, even if a literal has unused positions. -/
def PinClear (L : Pins.Layout) (start count : ℕ) : Prop :=
  (start+count ≤ L.ibase ∨ L.ibase+L.count ≤ start) ∧
    (start+count ≤ L.hbase ∨ L.hbase+L.width ≤ start)

private theorem PinClear.read {w : ℕ} {L : Pins.Layout} {start count : ℕ} (clear : PinClear L start count)
    (guess : ℕ → Bool) (m : Memory w) (i : ℕ) (hi : i < count) :
    Pins.preparedMemory L guess m L.count (start+i) = m (start+i) := by
  apply Pins.preparedMemory_other
  · intro x hx; obtain ⟨ha,_⟩ := clear; omega
  · intro x _ active; have hwidth := active.2; obtain ⟨_,hb⟩ := clear; omega

/-- Every possible true pin assignment produces the same profile, advice and geometry
operands on the real post-preparation memory. -/
theorem ProfileOperands.prepared {w d : ℕ} {L : Pins.Layout} {P : Pins.ProcessorFields L}
    {f A} {rp : ReferencePacket w d} {pub bits mem} (h : ProfileOperands P f A rp pub bits mem)
    (guess : ℕ → Bool) (input : PinClear L 0 P.header.length) (frame : PinClear L (pub 0).val 112)
    (header : PinClear L f.dst bits.length) : ProfileOperands P f A rp pub bits (Pins.preparedMemory L guess mem L.count) := by
  refine ⟨fun a ha => ?_,h.frame.congr (fun i hi => ?_),fun i => ?_,fun i => ?_⟩
  · have eq := input.read guess mem a ha
    rw [Nat.zero_add] at eq
    exact eq.trans (h.input a ha)
  · exact congrArg Fin.val (frame.read guess mem i (by omega))
  · simpa only [Nat.add_assoc] using (frame.read guess mem (31+i.val) (by have := i.isLt; omega)).trans
      (by simpa only [Nat.add_assoc] using h.extension i)
  · exact (header.read guess mem i i.isLt).trans (h.header i)

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
