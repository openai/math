import OAI.Computability.BorderVNP.RoutingISASignedReaderArena
import OAI.Computability.BorderVNP.TransmissionJointHeaderBoot
import OAI.Computability.BorderVNP.TransmissionPinIndex
import OAI.Computability.BorderVNP.TransmissionPinsReplay

/-! # The residue-reader controls and both bit indices on physical startup paths -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM DiagonalResidueRAM TeamContraction TeamContraction.JointHeader
open TeamContraction.ProcessorSlots Pins

variable {w : ℕ}

private theorem word_of_value (x : Word w) {v : ℕ} (hx : x.val=v) : x=word w v := by
  subst v
  exact Fin.ext (by simp [word])

/-- The real booted packet and the actual ordinary entry pointer supply
exactly the four word operands consumed by the final reader. -/
theorem boot_controls {d : ℕ} {L : Pins.Layout} {F : ProcessorFields L}
    {f : BroadcastFrame} {A : AdviceLayout} {p : ReferencePacket w d} {pub : Arg → Word w}
    {hdr : List Bool} {st : Bank w} {m : Memory w} (loaded : BootHeaderState F f A p pub hdr st m)
    {start : ℕ} (operand : pub 20=word w start) :
    packFrame pub m A.dst start p.entry.length := by
  obtain ⟨hd,hc,hw⟩ := loaded.frame.extension
  exact ⟨word_of_value _ hd,(loaded.core 19).trans operand,word_of_value _ hc,word_of_value _ hw⟩

/-- Pointwise survival of the four scalar reads and all genuine packed bits
transports the actual staged circuit and its operands to the final memory. -/
theorem reader_packet_after {d : ℕ} {L : Pins.Layout} {F : ProcessorFields L} {f : BroadcastFrame}
    {A : AdviceLayout} {p : ReferencePacket w d} {pub : Arg → Word w} {hdr : List Bool} {st : Bank w}
    {boot out : Memory w} (loaded : BootHeaderState F f A p pub hdr st boot)
    {start : ℕ} (operand : pub 20=word w start)
    (fields : ∀ k ∈ ([19,28,29,30] : List ℕ), out ((pub 0).val+k) = boot ((pub 0).val+k))
    (bytes : ∀ j < p.entry.length*w, out (A.dst+j)=boot (A.dst+j)) :
    packFrame pub out A.dst start p.entry.length ∧
      DiagonalTallyBits.WordsAt out A.dst (p.entry.map wordBits) := by
  obtain ⟨hd,hs,hc,hw⟩ := boot_controls loaded operand
  refine ⟨⟨(fields 28 (by decide)).trans hd,(fields 19 (by decide)).trans hs,
    (fields 29 (by decide)).trans hc,(fields 30 (by decide)).trans hw⟩,?_⟩
  apply DiagonalTallyBits.words_congr boot out A.dst w (p.entry.map wordBits) loaded.entry
  · intro x hx
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
    exact length_wordBits v
  · intro j low high
    rw [List.length_map] at high
    have eq : A.dst+(j-A.dst)=j := by omega
    simpa only [eq] using bytes (j-A.dst) (by omega)

/-- Every physical return of the lead team's index preparation on its observed
guess tape contains both the guessed row and the independent live column. -/
theorem lead_pin_words {R r t d link inner n : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (pin guess : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (m : Memory w) (s : Bank w)
    (physical : (G.processorFields 0 pin ext ibase hbase starbase).ContainsInput m)
    (frame : Frame (G.pinLayout 0 ibase hbase starbase) (readings pub) (readings m))
    (hframe : readings pub 0+24 < 2^w) (hs : (G.pinLayout 0 ibase hbase starbase).stride < 2^w)
    (hc : r*(G.program.length+t)<2^w) (room : d≤r*(G.program.length+t))
    (fit : LoopFits w (G.pinLayout 0 ibase hbase starbase))
    (sep : Separated (G.pinLayout 0 ibase hbase starbase))
    (actual : Pins.Return pub mac s m) (guessed : actual.val.1.flatMap TeamRAM.Event.choices=List.ofFn guess) :
    (∀ j, actual.val.2.2 (ibase+j.val)=wordBit w (guess j)) ∧
      (∀ j, actual.val.2.2 (hbase+j.val)=wordBit w (pin j)) := by
  obtain ⟨es,z,mz,run,_,choices,sub,col⟩ := G.preparePinIndices 0 pin guess ext ibase hbase starbase
    pub mac m s physical frame hframe hs hc room fit sep
  let a : Pins.Return pub mac s m := ⟨⟨es,z,mz⟩,run⟩
  have same : actual=a := Pins.return_eq_of_stream (u:=[]) (v:=[]) (by
    change actual.val.1.flatMap TeamRAM.Event.choices++[] = es.flatMap TeamRAM.Event.choices++[]
    simpa only [List.append_nil,guessed,ite_true] using choices.symm)
  rw [same]
  refine ⟨fun j ↦ ?_,fun j ↦ col rfl j⟩
  simpa [a,liveBit,j.isLt,wordBit,TeamTapeInputEmit.word] using sub j.val (j.isLt.trans_le room)

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
