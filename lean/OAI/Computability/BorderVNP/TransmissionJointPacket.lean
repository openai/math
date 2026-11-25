import OAI.Computability.BorderVNP.TransmissionPacketFrame
import OAI.Computability.BorderVNP.DiagonalNativeUnitStartup

/-! # Boot, physical packet gather and extended-frame installation before the signed selector -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins

/-- The actual signed-entry verifier, its query-address list, the 81 extended-frame
words, and its selected H* index in one canonical packet. -/
def ReferencePacket.ofCircuit {q v gates w d : ℕ} (base start : ℕ)
    (c : BooleanTranscript.Circuit (Fin q ⊕ Fin v) gates) (src : Fin q → ℕ)
    (extension : Fin 81 → Word w) (star : Fin d → Bool) : ReferencePacket w d :=
  ⟨DiagonalResidueRAM.payload w base start c src, extension, star⟩

/-- The certificate charge counts six header words, three words per shared gate, one
word per public query address, 81 extension words, and one bit per reference position. -/
theorem ReferencePacket.certificate_charge {q v gates w d : ℕ} (base start : ℕ)
    (c : BooleanTranscript.Circuit (Fin q ⊕ Fin v) gates) (src : Fin q → ℕ)
    (extension : Fin 81 → Word w) (star : Fin d → Bool) :
    (ReferencePacket.ofCircuit base start c src extension star).bits.length =
      w*(6+3*gates+q+81)+d := by
  rw [ReferencePacket.bits_length, ReferencePacket.offset]
  change w*((DiagonalResidueRAM.payload w base start c src).length+81)+d = _
  rw [DiagonalResidueRAM.payload_length]

/-- A word-space budget for all three fixed startup fragments, in actual charged ticks. -/
def jointBudget (count w : ℕ) : ℕ :=
  126+(literalAdviceSetup.slots+count*(literalAdviceBit.slots+1)+1)+(ExtendedFrame.setup.slots+8*81*(w+1)+8)

/-- Both the literal bits and the real boot/gather/install ticks have one common
explicit charge, linear in gate count, query arity and pin width at a fixed RAM width. -/
theorem ReferencePacket.joint_charge_le {q v gates w d : ℕ} (base start : ℕ)
    (c : BooleanTranscript.Circuit (Fin q ⊕ Fin v) gates) (src : Fin q → ℕ)
    (extension : Fin 81 → Word w) (star : Fin d → Bool) :
    let bits := (ReferencePacket.ofCircuit base start c src extension star).bits.length
    jointBudget bits w + bits ≤ 4096*(w+1)*(gates+q+d+1) := by
  intro bits
  have count : bits = w*(6+3*gates+q+81)+d := ReferencePacket.certificate_charge ..
  have setup : literalAdviceSetup.slots ≤ 100 := by decide
  have copy : literalAdviceBit.slots+1 ≤ 16 := by decide
  have frame : ExtendedFrame.setup.slots ≤ 64 := by decide
  have ht := Nat.mul_le_mul_left bits copy
  unfold jointBudget
  rw [count] at ht ⊢
  nlinarith

variable {pc reg k routines m g R r w a d : ℕ} {Q Γ : Type} [Fintype Q]
variable (physical : VPVNP.UniversalMachine.Program)
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
variable (S : SiteData R r reg k w a)

set_option maxRecDepth 3500 in
/-- Starting in the actual RAM initialized by the contracted processor tapes, the three
native fragments install the public scalar frame, preserve the original processor inputs,
deliver the packed residue certificate, and keep the true reference H* available.
Only the specified scalar operands and numeric memory bounds are assumed at entry. -/
theorem jointPacket_run_coreWith (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : fitsWith physical reg k r w a R link n e) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (f : BroadcastFrame) (A : AdviceLayout) :
    let G := wiringWith physical P (S.withPacket pack) d link n e fit
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let p := pack u
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord w F.header)
    PacketFrame L f A p.entry.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val → A.Fits f w (pub 0).val →
    ExtendedFrame.Fits w (pub 0).val A.dst p.entry.length →
    A.offset = adviceOffsetWith physical r k reg w n → p.bits.length ≤ A.count → starbase = A.dst+p.offset →
    ∃ es t mt, Runs pub mac Evaluator.unitStartup s initial es t mt ∧
      traceCost es ≤ jointBudget A.count w ∧ (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧
      F.ContainsInput mt ∧ PacketFrame L f A p.entry.length w (readings pub) (readings mt) ∧
      (∀ i : Fin 81, mt ((pub 0).val+31+i.val) = p.extension i) ∧
      DiagonalTallyBits.WordsAt mt A.dst (p.entry.map wordBits) ∧
      (∀ i : Fin d, mt (starbase+i.val) = TeamTapeInputEmit.word w (p.reference i).toNat) ∧
      ∀ i : Fin 31, mt ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1)) := by
  intro G L F p initial scalar physicalRoom adviceRoom frameRoom offset count star
  let mb := bootMemory pub initial 31
  obtain ⟨bs,b,boot,bc⟩ := bootFrame_run pub mac s initial (by have := frameRoom.frameBound; omega)
  have bootFields : PacketFrame L f A p.entry.length w (readings pub) (readings mb) :=
    scalar.congr (boot_field pub initial)
  have inputRoom : F.header.length ≤ (pub 0).val := by
    rw [F.header_length, scalar.input_extent]
    exact physicalRoom.input
  have bootInput : F.ContainsInput mb := (F.containsInput_initial w).boot pub 31 inputRoom
  have gather := gather_adviceWith physical P (S.withPacket pack) d link n e fit u pin ext ibase hbase starbase pub mac b mb f A
    bootFields.broadcast bootFields.pins bootInput bootFields.advice physicalRoom adviceRoom offset
  obtain ⟨gs,z,mz,gatherRun,gc,image,readSite⟩ := gather.complete trivial
  change readings mz = A.copied f (readings mb) A.count at image
  have gatheredFields : PacketFrame L f A p.entry.length w (readings pub) (readings mz) := by
    apply bootFields.congr
    intro i hi
    exact (congrFun image _).trans (A.copied_outside f (readings mb) (adviceRoom.frameDisjoint i hi))
  have gatheredInput : F.ContainsInput mz := by
    intro j hj
    apply Fin.ext
    exact (congrFun image j).trans ((A.copied_outside f (readings mb)
      (adviceRoom.sourceDisjoint j (by rwa [← scalar.input_extent,←F.header_length]))).trans
        (congrArg Fin.val (bootInput j hj)))
  have procs : f.processors = r := bootFields.broadcast.2.2.1.symm.trans bootFields.pins.processors
  have all (i : ℕ) (hi : i < p.bits.length) : (mz (A.dst+i)).val = (p.bits[i]?.getD false).toNat := by
    have hi' := hi.trans_le count
    let j : Fin r := ⟨i,procs ▸ hi'.trans_le adviceRoom.count⟩
    have h := readSite j hi'
    change (mz (A.dst+i)).val = (TeamTapeInputEmit.word w (p.bits[i]?.getD false).toNat).val at h
    have small : (p.bits[i]?.getD false).toNat < 2^w :=
      (Bool.toNat_le _).trans_lt (by have := frameRoom.frameBound; omega)
    exact h.trans (Nat.mod_eq_of_lt small)
  obtain ⟨entryBits,extBits,refBits⟩ := p.word_banks mz A.dst all
  obtain ⟨is,y,install,ic,_⟩ := ExtendedFrame.install_run pub mac z mz A.dst p.entry.length p.extension
    gatheredFields.extension frameRoom extBits
  let mt := ExtendedFrame.installed mz (pub 0).val p.extension
  have outside (j : ℕ) (h : j < (pub 0).val+31 ∨ (pub 0).val+112 ≤ j) : mt j = mz j :=
    ExtendedFrame.installed_outside mz (pub 0).val p.extension j h
  have run : Runs pub mac Evaluator.unitStartup s initial (bs++(gs++is)) y mt := boot.seq (gatherRun.seq install)
  refine ⟨_,_,_,run,?_,run.unsigned_events (by decide),?_,?_,ExtendedFrame.installed_at mz (pub 0).val p.extension,?_,?_,?_⟩
  · rw [show traceCost (bs++(gs++is)) = traceCost bs + traceCost (gs++is) from RAMBuckets.cost_append ..,
      show traceCost (gs++is) = traceCost gs + traceCost is from RAMBuckets.cost_append ..]
    unfold jointBudget
    omega
  · intro j hj
    exact (outside j (.inl (by omega))).trans (gatheredInput j hj)
  · apply gatheredFields.congr
    intro i hi
    exact congrArg Fin.val (outside ((pub 0).val+i) (.inl (by omega)))
  · apply DiagonalTallyBits.words_congr mz mt A.dst w _ entryBits
    · intro bs h
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp h
      exact length_wordBits x
    · intro j hj _
      exact outside j (.inr (frameRoom.separate.trans hj))
  · intro i
    rw [star,outside _ (.inr (by have := frameRoom.separate; omega))]
    apply Fin.ext
    exact (refBits i).trans (Nat.mod_eq_of_lt ((Bool.toNat_le _).trans_lt
      (by have := frameRoom.frameBound; omega))).symm
  · intro i
    rw [outside _ (.inl (Nat.add_lt_add_left i.isLt _))]
    apply Fin.ext
    have gatherKept := (congrFun image ((pub 0).val+i.val)).trans
      (A.copied_outside f (readings mb) (adviceRoom.frameDisjoint i.val i.isLt))
    have orig := boot_field pub initial i.val i.isLt
    simpa only [frameField,zero_add,operand,readings] using gatherKept.trans orig

/-- The ordinary signed processor instance of the program-indexed result. -/
theorem jointPacket_run_core (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : Fits P lib r w a R link n e) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (f : BroadcastFrame) (A : AdviceLayout) :
    let G := wiring P lib (S.withPacket pack) d link n e fit
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let p := pack u
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord w F.header)
    PacketFrame L f A p.entry.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val → A.Fits f w (pub 0).val →
    ExtendedFrame.Fits w (pub 0).val A.dst p.entry.length →
    A.offset = adviceOffset P lib r w n → p.bits.length ≤ A.count → starbase = A.dst+p.offset →
    ∃ es t mt, Runs pub mac Evaluator.unitStartup s initial es t mt ∧
      traceCost es ≤ jointBudget A.count w ∧ (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧
      F.ContainsInput mt ∧ PacketFrame L f A p.entry.length w (readings pub) (readings mt) ∧
      (∀ i : Fin 81, mt ((pub 0).val+31+i.val) = p.extension i) ∧
      DiagonalTallyBits.WordsAt mt A.dst (p.entry.map wordBits) ∧
      (∀ i : Fin d, mt (starbase+i.val) = TeamTapeInputEmit.word w (p.reference i).toNat) ∧
      ∀ i : Fin 31, mt ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1)) :=
  jointPacket_run_coreWith (TeamSite.Processor.machine P lib) P S pack link n e fit u pin ext ibase hbase starbase pub mac s f A

set_option maxRecDepth 3500 in
/-- The startup interface used by the unit and residue evaluators, with the pin,
certificate, extension and scalar fields needed by their native continuations. -/
theorem jointPacket_runWith (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : fitsWith physical reg k r w a R link n e) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (f : BroadcastFrame) (A : AdviceLayout) :
    let G := wiringWith physical P (S.withPacket pack) d link n e fit
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let p := pack u
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord w F.header)
    PacketFrame L f A p.entry.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val → A.Fits f w (pub 0).val →
    ExtendedFrame.Fits w (pub 0).val A.dst p.entry.length →
    A.offset = adviceOffsetWith physical r k reg w n → p.bits.length ≤ A.count → starbase = A.dst+p.offset →
    ∃ es t mt, Runs pub mac Evaluator.unitStartup s initial es t mt ∧
      traceCost es ≤ jointBudget A.count w ∧ (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧
      F.ContainsInput mt ∧ PacketFrame L f A p.entry.length w (readings pub) (readings mt) ∧
      (∀ i : Fin 81, mt ((pub 0).val+31+i.val) = p.extension i) ∧
      DiagonalTallyBits.WordsAt mt A.dst (p.entry.map wordBits) ∧
      ∀ i : Fin d, mt (starbase+i.val) = TeamTapeInputEmit.word w (p.reference i).toNat := by
  intro G L F p initial scalar room advice extended offset count star
  obtain ⟨es,t,mt,run,cost,events,input,fields,extension,entry,reference,_⟩ :=
    jointPacket_run_coreWith physical P S pack link n e fit u pin ext ibase hbase starbase pub mac s f A
      scalar room advice extended offset count star
  exact ⟨es,t,mt,run,cost,events,input,fields,extension,entry,reference⟩

/-- The ordinary signed processor instance of the program-indexed result. -/
theorem jointPacket_run (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : Fits P lib r w a R link n e) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (f : BroadcastFrame) (A : AdviceLayout) :
    let G := wiring P lib (S.withPacket pack) d link n e fit
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let p := pack u
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord w F.header)
    PacketFrame L f A p.entry.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val → A.Fits f w (pub 0).val →
    ExtendedFrame.Fits w (pub 0).val A.dst p.entry.length →
    A.offset = adviceOffset P lib r w n → p.bits.length ≤ A.count → starbase = A.dst+p.offset →
    ∃ es t mt, Runs pub mac Evaluator.unitStartup s initial es t mt ∧
      traceCost es ≤ jointBudget A.count w ∧ (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧
      F.ContainsInput mt ∧ PacketFrame L f A p.entry.length w (readings pub) (readings mt) ∧
      (∀ i : Fin 81, mt ((pub 0).val+31+i.val) = p.extension i) ∧
      DiagonalTallyBits.WordsAt mt A.dst (p.entry.map wordBits) ∧
      ∀ i : Fin d, mt (starbase+i.val) = TeamTapeInputEmit.word w (p.reference i).toNat :=
  jointPacket_runWith (TeamSite.Processor.machine P lib) P S pack link n e fit u pin ext ibase hbase starbase pub mac s f A

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
