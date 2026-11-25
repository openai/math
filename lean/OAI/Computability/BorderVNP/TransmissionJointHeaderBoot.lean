import OAI.Computability.BorderVNP.TransmissionJointHeader
import OAI.Computability.BorderVNP.TransmissionSiteOperands

/-! # Copying the canonical common header after the complete physical packet startup -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader

open VPVNP BurstRAM Routing RoutingISA RoutingISA.Pins ProcessorSlots

/-- The installed packet and complete common header at the branch instruction. -/
structure BootHeaderState {w d : ℕ} {L : Pins.Layout} (F : ProcessorFields L) (f : BroadcastFrame)
    (A : AdviceLayout) (p : ReferencePacket w d) (pub : Arg → Word w) (bits : List Bool)
    (s : Bank w) (mem : Memory w) : Prop where
  /-- All words of the original signed processor inputs survive the copy. -/
  input : F.ContainsInput mem
  /-- The ordinary boot frame retains its scalar operands. -/
  frame : PacketFrame L f A p.entry.length w (readings pub) (readings mem)
  /-- All 31 ordinary frame values, including caller-supplied cable, slot and cell fields. -/
  core (i : Fin 31) : mem ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1))
  /-- The packed decoder's 81 extended frame values survive. -/
  extension (i : Fin 81) : mem ((pub 0).val+31+i.val) = p.extension i
  /-- The residue entry certificate remains at its packed source. -/
  entry : DiagonalTallyBits.WordsAt mem A.dst (p.entry.map wordBits)
  /-- Every true reference bit is still available in the advised array. -/
  reference (i : Fin d) : mem (L.starbase+i.val) = TeamTapeInputEmit.word w (p.reference i).toNat
  /-- One physical word per bit of the actual canonical common header. -/
  header : FlatAt mem f.dst bits
  /-- Physical geometry and reference partner are available to the branch selector. -/
  registers : f.Stable (readings s)

/-- The actual executed instruction prefix before selecting either signed branch. -/
def bootHeader : Code := .seq Evaluator.unitStartup readBroadcast

variable {pc reg k routines m g R r w a d : ℕ} {Q Γ : Type} [Fintype Q]
variable (physical : UniversalMachine.Program)
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
variable (S : SiteData R r reg k w a)

set_option maxRecDepth 3500 in
/-- Execute the packet startup on an arbitrary physical wire assignment carrying the common header. -/
theorem packet_header_runCommonWith (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : fitsWith physical reg k r w a R link n e) (u : Fin (R+1)) (pin : Fin d → Bool)
    (L : WireLayout (R+1) r link) (bits : List Bool) (length : bits.length = L.header)
    (wire : Exterior R r link → Bool) (common : ∀ b, (L.exteriorEquiv wire).broadcast b = headerBits bits length)
    (ibase hbase starbase dst : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (A : AdviceLayout) :
    let G := wiringWith physical P (S.withPacket pack) d link n e fit
    let ext := wire
    let loc := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let f := G.transferFrame u L.header dst
    let p := pack u
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord w F.header)
    PacketFrame loc f A p.entry.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val → A.Fits f w (pub 0).val →
    ExtendedFrame.Fits w (pub 0).val A.dst p.entry.length →
    A.offset = adviceOffsetWith physical r k reg w n → p.bits.length ≤ A.count → starbase = A.dst+p.offset →
    (pub 0).val+112 ≤ dst → (A.dst+p.bits.length ≤ dst ∨ dst+L.header ≤ A.dst) →
    ∃ es t mt, Runs pub mac bootHeader s initial es t mt ∧
      traceCost es ≤ jointBudget A.count w + f.readTicks ∧
      (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧ BootHeaderState F f A p pub bits t mt := by
  intro G ext loc F f p initial scalar room advice extended off cap star frameBefore apart
  have hw : 0 < w := by
    by_contra! hz
    have h := extended.frameBound
    simp [show w = 0 by omega] at h
  obtain ⟨bs,b,mb,boot,bc,_,input,frame,extension,entry,ref,core⟩ :=
    jointPacket_run_coreWith physical P S pack link n e fit u pin ext ibase hbase starbase pub mac s f A
      scalar room advice extended off cap star
  obtain ⟨cs,z,mz,copy,cc,stable,stored,values⟩ :=
    native_copy L G u pin ext bits length common
      ibase hbase starbase dst pub mac b mb hw input frame.broadcast room
  change readings mz = f.copied (readings mb) L.header at stored
  have kept (addr : ℕ) (away : addr < dst ∨ dst+L.header ≤ addr) : mz addr = mb addr := by
    apply Fin.ext
    have value := congrFun stored addr
    change readings mz addr = (if dst ≤ addr ∧ addr-dst < L.header then _ else readings mb addr) at value
    change readings mz addr = readings mb addr
    simpa only [ite_eq_right (show ¬ (dst ≤ addr ∧ addr-dst < L.header) by omega)] using value
  have packetWord (addr : ℕ) (lo : A.dst ≤ addr) (hi : addr < A.dst+p.bits.length) :
      mz addr = mb addr := kept addr (by omega)
  have inputRoom : F.header.length ≤ (pub 0).val := by
    rw [F.header_length, scalar.input_extent]
    exact room.input
  have run : Runs pub mac bootHeader s initial (bs++cs) z mz := boot.seq copy
  refine ⟨_,_,_,run,(RAMBuckets.cost_append ..).trans_le (Nat.add_le_add bc cc),
    run.unsigned_events (by decide),?_,?_,?_,?_,?_,?_,flatAt_of_values hw mz dst bits values,stable⟩
  · intro j hj
    exact (kept j (.inl (by omega))).trans (input j hj)
  · apply frame.congr
    intro i hi
    exact congrArg Fin.val (kept ((pub 0).val+i) (.inl (by omega)))
  · intro i
    exact (kept ((pub 0).val+i.val) (.inl (by have := i.isLt; omega))).trans (core i)
  · intro i
    exact (kept ((pub 0).val+31+i.val) (.inl (by omega))).trans (extension i)
  · apply DiagonalTallyBits.words_congr mb mz A.dst w _ entry
    · intro v hv
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hv
      exact length_wordBits x
    · intro addr lo hi
      have bound : p.entry.length*w ≤ p.bits.length := by
        rw [p.bits_length,ReferencePacket.offset,Nat.mul_comm w (p.entry.length+81),Nat.add_mul]
        omega
      rw [List.length_map] at hi
      exact packetWord addr lo (hi.trans_le (Nat.add_le_add_left bound _))
  · intro i
    change mz (starbase+i.val) = _
    rw [packetWord _ (by omega) (by rw [p.bits_length]; omega)]
    exact ref i

/-- The signed site starts from the genuine time-zero RAM of the canonical exterior
assignment, boots the scalar frame, gathers the advised packet, installs its extended
frame and reads the full broadcast from the real partner blocks. -/
theorem packet_header_runWith (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : fitsWith physical reg k r w a R link n e) (u : Fin (R+1)) (pin : Fin d → Bool)
    (L : WireLayout (R+1) r link) (bits : List Bool) (length : bits.length = L.header)
    (payload : Fin (R+1) → Fin (R+1) → ℕ → Bool) (ibase hbase starbase dst : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (A : AdviceLayout) :
    let G := wiringWith physical P (S.withPacket pack) d link n e fit
    let ext := exterior L bits length payload
    let loc := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let f := G.transferFrame u L.header dst
    let p := pack u
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord w F.header)
    PacketFrame loc f A p.entry.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val → A.Fits f w (pub 0).val →
    ExtendedFrame.Fits w (pub 0).val A.dst p.entry.length →
    A.offset = adviceOffsetWith physical r k reg w n → p.bits.length ≤ A.count → starbase = A.dst+p.offset →
    (pub 0).val+112 ≤ dst → (A.dst+p.bits.length ≤ dst ∨ dst+L.header ≤ A.dst) →
    ∃ es t mt, Runs pub mac bootHeader s initial es t mt ∧
      traceCost es ≤ jointBudget A.count w + f.readTicks ∧
      (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧ BootHeaderState F f A p pub bits t mt := by
  exact packet_header_runCommonWith physical P S pack link n e fit u pin L bits length
    (exterior L bits length payload) (exterior_header L bits length payload)
    ibase hbase starbase dst pub mac s A

/-- The ordinary signed processor instance of the physical packet header result. -/
theorem packet_header_run (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : Fits P lib r w a R link n e) (u : Fin (R+1)) (pin : Fin d → Bool)
    (L : WireLayout (R+1) r link) (bits : List Bool) (length : bits.length = L.header)
    (payload : Fin (R+1) → Fin (R+1) → ℕ → Bool) (ibase hbase starbase dst : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (A : AdviceLayout) :
    let G := wiring P lib (S.withPacket pack) d link n e fit
    let ext := exterior L bits length payload
    let loc := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let f := G.transferFrame u L.header dst
    let p := pack u
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord w F.header)
    PacketFrame loc f A p.entry.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val → A.Fits f w (pub 0).val →
    ExtendedFrame.Fits w (pub 0).val A.dst p.entry.length →
    A.offset = adviceOffset P lib r w n → p.bits.length ≤ A.count → starbase = A.dst+p.offset →
    (pub 0).val+112 ≤ dst → (A.dst+p.bits.length ≤ dst ∨ dst+L.header ≤ A.dst) →
    ∃ es t mt, Runs pub mac bootHeader s initial es t mt ∧
      traceCost es ≤ jointBudget A.count w + f.readTicks ∧
      (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧ BootHeaderState F f A p pub bits t mt :=
  packet_header_runWith (TeamSite.Processor.machine P lib) P S pack link n e fit u pin L bits length payload
    ibase hbase starbase dst pub mac s A

set_option maxRecDepth 3500 in
/-- The whole header startup on the site's actual 32-word bank. Every team's literal
contains the encoded frame base, physical header layout and exact packet charge. The
reference address follows the 81 decoded frame words by construction. -/
theorem allocated_packet_header_runWith (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc reg 32 routines)
    (S : SiteData R r reg 32 w a)
    (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : fitsWith physical reg 32 r w a R link n e) (u : Fin (R+1)) (pin : Fin d → Bool)
    (L : WireLayout (R+1) r link) (bits : List Bool) (length : bits.length = L.header)
    (payload : Fin (R+1) → Fin (R+1) → ℕ → Bool)
    (ibase hbase frameBase dense dst : Fin (R+1) → ℕ) (mac : TeamOpcode.Macros w 8) (s : Bank w) :
    let G₀ := wiringWith physical P S d link n e fit
    let A := fun v => (⟨adviceOffsetWith physical r 32 reg w n,(pack v).bits.length,dense v⟩ : AdviceLayout)
    let star := fun v => dense v + (pack v).offset
    let B := fun v => operandsAtSite G₀ v (ibase v) (hbase v) (star v) (frameBase v) L.header (dst v) (A v) (pack v)
    let T := S.withOperands B
    let G := wiringWith physical P (T.withPacket pack) d link n e fit
    let F := G.processorFields u pin (exterior L bits length payload) (ibase u) (hbase u) (star u)
    let f := G.transferFrame u L.header (dst u)
    let pub := T.publicWords u
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord w F.header)
    (B u).Fits w → f.Fits w (frameBase u) → (A u).Fits f w (frameBase u) →
    ExtendedFrame.Fits w (frameBase u) (dense u) (pack u).entry.length →
    frameBase u+112 ≤ dst u → (dense u+(pack u).bits.length ≤ dst u ∨ dst u+L.header ≤ dense u) →
    ∃ es t mt, Runs pub mac bootHeader s initial es t mt ∧
      traceCost es ≤ jointBudget (pack u).bits.length w + f.readTicks ∧
      (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧
      BootHeaderState F f (A u) (pack u) pub bits t mt := by
  intro G₀ A star B T G F f pub initial bound room advice extended above apart
  have base : (pub 0).val = frameBase u := (B u).frameBase_word (S.publicWords u) bound
  have scalar := (B u).packetFrame (S.publicWords u) bound
  apply packet_header_runWith physical P T pack link n e fit u pin L bits length payload (ibase u) (hbase u) (star u)
    (dst u) pub mac s (A u) scalar
  · exact base.symm ▸ room
  · exact base.symm ▸ advice
  · exact base.symm ▸ extended
  · rfl
  · exact le_rfl
  · rfl
  · exact base.symm ▸ above
  · exact apart

/-- The ordinary signed processor instance of the physical packet header result. -/
theorem allocated_packet_header_run (P : TeamOpcode.Program pc reg 32 routines)
    (lib : Fin routines → TeamSite.Macro Q Γ m g) (S : SiteData R r reg 32 w a)
    (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : Fits P lib r w a R link n e) (u : Fin (R+1)) (pin : Fin d → Bool)
    (L : WireLayout (R+1) r link) (bits : List Bool) (length : bits.length = L.header)
    (payload : Fin (R+1) → Fin (R+1) → ℕ → Bool)
    (ibase hbase frameBase dense dst : Fin (R+1) → ℕ) (mac : TeamOpcode.Macros w 8) (s : Bank w) :
    let G₀ := wiring P lib S d link n e fit
    let A := fun v => (⟨adviceOffset P lib r w n,(pack v).bits.length,dense v⟩ : AdviceLayout)
    let star := fun v => dense v + (pack v).offset
    let B := fun v => operandsAtSite G₀ v (ibase v) (hbase v) (star v) (frameBase v) L.header (dst v) (A v) (pack v)
    let T := S.withOperands B
    let G := wiring P lib (T.withPacket pack) d link n e fit
    let F := G.processorFields u pin (exterior L bits length payload) (ibase u) (hbase u) (star u)
    let f := G.transferFrame u L.header (dst u)
    let pub := T.publicWords u
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord w F.header)
    (B u).Fits w → f.Fits w (frameBase u) → (A u).Fits f w (frameBase u) →
    ExtendedFrame.Fits w (frameBase u) (dense u) (pack u).entry.length →
    frameBase u+112 ≤ dst u → (dense u+(pack u).bits.length ≤ dst u ∨ dst u+L.header ≤ dense u) →
    ∃ es t mt, Runs pub mac bootHeader s initial es t mt ∧
      traceCost es ≤ jointBudget (pack u).bits.length w + f.readTicks ∧
      (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧
      BootHeaderState F f (A u) (pack u) pub bits t mt :=
  allocated_packet_header_runWith (TeamSite.Processor.machine P lib) P S pack link n e fit u pin L bits length payload
    ibase hbase frameBase dense dst mac s

end TeamContraction.JointHeader

end BorderVNP
end Computability
end OAI
