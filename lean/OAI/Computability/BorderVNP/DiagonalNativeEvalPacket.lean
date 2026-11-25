import OAI.Computability.BorderVNP.DiagonalNativeBudgetValue
import OAI.Computability.BorderVNP.TransmissionJointPacket

/-! # The evaluation tag on the genuine joint-packet processor header

After the fixed boot, literal gathering and extended-frame decode, the common tag is
read from the true shared exterior input. A disagreeing broadcast has no native paths.
A common positive tag invokes the evaluation branch with its true remaining clock.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator
open scoped BigOperators Classical
open private linked_iff withoutAccept from OAI.Computability.BorderVNP.DiagonalNativeUnitStartup
open private copied_pinFrame from OAI.Computability.BorderVNP.DiagonalNativeBroadcastUnit

variable {R r t d link inner n w : ℕ} {Edge : Type}

/-- The physical broadcast setup sees the same real exterior words as the initialized
processor header, and every reference word in its prefix is a genuine bit. -/
theorem Wiring.broadcast_input (G : Wiring R r t d link inner n Edge) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase header dst : ℕ)
    (m : Memory w) (physical : (G.processorFields u pin ext ibase hbase starbase).ContainsInput m)
    {base : ℕ} (fit : (G.transferFrame u header dst).Fits w base) :
    let f := G.transferFrame u header dst
    let F := G.processorFields u pin ext ibase hbase starbase
    f.ReferenceBits (readings m) ∧ ∀ v < f.teams, v ≠ f.team → ∀ j < f.capacity,
      readings m (f.addr v j) = readings (processorMemory F w) (f.addr v j) := by
  intro f F
  have hw : 0 < w := by
    by_contra! hz
    obtain rfl := Nat.eq_zero_of_le_zero hz
    have := fit.frame
    have := fit.out
    simp at *; omega
  have hp := f.partner_spec fit.three
  let partner : Fin (R+1) := ⟨f.partner,hp.2⟩
  have ne : u ≠ partner := fun he => hp.1 (congrArg Fin.val he.symm)
  refine ⟨?_,?_⟩
  · intro j hj
    have h := hj.trans_le fit.cap
    let pos : Fin (r*link) := ⟨j,by simpa [Wiring.transferFrame,BroadcastFrame.capacity,Nat.mul_comm] using h⟩
    exact (G.read_exterior_val hw u partner ne pin ext ibase hbase starbase m physical pos).trans_lt (Bool.toNat_lt _)
  · intro v hv hd j hj
    let v' : Fin (R+1) := ⟨v,hv⟩
    have hne : u ≠ v' := fun he => hd (congrArg Fin.val he.symm)
    let pos : Fin (r*link) := ⟨j,by simpa [f,Wiring.transferFrame,BroadcastFrame.capacity,Nat.mul_comm] using hj⟩
    exact (G.read_exterior_val hw u v' hne pin ext ibase hbase starbase m physical pos).trans
      (G.read_exterior_val hw u v' hne pin ext ibase hbase starbase (processorMemory F w) (F.containsInput_initial w) pos).symm

namespace ProcessorSlots

variable {pc reg k routines m g R r w a d : ℕ} {Q Γ : Type} [Fintype Q]
variable (physical : VPVNP.UniversalMachine.Program)
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
variable (S : SiteData R r reg k w a)

set_option maxRecDepth 4000 in
/-- The fully initialized evaluator either rejects a disagreeing physical broadcast or
continues from the actual post-copy state. On tag one, the value is the evaluation
body's finite signed path sum at the exact residual clock. The unchanged physical inputs,
preserved scalar fields and copy of the header are available for that continuation. -/
theorem jointPacket_eval_valueCoreWith (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : fitsWith physical reg k r w a R link n e) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (header dst ibase hbase starbase : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (A : AdviceLayout)
    (eval : Code) (he : eval.withoutAccept = true) (ticks burst clock : ℕ) :
    let G := wiringWith physical P (S.withPacket pack) d link n e fit
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let f := G.transferFrame u header dst
    let p := pack u
    let initial := processorMemory F w
    let value := nativeValue (processorMachine (withStartup eval) pub mac s F) ticks burst clock
    PacketFrame L f A p.entry.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val → A.Fits f w (pub 0).val → ExtendedFrame.Fits w (pub 0).val A.dst p.entry.length →
    A.offset = adviceOffsetWith physical r k reg w n → p.bits.length ≤ A.count → starbase = A.dst+p.offset →
    readings initial (f.addr f.partner 0) ≠ 0 →
    jointBudget A.count w + f.readTicks + 2 ≤ ticks →
    (¬ f.Agrees (readings initial) → value = 0) ∧
    (f.Agrees (readings initial) → ∃ used b mb,
      used ≤ jointBudget A.count w + f.readTicks + 2 ∧ F.ContainsInput mb ∧
      Frame L (readings pub) (readings mb) ∧
      (∀ j < header, readings mb (dst+j) = readings initial (f.addr f.partner j)) ∧
      (∃ booted, PacketFrame L f A p.entry.length w (readings pub) (readings booted) ∧
        (∀ i : Fin 81, booted ((pub 0).val+31+i.val) = p.extension i) ∧
        DiagonalTallyBits.WordsAt booted A.dst (p.entry.map wordBits) ∧
        (∀ i : Fin d, booted (starbase+i.val) = TeamTapeInputEmit.word w (p.reference i).toNat) ∧
        (∀ i : Fin 31, booted ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1))) ∧
        readings mb = f.copied (readings booted) f.header) ∧
      value = boundedValue eval pub mac b mb (ticks-used) burst clock) := by
  intro G L F f p initial value scalar fits adv ex off count star one allowance
  obtain ⟨pre,z,mz,start,ct,_,phys,packet,extended,entry,ref,core⟩ := jointPacket_run_coreWith physical P S pack link n e fit u
    pin ext ibase hbase starbase pub mac s f A scalar fits adv ex off count star
  obtain ⟨bits,real⟩ := G.broadcast_input u pin ext ibase hbase starbase header dst mz phys fits
  have partner := f.partner_spec fits.three
  have eq (v : ℕ) (hv : v < f.teams) (hd : v ≠ f.team) (i : ℕ) (hi : i < f.header) :=
    real v hv hd i (hi.trans_le fits.cap)
  have agrees : f.Agrees (readings mz) ↔ f.Agrees (readings initial) :=
    forall_congr' fun v => forall_congr' fun hv => forall_congr' fun hd =>
      forall_congr' fun i => forall_congr' fun hi => by rw [eq v hv hd i hi,eq _ partner.2 partner.1 i hi]
  have test := readBroadcast_test f pub mac z mz packet.broadcast fits bits
  constructor
  · intro bad
    have empty : IsEmpty (NativePath (processorMachine (withStartup eval) pub mac s F) ticks burst clock) := by
      constructor
      intro x
      obtain ⟨⟨b,mb,r⟩,_⟩ := (Code.execute_iff_runs (withoutAccept he)).mp x.property.1
      obtain ⟨_,_,_,_,_,first,tail⟩ := Runs.seq_iff.mp (linked_iff.mp r)
      obtain ⟨_,rfl,rfl⟩ := start.unique_of_deterministic (by decide) first
      obtain ⟨_,_,_,_,_,bc,_⟩ := Runs.seq_iff.mp tail
      exact bad (agrees.mp (test.sound bc).1)
    simp [value,nativeValue]
  · intro good
    obtain ⟨hs,b,mb,bc,cap,stable,copy⟩ := test.complete (agrees.mpr good)
    change readings mb = f.copied (readings mz) f.header at copy
    have dest (j : ℕ) (hj : j < f.header) : readings mb (f.dst+j) = readings initial (f.addr f.partner j) := by
      rw [copy,f.copied_at _ hj,eq _ partner.2 partner.1 j hj]
    have nonzero : (mb f.dst).val ≠ 0 := by
      have h := dest 0 fits.branch
      simpa only [Nat.add_zero,readings] using h.trans_ne one
    have used : pre.length+hs.length+2 ≤ jointBudget A.count w + f.readTicks + 2 := by
      have pLen := start.deterministic_cost (by decide)
      have bLen := bc.deterministic_cost (by decide)
      omega
    have fh : F.header.length ≤ (pub 0).val := by
      rw [F.header_length,scalar.input_extent]
      exact fits.input
    have live : F.ContainsInput mb := by
      intro a ha
      have before : a < f.dst := (ha.trans_le fh).trans_le (by have := fits.frame; omega)
      apply Fin.ext
      change readings mb a = _
      rw [copy,f.copied_before _ _ _ before]
      exact congrArg Fin.val (phys a ha)
    have frame : Frame L (readings pub) (readings mb) := copy ▸ copied_pinFrame f L fits packet.pins
    refine ⟨pre.length+hs.length+2, Function.update b 10 (mb f.dst), mb, used, live, frame, dest,
      ⟨mz,packet,extended,entry,ref,core,copy⟩,?_⟩
    have val := startup_selected_value f eval F s start bc stable he ticks burst clock (used.trans allowance)
    simpa only [selected,ite_eq_right nonzero] using val

/-- The same signed native value with the selected pin and certificate readback. -/
theorem jointPacket_eval_valueWith (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : fitsWith physical reg k r w a R link n e) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (header dst ibase hbase starbase : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (A : AdviceLayout)
    (eval : Code) (he : eval.withoutAccept = true) (ticks burst clock : ℕ) :
    let G := wiringWith physical P (S.withPacket pack) d link n e fit
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let f := G.transferFrame u header dst
    let p := pack u
    let initial := processorMemory F w
    let value := nativeValue (processorMachine (withStartup eval) pub mac s F) ticks burst clock
    PacketFrame L f A p.entry.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val → A.Fits f w (pub 0).val → ExtendedFrame.Fits w (pub 0).val A.dst p.entry.length →
    A.offset = adviceOffsetWith physical r k reg w n → p.bits.length ≤ A.count → starbase = A.dst+p.offset →
    readings initial (f.addr f.partner 0) ≠ 0 →
    jointBudget A.count w + f.readTicks + 2 ≤ ticks →
    (¬ f.Agrees (readings initial) → value = 0) ∧
    (f.Agrees (readings initial) → ∃ used b mb,
      used ≤ jointBudget A.count w + f.readTicks + 2 ∧ F.ContainsInput mb ∧
      Frame L (readings pub) (readings mb) ∧
      (∀ j < header, readings mb (dst+j) = readings initial (f.addr f.partner j)) ∧
      (∃ booted, PacketFrame L f A p.entry.length w (readings pub) (readings booted) ∧
        (∀ i : Fin 81, booted ((pub 0).val+31+i.val) = p.extension i) ∧
        DiagonalTallyBits.WordsAt booted A.dst (p.entry.map wordBits) ∧
        (∀ i : Fin d, booted (starbase+i.val) = TeamTapeInputEmit.word w (p.reference i).toNat) ∧
        readings mb = f.copied (readings booted) f.header) ∧
      value = boundedValue eval pub mac b mb (ticks-used) burst clock) := by
  intro G L F f p initial value scalar fits adv ex off count star one allowance
  have full := jointPacket_eval_valueCoreWith physical P S pack link n e fit u pin ext header dst ibase hbase starbase
    pub mac s A eval he ticks burst clock scalar fits adv ex off count star one allowance
  refine ⟨full.1,fun good => ?_⟩
  obtain ⟨used,b,mb,cap,inp,frame,dest,⟨booted,pf,ef,entry,ref,_,copy⟩,result⟩ := full.2 good
  exact ⟨used,b,mb,cap,inp,frame,dest,⟨booted,pf,ef,entry,ref,copy⟩,result⟩

/-- The ordinary signed processor instance of the program-indexed result. -/
theorem jointPacket_eval_value (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : Fits P lib r w a R link n e) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (header dst ibase hbase starbase : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (A : AdviceLayout)
    (eval : Code) (he : eval.withoutAccept = true) (ticks burst clock : ℕ) :
    let G := wiring P lib (S.withPacket pack) d link n e fit
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let f := G.transferFrame u header dst
    let p := pack u
    let initial := processorMemory F w
    let value := nativeValue (processorMachine (withStartup eval) pub mac s F) ticks burst clock
    PacketFrame L f A p.entry.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val → A.Fits f w (pub 0).val → ExtendedFrame.Fits w (pub 0).val A.dst p.entry.length →
    A.offset = adviceOffset P lib r w n → p.bits.length ≤ A.count → starbase = A.dst+p.offset →
    readings initial (f.addr f.partner 0) ≠ 0 →
    jointBudget A.count w + f.readTicks + 2 ≤ ticks →
    (¬ f.Agrees (readings initial) → value = 0) ∧
    (f.Agrees (readings initial) → ∃ used b mb,
      used ≤ jointBudget A.count w + f.readTicks + 2 ∧ F.ContainsInput mb ∧
      Frame L (readings pub) (readings mb) ∧
      (∀ j < header, readings mb (dst+j) = readings initial (f.addr f.partner j)) ∧
      (∃ booted, PacketFrame L f A p.entry.length w (readings pub) (readings booted) ∧
        (∀ i : Fin 81, booted ((pub 0).val+31+i.val) = p.extension i) ∧
        DiagonalTallyBits.WordsAt booted A.dst (p.entry.map wordBits) ∧
        (∀ i : Fin d, booted (starbase+i.val) = TeamTapeInputEmit.word w (p.reference i).toNat) ∧
        readings mb = f.copied (readings booted) f.header) ∧
      value = boundedValue eval pub mac b mb (ticks-used) burst clock) :=
  jointPacket_eval_valueWith (TeamSite.Processor.machine P lib) P S pack link n e fit u pin ext header dst ibase hbase starbase
    pub mac s A eval he ticks burst clock

end ProcessorSlots
end TeamContraction

end BorderVNP
end Computability
end OAI
