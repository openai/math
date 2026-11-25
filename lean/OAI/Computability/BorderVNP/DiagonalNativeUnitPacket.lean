import OAI.Computability.BorderVNP.TransmissionJointPacket

/-! # The charged unit contribution on the fully initialized, advised processor table

The literals determine the native advice packet and H*. The reference tag in the
original processor input determines the branch. All execution and memory facts needed
by the value theorem are supplied by the actual boot, literal gather and decoder.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator
open scoped Classical

variable {pc reg k routines m g R r w a d : ℕ} {Q Γ : Type} [Fintype Q]
variable (physical : VPVNP.UniversalMachine.Program)
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
variable (S : SiteData R r reg k w a)

/-- The total charged tick allowance of the real packet reader, broadcast, selector
and physical unit test. -/
def packetUnitBudget (count w : ℕ) (f : BroadcastFrame) (L : Layout) : ℕ :=
  jointBudget count w + (f.readTicks+(2+unitBudget f L))

/-- The native value of the complete assembled table, on the unit tag of the wired
processor input, is one precisely for a zero incident exterior assignment with the
correct live column on its owner. All other traces contribute zero. -/
theorem jointPacket_unit_valueWith (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : fitsWith physical reg k r w a R link n e) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (header dst ibase hbase starbase : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (A : AdviceLayout)
    (eval : Code) (fallsThrough : eval.withoutAccept = true) (ticks burst clock : ℕ) :
    let G := wiringWith physical P (S.withPacket pack) d link n e fit
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let f := G.transferFrame u header dst
    let p := pack u
    PacketFrame L f A p.entry.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val → A.Fits f w (pub 0).val →
    ExtendedFrame.Fits w (pub 0).val A.dst p.entry.length →
    A.offset = adviceOffsetWith physical r k reg w n → p.bits.length ≤ A.count → starbase = A.dst+p.offset →
    readings (processorMemory F w) (f.addr f.partner 0) = 0 →
    L.stride < 2^w → L.count < 2^w → L.width ≤ L.count →
    (starbase+d ≤ dst ∨ dst+header ≤ starbase) → (u = 0 → IdentityFits L w) →
    packetUnitBudget A.count w f L ≤ ticks →
    nativeValue (processorMachine (withStartup eval) pub mac s F) ticks burst clock =
      if LocalUnit u pin p.reference ext then 1 else 0 := by
  intro G L F f p scalar physRoom advice extended off count star zero stride cap room apart pins allowance
  obtain ⟨es,b,mb,run,cost,_,input,frame,_,_,ref⟩ := jointPacket_runWith physical P S pack link n e fit u
    pin ext ibase hbase starbase pub mac s f A scalar physRoom advice extended off count star
  exact G.startup_unit_value u pin p.reference ext header dst ibase hbase starbase pub mac s eval
    fallsThrough (jointBudget A.count w) ticks burst clock run cost input ref frame.broadcast frame.pins
    physRoom zero stride cap room apart (fun eq => pins (Fin.ext eq)) allowance

/-- The ordinary signed processor instance of the program-indexed result. -/
theorem jointPacket_unit_value (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : Fits P lib r w a R link n e) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (header dst ibase hbase starbase : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (A : AdviceLayout)
    (eval : Code) (fallsThrough : eval.withoutAccept = true) (ticks burst clock : ℕ) :
    let G := wiring P lib (S.withPacket pack) d link n e fit
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let f := G.transferFrame u header dst
    let p := pack u
    PacketFrame L f A p.entry.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val → A.Fits f w (pub 0).val →
    ExtendedFrame.Fits w (pub 0).val A.dst p.entry.length →
    A.offset = adviceOffset P lib r w n → p.bits.length ≤ A.count → starbase = A.dst+p.offset →
    readings (processorMemory F w) (f.addr f.partner 0) = 0 →
    L.stride < 2^w → L.count < 2^w → L.width ≤ L.count →
    (starbase+d ≤ dst ∨ dst+header ≤ starbase) → (u = 0 → IdentityFits L w) →
    packetUnitBudget A.count w f L ≤ ticks →
    nativeValue (processorMachine (withStartup eval) pub mac s F) ticks burst clock =
      if LocalUnit u pin p.reference ext then 1 else 0 :=
  jointPacket_unit_valueWith (TeamSite.Processor.machine P lib) P S pack link n e fit u pin ext header dst ibase hbase starbase
    pub mac s A eval fallsThrough ticks burst clock

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
