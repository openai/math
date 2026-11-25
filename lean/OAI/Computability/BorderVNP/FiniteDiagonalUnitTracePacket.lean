import OAI.Computability.BorderVNP.FiniteDiagonalUnitTraceLocal

/-! # Accepted unit traces from the assembled physical input

The boot, literal-advice gather, reference-column lookup, broadcast and zero-tag
selector yield the exact local trace fiber. Private returns may take any field value.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator
open scoped Classical

variable {w R r t d link inner n m g : ℕ} {Edge Q Γ : Type} {K : Type*} [Field K]
    (G : Wiring R r t d link inner n Edge) (u : Fin (R+1)) (pin advised : Fin d → Bool)
    (ext : Exterior R r link → Bool) (header dst ibase hbase starbase : ℕ)

/-- At a physically selected unit tag the full table has precisely the path for
the incident link and column tests, and its field weight is one. -/
theorem Wiring.startup_unit_trace (pub : Arg → Word w)
    (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : FieldProcessor.Returns Q Γ K m 8)
    (fuel : ℕ) (s : Bank w)
    (eval : Code) (fallsThrough : eval.withoutAccept = true) (ct ticks burst clock : ℕ) :
    let mac := TeamSiteEvents.macros lib fuel
    let f := G.transferFrame u header dst
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let initial := processorMemory F w
    ∀ {es a ma}, Runs pub mac unitStartup s initial es a ma → traceCost es ≤ ct →
      F.ContainsInput ma → (∀ i : Fin d, ma (starbase+i.val) = TeamTapeInputEmit.word w (advised i).toNat) →
      f.At (readings pub) (readings ma) → Frame L (readings pub) (readings ma) → f.Fits w (pub 0).val →
      readings initial (f.addr f.partner 0) = 0 → L.stride < 2^w → L.count < 2^w → L.width ≤ L.count →
      (L.starbase+L.width ≤ f.dst ∨ f.dst+f.header ≤ L.starbase) → (L.team = 0 → IdentityFits L w) →
      ct+(f.readTicks+(2+unitBudget f L)) ≤ ticks →
      let M := processorMachine (withStartup eval) pub mac s F
      Nonempty (NativePath M ticks burst clock ≃ PLift (LocalUnit u pin advised ext)) ∧
        ∀ path : NativePath M ticks burst clock,
          FieldProcessor.pathProduct (withStartup eval).program pub lib ret fuel ⟨0,s⟩ path.val = 1 := by
  intro mac f L F initial es a ma startRun cost physical reference image frame fit initZero hs hc room apart pins tickFit
  have hw : 0 < w := by by_contra! hz; obtain rfl := Nat.eq_zero_of_le_zero hz; have := fit.frame; have := fit.out; simp at *; omega
  have partner := f.partner_spec fit.three
  let v : Fin (R+1) := ⟨f.partner,partner.2⟩
  have ne : u ≠ v := fun eq => partner.1 (congrArg Fin.val eq.symm)
  have bits : f.ReferenceBits (readings ma) := by
    intro j hj
    have cap := hj.trans_le fit.cap
    let pos : Fin (r*link) := ⟨j,by simpa [f,Wiring.transferFrame,BroadcastFrame.capacity,Nat.mul_comm] using cap⟩
    exact (G.read_exterior_val hw u v ne pin ext ibase hbase starbase ma physical pos).trans_lt (Bool.toNat_lt _)
  have zero : readings ma (f.addr f.partner 0) = 0 := by
    have hi := f.addr_lt_input fit partner.2 partner.1 (fit.branch.trans_le fit.cap)
    have lt : f.addr f.partner 0 < F.header.length := by
      rw [F.header_length]
      simpa [f,F,Wiring.transferFrame,Wiring.pinLayout,Layout.stride,Layout.offset,BroadcastFrame.stride,
        Nat.two_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hi
    exact (congrArg Fin.val ((physical _ lt).trans ((F.containsInput_initial w) _ lt).symm)).trans initZero
  have check := startup_unit_test f L eval startRun cost image fit bits zero frame hs hc room apart pins
  have logical := check.mono le_rfl (G.unitTest_iff u pin advised ext header dst ibase hbase starbase
    ma physical reference hw room) (fun _ h => h)
  exact FiniteDiagonal.unitTrace_of_test F pub s eval fallsThrough lib ret fuel tickFit logical
    (fun run => (startup_zero_runs_iff f eval startRun image fit bits zero).mp run)

end TeamContraction

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator
open scoped Classical

variable {pc reg k routines m g R r w a d : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
variable (S : SiteData R r reg k w a)

/-- A genuine advised packet on the zero tag produces the complete local unit trace
index and its exact multiplicative field weight. -/
theorem jointPacket_unit_trace (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : Fits P lib r w a R link n e) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (header dst ibase hbase starbase : ℕ)
    (pub : Arg → Word w) {Q' Γ' : Type} {K : Type*} [Field K] {m' g' : ℕ}
    (nativeLib : Fin 8 → TeamSite.Macro Q' Γ' m' g') (ret : FieldProcessor.Returns Q' Γ' K m' 8)
    (fuel : ℕ) (s : Bank w) (A : AdviceLayout)
    (eval : Code) (fallsThrough : eval.withoutAccept = true) (ticks burst clock : ℕ) :
    let mac := TeamSiteEvents.macros nativeLib fuel
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
    let M := processorMachine (withStartup eval) pub mac s F
    Nonempty (NativePath M ticks burst clock ≃ PLift (LocalUnit u pin p.reference ext)) ∧
      ∀ path : NativePath M ticks burst clock,
        FieldProcessor.pathProduct (withStartup eval).program pub nativeLib ret fuel ⟨0,s⟩ path.val = 1 := by
  intro mac G L F f p scalar physical advice extended off count star zero stride cap room apart pins allowance
  obtain ⟨es,b,mb,run,cost,_,input,frame,_,_,ref⟩ := jointPacket_run P lib S pack link n e fit u
    pin ext ibase hbase starbase pub mac s f A scalar physical advice extended off count star
  exact G.startup_unit_trace u pin p.reference ext header dst ibase hbase starbase pub nativeLib ret fuel s eval
    fallsThrough (jointBudget A.count w) ticks burst clock run cost input ref frame.broadcast frame.pins
    physical zero stride cap room apart (fun eq => pins (Fin.ext eq)) allowance

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
