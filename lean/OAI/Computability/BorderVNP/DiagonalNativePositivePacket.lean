import OAI.Computability.BorderVNP.DiagonalJointPositiveProgram
import OAI.Computability.BorderVNP.DiagonalNativeRootProduct
import OAI.Computability.BorderVNP.DiagonalNativeTimedModes
import OAI.Computability.BorderVNP.TransmissionPinsComplete

/-! # Positive teams at the actual post-broadcast signed packet state -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator RoutingISA.CompactMachine
open BorderVNP.Cube CellMacro.Generator

variable {dim box lanes selectors symbols w d : ℕ}

/-- Boot information carried into the positive program. The 31 scalar words,
81 extension words, packed entry circuit, reference index and copied common header
all come from the executed startup on the original processor fields. -/
structure PositivePacketBoot (L : Layout) (F : ProcessorFields L) (f : BroadcastFrame)
    (p : ReferencePacket w d) (pub : Arg → Word w) (a : UnitAddresses)
    (initial : Memory w) (used : ℕ) (saved : Memory w) : Prop where
  spent : used ≤ jointBudget a.advice.count w+f.readTicks+2
  input : F.ContainsInput saved
  frame : Frame L (readings pub) (readings saved)
  copied : ∀ j < a.header, readings saved (a.dst+j) = readings initial (f.addr f.partner j)
  packet : ∃ m, PacketFrame L f a.advice p.entry.length w (readings pub) (readings m) ∧
    (∀ i : Fin 81, m ((pub 0).val+31+i.val) = p.extension i) ∧
    DiagonalTallyBits.WordsAt m a.advice.dst (p.entry.map wordBits) ∧
    (∀ i : Fin d, m (a.starbase+i.val) = TeamTapeInputEmit.word w (p.reference i).toNat) ∧
    (∀ i : Fin 31, m ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1))) ∧
    readings saved = f.copied (readings m) f.header

/-- Exact cost, choice spelling and scratch memory of every true substituted pin
return used for the positive team's prefix dictionary. -/
def PositivePinOutputs {k : ℕ} (L : Layout) {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s : Bank w} {m : Memory w} (E : (Fin k → Bool) ≃ Pins.Return pub mac s m) : Prop :=
  ∀ b, (E b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b ∧
    traceCost (E b).val.1 ≤ pinSetup.slots+17*L.count+1 ∧
    (∀ e ∈ (E b).val.1, e.sign = .plus) ∧ Ready L L.count (E b).val.2.1 ∧
    (E b).val.2.2 = preparedMemory L (extendGuess b) m L.count

/-- Measured continuation evidence on the actual startup and pin state. -/
structure PositiveContinuation (id : TableEntry dim box lanes selectors symbols → ℕ) (gen : Fragment IO)
    (n : ℕ) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    {k : ℕ} (E : (Fin k → Bool) ≃ Pins.Return pub (install gen n mac) s m) (used limit : ℕ) where
  /-- Packed private inputs on the true native directory. -/
  cells : ∀ b (p : SignedPreps id pub mac gen n s m E b), GeneratedCells gen n pub p.val.2.2
  /-- Actual allocation of all rows read by private cell calls. -/
  room : ∀ b (p : SignedPreps id pub mac gen n s m E b), let f := CellDispatch.Frame.ofMemory pub p.val.2.2
    f.base+3*f.count ≤ 2^w
  /-- The real phase costs fit the original cutoff with the startup already charged. -/
  window : SignedStageWindow id pub mac gen n s m E used limit

/-- Every agreeing positive tag selects a real positive team, including when its
bounded body has signed value zero. The pin bijection is constructed by executing the
native pin code; the continuation evidence is evaluated in precisely this saved state. -/
theorem positiveMasked_team (physical : UniversalMachine.Program) {R r a link n e : ℕ}
    (id : TableEntry dim box lanes selectors symbols → ℕ) (gen : Fragment IO)
    (S : SiteData R r 64 32 w a) (pack : Fin (R+1) → ReferencePacket w d)
    (fit : fitsWith physical 64 32 r w a R link n e) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (u : Fin (R+1))
    (cap : TeamScales.width n (1/2) ≤ S.burst.val) :
    let P := (withStartup (signedBody id)).program
    let G := wiringWith physical P (S.withPacket pack) d link n e fit
    let ad := args u
    let f := G.transferFrame u ad.header ad.dst
    let L := G.pinLayout u ad.ibase ad.hbase ad.starbase
    let F := G.processorFields u pin ext ad.ibase ad.hbase ad.starbase
    let pub := S.publicWords u
    let initial := processorMemory F w
    let mac := TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)
    ad.Fitted G u (pack u) pub (adviceOffsetWith physical r 32 64 w n) →
    jointBudget ad.advice.count w+f.readTicks+2 ≤ S.limit.val →
    LoopFits w L → modeTag (w := w) G args pin ext u ≠ 0 → f.Agrees (readings initial) →
    (∀ used b mb, PositivePacketBoot L F f (pack u) pub ad initial used mb →
      ∀ pins : (Fin L.guessWidth → Bool) ≃ Pins.Return pub (install gen n mac) b mb,
      PositivePinOutputs L pins → Nonempty (PositiveContinuation id gen n pub mac b mb pins used S.limit.val)) →
    ∃ T : PositiveTeam id gen n w,
      T.pub = pub ∧ T.routines = mac ∧ T.limit = S.limit.val ∧ T.burst = S.burst.val ∧
      T.guessWidth = L.guessWidth ∧ PositivePinOutputs L T.pins ∧
      PositivePacketBoot L F f (pack u) pub ad initial T.used T.memory ∧
      positiveMaskedNativeValue G (signedBody id) mac S.publicWords S.registers args pin S.limit.val
        S.burst.val (n^25) ext u =
        boundedValue (signedBody id) T.pub (install gen n T.routines) T.bank T.memory (T.limit-T.used) T.burst (n^25) := by
  intro P G ad f L F pub initial mac ready time fits tag good stages
  have replay := jointPacket_eval_valueCoreWith physical P S pack link n e fit u pin ext ad.header ad.dst
    ad.ibase ad.hbase ad.starbase pub mac (S.registers u) ad.advice (signedBody id) (signedBody_withoutAccept id)
    S.limit.val S.burst.val (n^25) ready.operands ready.physical ready.gather ready.extended
    ready.literalOffset ready.packet ready.reference tag time
  obtain ⟨used,b,mb,cost,input,frame,copy,packet,eq⟩ := replay.2 good
  have boot : PositivePacketBoot L F f (pack u) pub ad initial used mb := ⟨cost,input,frame,copy,packet⟩
  obtain ⟨stride,count,width,_⟩ := ready.pinRoom
  have regRoom : readings pub 0+24 < 2^w := by
    have before := ready.physical.frame
    have after := ready.physical.out
    change (pub 0).val+31 ≤ f.dst at before
    change f.dst+f.header < 2^w at after
    change (pub 0).val+24 < 2^w
    omega
  obtain ⟨pins,outputs⟩ := preparePins_exact L pub (install gen n mac) mb b frame regRoom
    (show 0<L.teams by change 0<R+1; omega) stride count width fits
  obtain ⟨c⟩ := stages used b mb boot pins outputs
  let T : PositiveTeam id gen n w :=
    ⟨pub,mac,b,mb,L.guessWidth,pins,used,S.limit.val,S.burst.val,cap,by change (pub 0).val+24 < 2^w at regRoom; omega,
      c.room,c.cells,c.window⟩
  refine ⟨T,rfl,rfl,rfl,rfl,rfl,outputs,boot,?_⟩
  rw [positiveMaskedNativeValue,ite_eq_right tag]
  change packetNative G (signedBody id) mac S.publicWords S.registers args pin S.limit.val S.burst.val (n^25) ext u =
    boundedValue (signedBody id) pub (install gen n mac) b mb (S.limit.val-used) S.burst.val (n^25)
  have installed : mac = install gen n mac := siteLibrary_installed gen n
  rw [← installed]
  exact eq

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
