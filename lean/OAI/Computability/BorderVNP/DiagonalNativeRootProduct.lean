import OAI.Computability.BorderVNP.DiagonalNativeSignedWindow
import OAI.Computability.BorderVNP.DiagonalNativeEvalPacket
import OAI.Computability.BorderVNP.DiagonalNativeSiteMacro

/-! # The positive common-tag branch on the actual physical signed processor input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM UniversalMachine RoutingISA RoutingISA.Pins RoutingISA.Evaluator RoutingISA.CompactMachine
open BorderVNP.Cube BorderVNP.Cube.Tally CellMacro.Generator
open scoped BigOperators Classical

variable {dim box lanes selectors symbols R r w a d : ℕ}
variable (physical : Program) (id : TableEntry dim box lanes selectors symbols → ℕ)
variable (S : SiteData R r 64 32 w a) (pack : Fin (R+1) → ReferencePacket w d)

/-- On a common positive exterior tag, the fully initialized signed processor reduces at its
true remaining clock to the product of actual packed cell weights and the staged residue value.
The continuation has the copied common header, both live pin and reference banks, and all
81 extended words available for certifying its actual directory and phase charges. -/
theorem jointPacket_signed_productWith (link n e : ℕ) (fit : fitsWith physical 64 32 r w a R link n e)
    (u : Fin (R+1)) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (header dst ibase hbase starbase : ℕ) (pub : Arg → Word w) (s : Bank w) (A : AdviceLayout)
    (gen : Fragment IO) (limit burst : ℕ) (hn : 1 ≤ n) (cap : TeamScales.width n (1/2) ≤ burst) :
    let P := (signedProgram id).program
    let mac := TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)
    let G := wiringWith physical P (S.withPacket pack) d link n e fit
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let f := G.transferFrame u header dst
    let p := pack u
    let initial := processorMemory F w
    let value := nativeValue (processorMachine (signedProgram id) pub mac s F) limit burst (n^25)
    PacketFrame L f A p.entry.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val → A.Fits f w (pub 0).val → ExtendedFrame.Fits w (pub 0).val A.dst p.entry.length →
    A.offset = adviceOffsetWith physical r 32 64 w n → p.bits.length ≤ A.count → starbase = A.dst+p.offset →
    readings initial (f.addr f.partner 0) ≠ 0 → jointBudget A.count w + f.readTicks+2 ≤ limit →
    f.Agrees (readings initial) → ∃ used b mb,
      used ≤ jointBudget A.count w + f.readTicks+2 ∧ F.ContainsInput mb ∧
      Frame L (readings pub) (readings mb) ∧
      (∀ j < header, readings mb (dst+j) = readings initial (f.addr f.partner j)) ∧
      (∃ booted, PacketFrame L f A p.entry.length w (readings pub) (readings booted) ∧
        (∀ i : Fin 81, booted ((pub 0).val+31+i.val) = p.extension i) ∧
        DiagonalTallyBits.WordsAt booted A.dst (p.entry.map wordBits) ∧
        (∀ i : Fin d, booted (starbase+i.val) = TeamTapeInputEmit.word w (p.reference i).toNat) ∧
        (∀ i : Fin 31, booted ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1))) ∧
        readings mb = f.copied (readings booted) f.header) ∧
      ∀ {k : ℕ} (pins : (Fin k → Bool) ≃ Pins.Return pub (install gen n mac) b mb)
        (window : SignedStageWindow id pub mac gen n b mb pins used limit),
        letI (i : Fin k → Bool) := @Fintype.ofFinite (SignedPreps id pub mac gen n b mb pins i)
          (window.preparationFinite id pub mac gen n b mb pins i)
        ∀ (C : ∀ i (prep : SignedPreps id pub mac gen n b mb pins i), GeneratedCells gen n pub prep.val.2.2),
        (pub 0).val+15 < 2^w →
        (∀ i (prep : SignedPreps id pub mac gen n b mb pins i), let frame := CellDispatch.Frame.ofMemory pub prep.val.2.2
          frame.base+3*frame.count ≤ 2^w) →
        value = ∑ i : Fin k → Bool, ∑ prep : SignedPreps id pub mac gen n b mb pins i,
          pathWeight prep.val.1 * ((C i prep).product * tallyValue pub (install gen n mac)
            (cellBank pub (install gen n mac) prep.val.2.1 prep.val.2.2) prep.val.2.2 signedOccurrences
            signedOccurrences_deterministic) := by
  intro P mac G L F f p initial value scalar physicalRoom advice extended offset count star tag time good
  have result := jointPacket_eval_valueCoreWith physical P S pack link n e fit u pin ext header dst ibase hbase starbase
    pub mac s A (signedBody id) (signedBody_withoutAccept id) limit burst (n^25) scalar physicalRoom advice
    extended offset count star tag time
  obtain ⟨used,b,mb,spent,input,frame,copy,boot,valueEq⟩ := result.2 good
  refine ⟨used,b,mb,spent,input,frame,copy,boot,?_⟩
  intro k pins window C hf room
  have macEq : mac = install gen n mac := siteLibrary_installed gen n
  apply valueEq.trans
  conv_lhs => arg 3; rw [macEq]
  exact signedBody_bounded_product id pub mac gen n b mb pins window hn burst cap hf room C

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
