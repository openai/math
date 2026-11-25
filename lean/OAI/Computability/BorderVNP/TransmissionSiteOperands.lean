import OAI.Computability.BorderVNP.TransmissionPacketOperands
import OAI.Computability.BorderVNP.TransmissionSiteProcessor

/-! # The assembled signed site decodes its actual packet operand bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RAMTape TeamSite TeamSite.Processor RoutingISA RoutingISA.Pins

/-- Construct the ordinary scalar tuple from the *same* physical geometry as the
signed wiring and the separate allocations for frame, broadcast, packet and pin arrays. -/
def operandsAtSite {R r t d link inner n w : ℕ} {E : Type}
    (G : Wiring R r t d link inner n E) (u : Fin (R+1)) (ibase hbase starbase : ℕ)
    (frame header copy : ℕ) (A : AdviceLayout) (packet : ReferencePacket w d) : PacketOperands :=
  ⟨G.pinLayout u ibase hbase starbase,frame,header,copy,A,packet.entry.length⟩

private theorem startup_public {reg k w : ℕ} (pub : Fin k → Word w) (H limit burst : Word w)
    (ing : List Bool) (i : Fin k) :
    (TeamLocalClock.Startup.input (r := reg) pub H limit burst ing) (.clock (.isa (.pub i))) =
      wordBits (pub i) := by
  have view := Bank.startup_view (r := reg) (d := 0) (fun _ => []) pub H limit burst [] [] [] ing []
  exact (congrFun view (.clock (.isa (.pub i)))).symm

variable {pc reg routines m g R r w a d : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg 32 routines) (lib : Fin routines → Macro Q Γ m g)
variable (S : SiteData R r reg 32 w a)

/-- After actual raw-tape startup, each of the 32 architectural public register stacks
contains exactly the encoded scalar from the allocator. Every independent stage operand
travels through the same real public word decoder. The same bank supplies the ordinary
frame hypothesis used by `jointPacket_run`. -/
theorem site_operands_loaded (B : Fin (R+1) → PacketOperands) (pack : Fin (R+1) → ReferencePacket w d)
    (link n e : ℕ) (fit : Fits P lib r w a R link n e) (hw : 0 < w) (hH : 2^e ≤ n)
    (u : Fin (R+1)) (j : Fin r) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (int : Wires.Edge r reg w e (w+1) → Bool) (ibase hbase starbase : ℕ) :
    let T := (S.withOperands B).withPacket pack
    let G := wiring P lib T d link n e fit
    let F := G.processorFields u pin ext ibase hbase starbase
    let data := F.row j
    let stride := entryStride (Processor.machine P lib) (w+1) n (prefixCapacity r 32 reg w n+1+a) R link
    let base := j.val*stride
    (B u).Fits w → 2*(base+data.length) ≤ 2^(w+1) → 2*data.length ≤ 4*(2^e) →
    ∃ ticks bank, ticks ≤ preludeTime (entryBudget w n e data.length) reg 32 w (last j) ∧
      StackRuns (Processor.code P lib) ticks Processor.start
        (StackCompiler.labeledInput TeamSite.Layout.input (List.ofFn (G.word pin ext int u j)))
        (beginBlock (last j)) bank ∧
      (∀ i : Arg, bank (TeamSite.Layout.site (.clock (.isa (.pub i)))) =
        wordBits ((B u).bank (S.publicWords u) i)) ∧
      PacketFrame (B u).layout (B u).broadcast (B u).advice (B u).entryWords w
        (fun _ => 0) (operand (T.publicWords u)) := by
  intro T G F data stride base scalar room cap
  obtain ⟨ticks,bank,hcost,run,hstartup,_⟩ :=
    sitePrelude P lib T d link n e fit hw hH u j pin ext int ibase hbase starbase room cap
  refine ⟨ticks,bank,hcost,run,?_,(B u).packetFrame (S.publicWords u) scalar⟩
  intro i
  exact (congrFun hstartup (.clock (.isa (.pub i)))).trans (startup_public ..)

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
