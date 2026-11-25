import OAI.ThreeFlat.RAM.TickMachineMounted
import OAI.ThreeFlat.RAM.TickAdmittedTransfer

namespace OAI
/-! # One physical tick from mounted input through native admission and contraction -/

noncomputable section
namespace ThreeFlat.RAM.TickMachine
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink DescriptorScan TickFuel Diagonal.TickChronology
open Diagonal.ApproximateImage TickActiveROM Contraction BitLayout HistoryFactors
open scoped Fin.CommRing Classical

variable {F : Type*} [Field F] [Fintype F] {H J w k n m nr mr r : ℕ}
variable {u a teams cap q nt ns np : ℕ}

local notation "B" => TickPhysicalABI.mounted u a teams cap q nt ns np
local notation "pins" => pinCount q nt ns np a

/-- For each word-encoded tensor proposal this identifies the weight of the
single concrete interpreter, including rejected histograms, identity checks,
cyclic external comparisons and the chosen team's terminal factors. -/
theorem physical_tick (clock : Clock) (fit : Fits (TickWeightedBank.shape F pins H J) w)
    (front : TickFrontROM.Reg w k clock ↪ Fin r) (regs : Registers B clock fit nr mr r k)
    (keys : TickPrefix.Keys k) (data : Fin k → Word w) (K : Fin 7 → Fin k)
    (nav : Block w n nr k) (prep : Block w m mr k)
    (x : CellInput B clock fit) (D : Fin q → Bool) (params : Fin np → Bool)
    (oa na oc nc : Fin a → Bool) (team step navTime prepTime : ℕ)
    (ft : team < 2^nt) (fs : step < 2^ns) (wt : team < 2^w) (ws : step < 2^w)
    (tb : (data keys.teamBase).val = 2+q) (tw : (data keys.teamWidth).val = nt)
    (sb : (data keys.stepBase).val = 2+q+nt) (sw : (data keys.stepWidth).val = ns)
    (duration : clock.groupDuration < 2^w) (last : clock.last < 2^w) (begin : clock.beginTick < 2^w)
    (room : 2+pins+a < 2^w) (space : WordBounds B fit)
    (par : ∀ i, data (K i) = (interpreter pins H J (B).metadata (B).lut (F:=F) fit).publicData i)
    (pre admitted slotInput : Memory w → Prop) :
    let M := program B clock fit front regs keys data K nav prep
    let ph := clock.phase step
    let pin := fields D (digits team nt) (digits step ns) params oa na oc nc
    let mem := TickMountedPins.memory (w:=w) pin
    let field := codec (TickWeightedBank.shape F pins H J) fit
    let start := TickNavigationEntry.input B clock team step mem
    TickStageSpec.Admission field nav data pre admitted
      (fun _ out => NavOutput x ph oa na oc nc slotInput out) navTime →
    pre start → TickStageSpec.Prepare prep data slotInput
      (fun _ out => TickWeightedBank.Ready fit x.net x.lib pin (B).metadata (B).lut out) prepTime →
    ∀ (cfg : Config w (Fintype.card (All (k:=k) (n:=n) (m:=m) B clock fit)) r), cfg.pc=M.entry →
    Returns field M.program ((159+6*(nt+ns)+25+18*a)+(1470+navTime+21+x.tail prepTime)) cfg mem
      (if Diagonal.TickAuxiliary.branch x.aux ph oa na then
        if admitted start then x.weight ph oa na oc nc pin else 0
       else if oa=(fun _ => false) ∧ na=(fun _ => false) ∧ oc=nc then 1 else 0) := by
  intro machine ph pin mem field start spec init generator cfg entry
  let L := historyLocation (k:=k) (n:=n) (m:=m) B clock fit
  let R := {regs with control := selectedRegs front}
  have programRows := program_history B clock fit front regs keys data K nav prep
  have wide := space.width
  apply returns_mounted field clock fit front regs keys data K nav prep x.aux D params oa na oc nc
    team step _ _ ft fs wt ws tb tw sb sw duration last (by omega) room cfg entry
  intro c _ there teamWord stepWord tag marker
  exact navigate B clock fit machine nav prep L R K programRows team step c mem there
    teamWord stepWord tag marker space.ctrl
    (by have h := space.clk; have h' := space.bounds; have := space.requests; omega)
    duration begin ws pre admitted _ navTime (x.tail prepTime) _ spec init
    (fun out post d here => admitted_transfer B clock fit machine nav prep L R K programRows
      ph x oa na oc nc pin space par slotInput prepTime generator out post d here)


end ThreeFlat.RAM.TickMachine

end
end OAI
