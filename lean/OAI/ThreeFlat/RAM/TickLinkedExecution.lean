import OAI.ThreeFlat.RAM.TickLinkedProgram
import OAI.ThreeFlat.RAM.TickInstructions

namespace OAI
/-! # Execution with disjoint fixed public ROMs for both native procedures -/

noncomputable section
namespace ThreeFlat.RAM.TickMachine
open Computability.VPVNP.BurstRAM PrivateRAM TickActiveROM ContinuationLink Contraction BitLayout HistoryFactors
open Diagonal.ApproximateImage Diagonal.TickChronology TickFuel
open scoped Fin.CommRing Classical

variable {F : Type*} [Field F] [Fintype F] {H J w np sp nr sr nk sk : ℕ}
variable {age bits teams capacity q nt ns paramSize : ℕ}
local notation "B" => TickPhysicalABI.mounted age bits teams capacity q nt ns paramSize
local notation "pins" => pinCount q nt ns paramSize bits

theorem linked_execution (clock : Clock) (fit : Fits (TickWeightedBank.shape F pins H J) w)
    (nav : Block w np nr nk) (prep : Block w sp sr sk) (nd : Fin nk → Word w) (sd : Fin sk → Word w)
    (large : textCutoff F np sp nr sr nk sk ≤ age) (x : CellInput B clock fit) (D : Fin q → Bool)
    (params : Fin paramSize → Bool) (oa na oc nc : Fin bits → Bool) (team step navTime prepTime : ℕ)
    (ft : team < 2^nt) (fs : step < 2^ns) (wt : team < 2^w) (ws : step < 2^w)
    (duration : clock.groupDuration < 2^w) (last : clock.last < 2^w) (begin : clock.beginTick < 2^w)
    (room : 2+pins+bits < 2^w) (space : WordBounds B fit) (pre admitted slotInput : Memory w → Prop) :
    let M := linkedProgram B clock fit nav prep nd sd large q nt ns
    let ph := clock.phase step
    let pin := fields D (digits team nt) (digits step ns) params oa na oc nc
    let mem := TickMountedPins.memory (w:=w) pin
    let field := codec (TickWeightedBank.shape F pins H J) fit
    let start := TickNavigationEntry.input B clock team step mem
    TickStageSpec.Admission field nav nd pre admitted (fun _ out => NavOutput x ph oa na oc nc slotInput out) navTime →
    pre start → TickStageSpec.Prepare prep sd slotInput
      (fun _ out => TickWeightedBank.Ready fit x.net x.lib pin (B).metadata (B).lut out) prepTime →
    ∀ (cfg : Config w (Fintype.card (All (n:=np) (m:=sp) (k:=TickPublicData.count nk sk) B clock fit)) age), cfg.pc=M.entry →
      Returns field M.program ((159+6*(nt+ns)+25+18*bits)+(1470+navTime+21+x.tail prepTime)) cfg mem
        (if Diagonal.TickAuxiliary.branch x.aux ph oa na then
          if admitted start then x.weight ph oa na oc nc pin else 0
         else if oa=(fun _ => false) ∧ na=(fun _ => false) ∧ oc=nc then 1 else 0) := by
  intro machine ph pin mem field start adm admittedStart prepRuns
  let ev := (interpreter pins H J (B).metadata (B).lut (F:=F) fit).publicData
  let bank := TickPublicData.data q nt ns ev nd sd
  have small : 2+q+nt < 2^w ∧ ns < 2^w := by unfold pinCount at room; omega
  obtain ⟨tb,tw,sb,sw⟩ := TickPublicData.decode_params q nt ns ev nd sd small.1 small.2
  let size := fits_text large
  let front := frontRegisters (w:=w) (k:=TickPublicData.count nk sk) (u:=age) clock
    (by have := size.2.1; omega)
  let regs := registers B clock fit (k:=TickPublicData.count nk sk) size.2.1
  exact physical_tick clock fit front regs (TickPublicData.keys nk sk) bank (TickPublicData.evaluator nk sk)
    _ _ x D params oa na oc nc team step navTime prepTime ft fs wt ws tb tw sb sw duration last begin
    room space (TickPublicData.eval_read q nt ns ev nd sd) pre admitted slotInput
    (TickPublicData.admission_port field nav nd bank _ (TickPublicData.nav_read q nt ns ev nd sd) adm)
    admittedStart (TickPublicData.prepare_port prep sd bank _ (TickPublicData.prep_read q nt ns ev nd sd) prepRuns)


end ThreeFlat.RAM.TickMachine

end
end OAI
