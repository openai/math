import OAI.ThreeFlat.RAM.TickLinkedExecution

namespace OAI
/-! # Malformed shared records in the installed native tick -/

noncomputable section
namespace ThreeFlat.RAM.TickMachine

open Computability.VPVNP.BurstRAM PrivateRAM TickActiveROM ContinuationLink Contraction BitLayout HistoryFactors
open Diagonal.ApproximateImage Diagonal.TickChronology TickFuel
open scoped Fin.CommRing Classical

variable {F : Type*} [Field F] [Fintype F] {H J w np sp nr sr nk sk : ℕ}
variable {age bits teams capacity q nt ns paramSize : ℕ}
local notation "B" => TickPhysicalABI.mounted age bits teams capacity q nt ns paramSize
local notation "pins" => pinCount q nt ns paramSize bits

/-- The deterministic navigation checks already reject here. This proof
does not select a history, allocate a fictitious slot, or invoke preparation. -/
theorem rejected_execution (clock : Clock) (fit : Fits (TickWeightedBank.shape F pins H J) w)
    (nav : Block w np nr nk) (prep : Block w sp sr sk) (nd : Fin nk → Word w) (sd : Fin sk → Word w)
    (large : textCutoff F np sp nr sr nk sk ≤ age) (L : Diagonal.TickAuxiliary.Layout bits) (D : Fin q → Bool)
    (params : Fin paramSize → Bool) (oa na oc nc : Fin bits → Bool) (team step navTime : ℕ)
    (ft : team < 2^nt) (fs : step < 2^ns) (wt : team < 2^w) (ws : step < 2^w)
    (duration : clock.groupDuration < 2^w) (last : clock.last < 2^w) (begin : clock.beginTick < 2^w)
    (room : 2+pins+bits < 2^w) (space : WordBounds B fit)
    (pre admitted : Memory w → Prop) (post : Memory w → Memory w → Prop) :
    let M := linkedProgram B clock fit nav prep nd sd large q nt ns
    let pin := fields D (digits team nt) (digits step ns) params oa na oc nc
    let mem := TickMountedPins.memory (w:=w) pin
    let field := codec (TickWeightedBank.shape F pins H J) fit
    let start := TickNavigationEntry.input B clock team step mem
    TickStageSpec.Admission field nav nd pre admitted post navTime →
    pre start → ¬admitted start →
    ∀ (cfg : Config w (Fintype.card (All (n:=np) (m:=sp) (k:=TickPublicData.count nk sk) B clock fit)) age), cfg.pc=M.entry →
      Returns field M.program ((159+6*(nt+ns)+25+18*bits)+(1470+navTime+21)) cfg mem
        (if Diagonal.TickAuxiliary.branch L (clock.phase step) oa na then 0
         else if oa=(fun _ => false) ∧ na=(fun _ => false) ∧ oc=nc then 1 else 0) := by
  intro M pin mem field start admission initial bad cfg atEntry
  let ev := (interpreter pins H J (B).metadata (B).lut (F:=F) fit).publicData
  let bank := TickPublicData.data q nt ns ev nd sd
  have small : 2+q+nt < 2^w ∧ ns < 2^w := by unfold pinCount at room; omega
  obtain ⟨tb,tw,sb,sw⟩ := TickPublicData.decode_params q nt ns ev nd sd small.1 small.2
  let size := fits_text large
  let front := frontRegisters (w:=w) (k:=TickPublicData.count nk sk) (u:=age) clock
    (by have := size.2.1; omega)
  let regs := registers B clock fit (k:=TickPublicData.count nk sk) size.2.1
  let nav' := nav.reindex (Function.Embedding.refl _) (TickPublicData.navigator nk sk)
  let prep' := prep.reindex (Function.Embedding.refl _) (TickPublicData.preparer nk sk)
  let K := TickPublicData.evaluator nk sk
  let ky := TickPublicData.keys nk sk
  let loc := historyLocation (k:=TickPublicData.count nk sk) (n:=np) (m:=sp) B clock fit
  let frame := {regs with control := selectedRegs front}
  have rom := program_history B clock fit front regs ky bank K nav' prep'
  have restricted : TickStageSpec.Admission field nav nd (fun m => pre m ∧ ¬admitted m)
      admitted (fun _ _ => False) navTime := by
    intro P R K' target pc rr pr exit installed params c m entry ready
    obtain ⟨_,reject⟩ := admission target pc rr pr exit installed params c m entry ready.1
    exact ⟨fun yes => (ready.2 yes).elim,reject⟩
  have lifted : TickStageSpec.Admission field nav' bank (fun m => pre m ∧ ¬admitted m)
      admitted (fun _ _ => False) navTime := by
    intro pc r k machine
    exact TickPublicData.admission_port field nav nd bank (TickPublicData.navigator nk sk)
      (TickPublicData.nav_read q nt ns ev nd sd) restricted machine
  have wide := space.width
  apply returns_mounted field clock fit front regs ky bank K nav' prep' L D params oa na oc nc
    team step _ 0 ft fs wt ws tb tw sb sw duration last (by omega) room cfg atEntry
  intro c _ there teamWord stepWord tag marker
  have run := navigate B clock fit (program B clock fit front regs ky bank K nav' prep')
    nav' prep' loc frame K rom team step c mem there teamWord stepWord tag marker
    space.ctrl (by have h := space.clk; have h' := space.bounds; have := space.requests; omega)
    duration begin ws (fun m => pre m ∧ ¬admitted m) admitted (fun _ _ => False) navTime 0 0
    lifted ⟨initial,bad⟩ (fun _ impossible => impossible.elim)
  simpa only [field, mem, pin, Nat.add_zero, ite_self] using run


end ThreeFlat.RAM.TickMachine

end
end OAI
