import OAI.Hierarchy.DescentNamedCalibratedPreflightPrice
import OAI.Hierarchy.DescentNamedOriginalPreflight
import OAI.Hierarchy.DescentLateReelPrice

namespace OAI
/-! # Cost of the actual original preprocessing bracketed by its paid count scan and its final reel -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch DescentKernelHistory DescentExteriorReplay
open DescentTerminalGraphVolume DescentTerminalCompiledPrefix.AddressPlan DescentExteriorMatrixUpdate
open DescentTerminalFixedSlices DescentTerminalCombinedRole DescentTerminalPreflightSpace DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM Filter ThreeFlat.RAM PhysicalProcedure
open scoped Classical Topology
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8000
set_option maxHeartbeats 800000
attribute [local irreducible] Origin.source
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec)
variable (t f g reset τ B drift : ℕ)
local notation "κ" => 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
local notation "limit_" => localSocketRate G t g
local notation "scan_" => PreflightCalendar.scanExponent G t f g reset
local notation "slice_" => 1+operandExponent G (stageNumbers G t 0 f g reset 0 0)+groupRate G t f g reset+4

/-- Both boundary reels, the six genuine role banks, all replay instructions and the fixed
preflight use the original open-host allowance at the same height. -/
theorem original_preflight_price (big : 20≤B) (pad : 2*limit_≤τ)
    (funded : limit_+max scan_ slice_≤τ)
    (budget : 2*(limit_+(τ+κ+4))+Nat.clog 2 G.b*(t+1)≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ sites w factor roof lo compact lateStart takeOff : ℕ,
        let S:=stageNumbers G t J f g reset sites (tail τ J)
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        let j:=Nat.clog 2 (NativeBranch.localLimit G S)
        let dim:=S.groupWidth k (tail τ J) 0+k
        let r:=dim-2*j
        let W:=NativeBranch.binLimit (k:=k) S
        let U:=G.b^(t*J)*G.b
        let p:=W*(h/(16*((2^j*U)*W)))
        let s:=S.firstWidth G.b p
        let q:=PreflightCalendar.publicSlots G S
        let wire : ℝ := (S.epochPower:ℝ)^S.priceExponent
        let u:=(1/((s:ℝ)*(wire:ℝ)):ℝ)*(wire:ℝ)
        let ε:=(((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
        ∀ {cp ar} (X : Approximation F cp ar) {n D C : ℕ} {he : 0≤ε} {hu : 0≤u}
          (radix : S.radix=2^k) (baseGroups : S.baseGroups=2^(tail τ J))
          {history : Epochs G hu he (h:=D) (C:=C) (Ht:=GroupStage.depthBound (atRound S.rounds) n f g)
             (t:=S.rounds) S.height (initial X S.copies s (S.groupCount 0) k (S.initialDigits radix))}
          {chosen : (Epochs.finish G hu he history).Choice} (_b : Branch X G S (p:=p) (n:=n) (h:=D) (C:=C) (f:=f) (g:=g) (k:=k) (he:=he) (hu:=hu) radix drift history chosen)
          (tag : ℕ→Bool) (rot loc : ℕ→ℕ) (plan : DescentExteriorMatrixUpdate.Reel)
          (phase : Phase F) (A : Snapshots k)
          (headerRows paidRows slots bundle bins homes₀ rate blocks₀ roleBase : ℕ),
          let E:=Fintype.card (Port ar X.width)
          let fund:=(S.copies*s)*(sites+2^J*E)
          let rawCount:=integralFrontier (2^J) sites (S.copies*s) E rate
          let pool:=bought (rowBudget bundle slots bins rawCount ((S.copies*s)*E) homes₀ 3) bins
          let ρ:=6*(32*factor)*(3+4*rate)+2*factor
          let orig:=geometryFormat G S k g p (tail τ J) q drift op headerRows paidRows
          let spec:=preflightSpec X G S k g p (tail τ J) orig
          let first:=Calendar.earlyEnd S k (tail τ J) roof j r s E
          let cal:=replayCalendar X S k (tail τ J) j r A
          let base:=phase.stop first
          let censusAt:=(spec.scanPages (cal.packetEnd base) q).stop
          ∀(blocks : spec.scalar.blocks=phase.output.receiver.blocks) (peer : Bank) (paid actor : Fin spec.scalar.blocks→Bank)
            (signed : Fin spec.scalar.blocks→Fin (2*spec.cap)→Bank) (room : cal.stop censusAt<2^w),
            let dates:=Chronology.countDates 0 (Chronology.kindCalendar S.rounds S.height)
            let countCPU:=DescentLowCountBook.program w lo (fun i=>loc (dates[i]?.getD 0)) dates.length
            let prefixCPU:=originalPreflight X G S baseGroups radix g p q drift op headerRows paidRows j r s roof
              compact tag rot phase A blocks roleBase peer paid actor signed room
            let prefixClocks:=originalPreflightClocks X G S (k:=k) (tail:=tail τ J) g p q drift op headerRows paidRows j r s roof
              phase A blocks peer paid actor signed room
            let postCPU:=Calendar.postProgram (plan.late lateStart) dim S.length j r s E w compact takeOff
            0<p → p≤h → 2*(6*PreflightCalendar.fieldExponent G t f g reset τ+11)≤B →
            PreflightCalendar.Ready G op t f g reset τ B drift h → 0< sites →
            2^h≤2*(sites*S.copies) → 0<w → w+1≤factor*h → h≤32*(slots*bundle) →
            0<bins → bins≤2^(h/2) → (4+(homes₀+1)*(26+234*blocks₀))*h*2^J≤ sites*(S.copies*s) →
            headerRows≤pool+(rawCount/(slots*bundle)+1) → paidRows≤pool → drift+1≤ scale J 1 →
            phase.Paid h (scale J slice_) → phase.output.metadataEnd phase.dateBase≤first →
            phase.output.receiver.hosts=S.hostSize S.length → 0<phase.output.receiver.hosts →
            phase.output.argumentSlots≤S.retainedArgumentsAt G drift → phase.output.receiver.blocks≤2^k →
            A.hosts=S.hostSize →
            (4+11*dates.length+prefixClocks+Calendar.postClock S.length j r s E+
             7*names ((countCPU.seq prefixCPU).seq postCPU))*(w+1)*2^J≤
               (524288*(factor+1)+7*16384*(2*factor)+(128000+262144)*factor+7*24200200*(2*factor+6*ρ))*fund := by
  filter_upwards [stage_both_native_reels G t f g reset τ B big pad budget,
    stage_replay_open_invoice G t f g reset τ B big pad budget, early_native_packing G t f g reset τ B big pad budget,
    Filter.eventually_ge_atTop 10] with h both replay packing tall
  intro J sites w factor roof lo compact lateStart takeOff S k j dim r W U p s q wire u ε
    cp ar X n D C he hu radix baseGroups history chosen _b tag rot loc plan phase A headerRows paidRows
    slots bundle bins homes₀ rate blocks₀ roleBase E fund rawCount pool ρ orig spec first cal base censusAt
    blocks peer paid actor signed room dates countCPU prefixCPU prefixClocks postCPU
    positive short reserve date occupied support word arch packed binsPos binsRoom positions fitHeader fitPaid
    late measured past ends active lanes groups aligned
  obtain ⟨_,_,power,_,head⟩:=packing sites
  have ready:=replay sites E w factor base censusAt A cal.seed room aligned support word arch
  have boundary:=both sites w factor roof lo compact lateStart takeOff X tag rot loc plan support
    ((Nat.le_succ _).trans arch)
  let front:=historyCountReel X S roof tag rot loc lo compact k (tail τ J) j r s w
  let entry:=Calendar.earlyClock S k (tail τ J) j r s E
  let finish:=Calendar.postClock S.length j r s E
  have prior : (4+11*dates.length+entry+finish+7*names (front.seq postCPU))*(w+1)*2^J≤
      (524288*(factor+1))*fund := by
    have grouped : ((4+11*dates.length+entry+7*names front)+(finish+7*names postCPU))*(w+1)*2^J ≤
        (524288*(factor+1))*fund := boundary
    rw [names_seq]
    convert grouped using 1
    ring
  have limits:=cal.addresses base censusAt
  have space : phase.stop first<2^w :=
    ((limits.1.trans (limits.2.1.trans limits.2.2.1)).trans
      ((show cal.packetEnd base≤censusAt from Nat.le_add_right ..).trans limits.2.2.2.1)).trans_lt room
  let matrix:=Calendar.stop S k (tail τ J) roof+S.length
  let ptr:=fun (f : Fin 4) (i : Fin phase.output.argumentSlots) (a : Fin spec.scalar.blocks)=>
    phase.output.terminalPointers phase.dateBase f i (a.cast blocks)
  have bought:=calibrated_preflight_prefix X G op t f g reset τ B h sites drift p _b positive short (by omega)
    reserve date headerRows paidRows censusAt E slots bundle bins homes₀ factor rate blocks₀ phase first w cal room
    peer paid actor signed matrix roleBase ptr baseGroups occupied funded tall support power arch head packed binsPos
    binsRoom positions fitHeader fitPaid late measured past space ends active lanes groups ready front postCPU _ _ prior
  let earlyCPU := Calendar.earlyProgram S k (tail τ J) roof tag rot j r s E compact w
  let sheetCPU := phase.program first w
  let replayCPU := cal.program base censusAt room
  let fixedCPU := fixedPreflight X G S baseGroups radix g p q drift op headerRows paidRows censusAt
    (cal.packetEnd base) w peer (cal.homes base) paid actor signed matrix roleBase (phase.banks first) ptr
  let replayPrice := cal.cost base censusAt room
  let fixedPrice := fixedPreflightClocks X G S (k:=k) (tail:=tail τ J) g p q drift op headerRows paidRows
    censusAt (cal.packetEnd base) peer (cal.homes base) paid actor signed matrix ptr
  have front_eq : front = countCPU.seq earlyCPU := rfl
  have program_eq : prefixCPU = ((earlyCPU.seq sheetCPU).seq replayCPU).seq fixedCPU := rfl
  have clocks_eq : prefixClocks = entry+phase.cost first+replayPrice+fixedPrice := rfl
  change (4+11*dates.length+entry+finish+phase.cost first+replayPrice+fixedPrice+
    7*names ((((front.seq sheetCPU).seq replayCPU).seq fixedCPU).seq postCPU))*(w+1)*2^J ≤
    (524288*(factor+1)+7*16384*(2*factor)+(128000+262144)*factor+7*24200200*(2*factor+6*ρ))*fund at bought
  rw [front_eq] at bought
  rw [program_eq,clocks_eq]
  change (4+11*dates.length+(entry+phase.cost first+replayPrice+fixedPrice)+finish+
    7*names ((countCPU.seq (((earlyCPU.seq sheetCPU).seq replayCPU).seq fixedCPU)).seq postCPU))*(w+1)*2^J ≤ _
  simp only [names_seq] at bought ⊢
  convert bought using 1
  ring

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
