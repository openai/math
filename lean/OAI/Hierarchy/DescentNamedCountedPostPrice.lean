import OAI.Hierarchy.DescentNamedPostEarlyInvoice

namespace OAI
/-! # The exact count, early reel, deferred terminal-preflight and late reel interval of the issued stage -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch DescentKernelHistory DescentExteriorReplay
open DescentTerminalGraphVolume DescentTerminalCompiledPrefix.AddressPlan DescentExteriorMatrixUpdate
open DescentTerminalFixedSlices DescentTerminalCombinedRole DescentTerminalPreflightSpace DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM Filter ThreeFlat.RAM PhysicalProcedure
open scoped Classical Topology
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec)
variable (t f g reset τ B drift : ℕ)
local notation "κ" => 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
local notation "limit_" => localSocketRate G t g
local notation "scan_" => PreflightCalendar.scanExponent G t f g reset
local notation "slice_" => 1+operandExponent G (stageNumbers G t 0 f g reset 0 0)+groupRate G t f g reset+4

/-- All original count capture, early reel, post-preflight and late reel charges at one height. -/
def CountedPostAt (h : ℕ) : Prop :=
  let J:=Nat.log 2 h/(2*B)
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
            let earlyCPU:=Calendar.earlyProgram S k (tail τ J) roof tag rot j r s E compact w
            let termCPU:=postEarlyPreflight X G S baseGroups radix g p q drift op headerRows paidRows j r s roof
              phase A blocks roleBase peer paid actor signed room
            let termClocks:=postEarlyPreflightClocks X G S (k:=k) (tail:=tail τ J) g p q drift op headerRows paidRows j r s roof
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
            (4+11*dates.length+Calendar.earlyClock S k (tail τ J) j r s E+termClocks+Calendar.postClock S.length j r s E+
             7*names (((countCPU.seq earlyCPU).seq termCPU).seq postCPU))*(w+1)*2^J≤
               (524288*(factor+1)+7*16384*(2*factor)+(128000+262144)*factor+7*24200200*(2*factor+6*ρ))*fund

/-- Both boundary reels, the six genuine role banks, all replay instructions and the fixed
preflight use the original open-host allowance at the same height. -/
theorem counted_post_preflight_price (big : 20≤B) (pad : 2*limit_≤τ)
    (funded : limit_+max scan_ slice_≤τ)
    (budget : 2*(limit_+(τ+κ+4))+Nat.clog 2 G.b*(t+1)≤B) :
    ∀ᶠ h : ℕ in atTop, CountedPostAt G op t f g reset τ B drift h := by
  filter_upwards [original_preflight_price (F:=F) G op t f g reset τ B drift big pad funded budget] with h paid
  simpa only [CountedPostAt,postEarlyPreflightClocks,originalPreflightClocks,postEarlyPreflight,originalPreflight,
    names_seq,Nat.add_assoc] using paid

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
