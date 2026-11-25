import OAI.Hierarchy.DescentTerminalSocketWidths
import OAI.Hierarchy.DescentNamedPublicGrains
import OAI.Hierarchy.DescentNamedTerminalPrior
import OAI.Hierarchy.DescentTerminalPublicWidthTape

namespace OAI
/-! # The named branch's actual public width bank and four shared ROM columns -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)

local notation "s" => S.firstWidth G.b p
open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace Branch
variable {tail : ℕ} (base : S.baseGroups=2^tail)
local notation "trace" => pinSpine X G S b hp base
local notation "E" => Fintype.card (Port P X.width)
local notation "H" => S.hostSize S.length
local notation "a" => S.groupWidth k tail S.length+k
local notation "N" => ((Epochs.finish G hu he r).state c).graph
local notation "A" => b.target.placement
local notation "frozenBits" => b.path.frozen
local notation "Cohort" => Fin (E*2^frozenBits)

open Computability.BorderVNP.FragmentBucket DescentTerminalExteriorHeaders DescentTerminalCohortRanks
open scoped BigOperators

open DescentTerminalPublicWidthTape DescentTerminalCohortArena
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
local notation "cb" => 8+S.capGain*S.length
local notation "homes" => cohortHome X G S b hp base
local notation "grate" => publicRate G S (p:=p) (k:=k) (tail:=tail)

variable (cohortBase start rows q₀ : ℕ)
local notation "arena" => DescentTerminalCohortArena.stop cohortBase frozenBits cb (E*2^frozenBits) H
local notation "ord" => DescentTerminalCohortArena.order cohortBase frozenBits cb (E*2^frozenBits) H
def publicWidthShape : Shape :=
  ⟨start,2^cb,H,rows,grate,⟨(ord).counts,Nat.clog 2 H⟩⟩
local notation "job" => publicWidthShape X G S b (tail:=tail) cohortBase start rows
variable (ext : (Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))) ↪ ℕ)
    (nodes : ((Epochs.finish G hu he r).state c).graph.Site ↪ ℕ)
    (ops : ∀ v, DescentKernelHistory.Boundary ((Epochs.finish G hu he r).state c).graph v ↪ ℕ)
local notation "xs" => DescentTerminalExteriorHeaders.stream (q:=q₀) (p:=p)
  N b.target.home b.target.order ext nodes ops H
variable (hq : 0<q₀)
include hp base hq in
theorem public_tape :
    DescentTerminalWidthRowsRAM.tape q₀ p (fun i=>count homes i*grate)=xs := by
  have edges (e:(N).Edge) : p∣(N).width e := by
    have e₀:=b.target.valid.divides e
    rw [b.target.grain] at e₀
    exact (dvd_mul_right p G.b).trans e₀
  have pins (z:SeedPin) : p∣s := by
    unfold AtomSchedule.firstWidth AtomSchedule.grainAt
    exact (dvd_mul_right p _).trans (dvd_mul_right _ _)
  exact tape_eq N b.target.home b.target.order ext nodes ops hp edges (fun z => by simpa only [Nat.mul_one] using pins z) q₀ hq _
    (fun i=>(site_public_grains X G S b hp base i).symm)

variable {w : ℕ} (m : Memory w)
    (after : DescentTerminalCohortArena.stop cohortBase b.path.frozen (8+S.capGain*S.length)
      (Fintype.card (Port P X.width)*2^b.path.frozen) (S.hostSize S.length) ≤ start)
    (space : (publicWidthShape X G S b (tail:=tail) cohortBase start rows).widthLayout.stop < 2^w)
include after space in
private theorem cohort_old_fit : (job).old.Fits w start := by
  have end_ : (ord).counts+2^Nat.clog 2 H≤arena := by
    change cohortBase+_+_+2^Nat.clog 2 H ≤ cohortBase+_+_+2^Nat.clog 2 H+H+1+_+_+_+4*(E*2^frozenBits)+H+1
    simpa only [Nat.add_assoc] using Nat.le_add_right (cohortBase+_+_+2^Nat.clog 2 H) _
  have small:=(job).scale_space space
  have top:start≤(job).widthLayout.origin:=by
    change start≤ start+(DescentTerminalPublicCountRAM.lut start (2^cb)).size+(job).scaleOut.size
    omega
  exact ⟨Nat.two_pow_pos _, (Nat.le_add_left _ _).trans_lt (end_.trans_lt (after.trans_lt (top.trans_lt small))), end_.trans after⟩

include hp base hq after space in
/-- The sparse public-width stream is issued from the original frozen-census tally. Only
the original four bounded table words and the attained low census page are read. -/
theorem public_prefix (liveRows:(xs).length≤rows)
    (census:∀i:Fin H,m ((ord).counts+i.val)=(count homes i:Computability.VPVNP.BurstRAM.Word w)) (j:Fin H) :
    (job).widthLayout.prefix.read ((job).lastMem q₀ p m) (j.val:Computability.VPVNP.BurstRAM.Word w)=
      ((DescentTerminalExteriorHeaders.stream (q:=q₀) (p:=p) N b.target.home
        b.target.order ext nodes ops (j.val+1)).length:Computability.VPVNP.BurstRAM.Word w) := by
  have source:=cohort_old_fit X G S b (tail:=tail) cohortBase start rows after space
  have sc:=(job).scale_space space
  have inputs:=DescentTerminalPublicCountRAM.count_read start (2^cb) H (job).old grate m source sc
    (count homes) (cohort_cap X G S b hp base) (Nat.le_pow_clog (by decide) _) census
  have tape:=public_tape X G S b hp base q₀ ext nodes ops hq
  have read:=DescentTerminalHeaderSockets.prefix_reads ((job).scaled m) (job).widthLayout q₀ p
    (fun i=>count homes i*grate) (fun i=>Nat.mul_le_mul_right _ (cohort_cap X G S b hp base i))
    ((congrArg List.length tape).le.trans liveRows)
    (DescentTerminalPublicCountRAM.bank_fits start (2^cb) H sc) (Nat.le_pow_clog (by decide) _) space inputs j
  have edges (e:(N).Edge) : p∣(N).width e := by
    have d:=b.target.valid.divides e
    rw [b.target.grain] at d
    exact (dvd_mul_right p G.b).trans d
  have pins (z:SeedPin) : p∣s := by
    unfold AtomSchedule.firstWidth AtomSchedule.grainAt
    exact (dvd_mul_right p _).trans (dvd_mul_right _ _)
  have passed := DescentTerminalPublicWidthTape.passed_eq N b.target.home b.target.order ext nodes ops hp edges (fun z => by simpa only [Nat.mul_one] using pins z) q₀ hq _
    (fun i=>(site_public_grains X G S b hp base i).symm) (j.val+1) j.isLt
  exact read.trans (congrArg (fun n : ℕ => (n : Computability.VPVNP.BurstRAM.Word w)) (congrArg List.length passed))

attribute [local irreducible] ProtocolRAM.CheapCode DescentTerminalDenseHeaderRAM.Reads
  DescentTerminalPublicWidthTape.Shape.program DescentTerminalPublicWidthTape.Shape.lastMem
  DescentTerminalPublicWidthTape.Shape.clocks DescentTerminalCohortArena.machine
  DescentTerminalCohortArena.ticks

private theorem widthsFromTape (shape : DescentTerminalPublicWidthTape.Shape)
    (q p w : ℕ) (m : Computability.VPVNP.BurstRAM.Memory w) (source : shape.old.Fits w shape.base)
    (space : shape.widthLayout.stop < 2^w) (counts : Fin shape.H → ℕ)
    (cap : ∀ i, counts i ≤ shape.maxCohorts) (room : shape.H ≤ shape.old.size)
    (census : ∀ i : Fin shape.H, m (shape.old.base+i.val) = (counts i : Computability.VPVNP.BurstRAM.Word w))
    (entries : List (DescentTerminalDenseHeader.Profile q p))
    (same : DescentTerminalWidthRowsRAM.tape q p (fun i => counts i*shape.rate) = entries)
    (fits : entries.length ≤ shape.rows) (positive : 0 < q*p)
    (rom : ℕ) (rem whole index control : Bank)
    (prior : rom+DescentTerminalDenseHeaderBoot.extent q p ≤ shape.base)
    (static_ : ∀ j < DescentTerminalDenseHeaderBoot.extent q p,
      m (rom+j) = DescentTerminalDenseHeaderBoot.back w q p j) :
    (shape.program w q p).Exec m (shape.lastMem q p m) (shape.clocks q p) ∧
    CheapCode (shape.program w q p) ∧
    DescentTerminalDenseHeaderRAM.Reads
      (DescentTerminalDenseHeaderBoot.layout q p rom shape.widthLayout.output rem whole index control)
      (DescentTerminalHeaderGroups.padded (n := shape.rows) entries) (shape.lastMem q p m) ∧
    ∀ j < shape.base, shape.lastMem q p m j = m j := by
  subst entries
  have run := shape.any q p m source space
  exact ⟨run.1, run.2, shape.exterior q p m source space counts cap room census fits positive
    rom rem whole index control prior static_, shape.before q p m space⟩

include hp base hq after space in
theorem public_widths (liveRows:(xs).length≤rows)
    (census:∀i:Fin H,m ((ord).counts+i.val)=(count homes i:Computability.VPVNP.BurstRAM.Word w))
    (rom:ℕ) (rem whole index control:Bank) (prior:rom+DescentTerminalDenseHeaderBoot.extent q₀ p≤ start)
    (static_:∀j<DescentTerminalDenseHeaderBoot.extent q₀ p,m (rom+j)=DescentTerminalDenseHeaderBoot.back w q₀ p j) :
    ((job).program w q₀ p).Exec m ((job).lastMem q₀ p m) ((job).clocks q₀ p) ∧ CheapCode ((job).program w q₀ p) ∧
    DescentTerminalDenseHeaderRAM.Reads (DescentTerminalDenseHeaderBoot.layout q₀ p rom
      (job).widthLayout.output rem whole index control)
      (DescentTerminalHeaderGroups.padded (n:=rows) xs) ((job).lastMem q₀ p m) ∧
    (∀j<start,(job).lastMem q₀ p m j=m j) := by
  have old:=cohort_old_fit X G S b (tail:=tail) cohortBase start rows after space
  exact widthsFromTape (job) q₀ p w m old space (count homes) (cohort_cap X G S b hp base)
    (Nat.le_pow_clog (by decide) _) census xs (public_tape X G S b hp base q₀ ext nodes ops hq)
    liveRows (Nat.mul_pos hq hp) rom rem whole index control prior static_

include hp base hq after space in
/-- Executing the sorter and producer uses only original selected cohort addresses and a single
copy of the four ROM columns. -/
theorem after_public_cohorts (homeSrc:Bank) (src:homeSrc.Fits w cohortBase) (alive:0<H)
    (fromFlight:∀j:Cohort,homeSrc.read m (j.val:Computability.VPVNP.BurstRAM.Word w)=((homes j).val:Computability.VPVNP.BurstRAM.Word w))
    (liveRows:(xs).length≤rows) (rom:ℕ) (rem whole index control:Bank)
    (prior:rom+DescentTerminalDenseHeaderBoot.extent q₀ p≤cohortBase)
    (static_:∀j<DescentTerminalDenseHeaderBoot.extent q₀ p,m (rom+j)=DescentTerminalDenseHeaderBoot.back w q₀ p j)
    (arenaFit:arena<2^w) :
    let pref:=DescentTerminalCohortArena.machine cohortBase frozenBits cb (E*2^frozenBits) H arenaFit homeSrc
    let cost:=DescentTerminalCohortArena.ticks cohortBase frozenBits cb (E*2^frozenBits) H arenaFit homeSrc
    ∃out,(pref.seq ((job).program w q₀ p)).Exec m out (cost+(job).clocks q₀ p) ∧
      CheapCode (pref.seq ((job).program w q₀ p)) ∧
      DescentTerminalDenseHeaderRAM.Reads (DescentTerminalDenseHeaderBoot.layout q₀ p rom
        (job).widthLayout.output rem whole index control) (DescentTerminalHeaderGroups.padded (n:=rows) xs) out ∧
      (∀j<cohortBase,out j=m j) := by
  intro pref cost
  obtain ⟨mid,run,cheap,cols,_,held⟩:=DescentTerminalCohortArena.produced
    cohortBase frozenBits cb (E*2^frozenBits) H arenaFit homeSrc m alive src homes fromFlight (cohort_cap X G S b hp base)
  have bound : cohortBase≤arena := by
    change cohortBase ≤ cohortBase+_+_+_+_+1+_+_+_+4*(E*2^frozenBits)+H+1
    simp only [Nat.add_assoc, Nat.le_add_right]
  obtain ⟨issued,allow,reads,low⟩:=public_widths X G S b hp base cohortBase start rows q₀ ext nodes ops hq mid after space
    liveRows (fun j=>(cols j).2) rom rem whole index control ((prior.trans bound).trans after)
    (fun j hj=>(held _ (by omega)).trans (static_ j hj))
  exact ⟨(job).lastMem q₀ p mid, Procedure.Exec.then run issued,
    @cheap_seq w pref ((job).program w q₀ p) cheap allow,reads,fun j hj=>
    (low j (hj.trans_le (bound.trans after))).trans (held j hj)⟩

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
