import OAI.Hierarchy.DescentNamedTerminalPopulation
import OAI.Hierarchy.DescentTerminalPriorArena
import OAI.Hierarchy.DescentTerminalCohortRun

namespace OAI
/-! # Actual selected f1/f3 fields at the end of the fixed frozen-cohort allocation -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S radix R r c) (hp : 0<p)

open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace Branch
attribute [local irreducible] Origin.source Branch.pinSpine Branch.cohortHome
variable {tail : ℕ} (base : S.baseGroups=2^tail)
local notation "trace" => pinSpine X G S b hp base
local notation "E" => Fintype.card (Port P X.width)
local notation "H" => S.hostSize S.length
local notation "N" => ((Epochs.finish G hu he r).state c).graph
local notation "A" => b.target.placement
local notation "frozenLength" => b.path.frozen
local notation "Cohort" => Fin (E*2^frozenLength)


local notation "W" => (Epochs.finish G hu he r).state c
local notation "cap_" => 2^(8+S.capGain*S.length)
local notation "homes" => cohortHome X G S b hp base

open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
local notation "gs" => S.groupCount S.length
local notation "hosts" => b.target.vertex.trans (Fin.castLEEmb b.target.valid.host)
local notation "paid" bits_ => Census.count A (Equiv.refl (Fin gs)) hosts bits_
local notation "ext" => Computability.BorderVNP.FragmentBucket.count homes
local notation "arch" => Branch.archive X G S b hp

open DescentTerminalPriorArena DescentTerminalPrimitiveArena
open scoped Fin.CommRing
variable {w : ℕ} (cohortBase columns pointerBits countBits : ℕ)
    (mPaid mAct paidBits extBits nodeBits : ℕ)
    (paidSrc actorSrc : Block k → Bank)
local notation "shape_" => (⟨2^k,H,columns,pointerBits,countBits⟩ : Shape)
local notation "occurrences" => E*2^frozenLength
local notation "capBits" => 8+S.capGain*S.length
local notation "ord" => DescentTerminalCohortArena.order cohortBase frozenLength capBits occurrences H
local notation "popStart_" => DescentTerminalCohortArena.stop cohortBase frozenLength capBits occurrences H
local notation "counts" => (⟨(ord).counts,Nat.clog 2 H⟩ : Bank)
local notation "popAddr" => pop shape_ gs mPaid paidBits extBits popStart_
local notation "actAddr" => actor shape_ gs mPaid mAct paidBits extBits 1 popStart_
local notation "next" => DescentTerminalPriorArena.start shape_ gs mPaid mAct paidBits extBits 1 popStart_
local notation "occ" => (shape_).subrow actAddr
local notation "pick" => (fun (_ : Block k) (x : Cell 1) => x)
local notation "proc" => DescentTerminalPriorArena.program (wb:=w) (s:=shape_) (groups:=gs)
  (mPaid:=mPaid) (mAct:=mAct) (paidBits:=paidBits) (extBits:=extBits) (actBits:=1) (origin:=popStart_)
  («paid»:=paidSrc) (actorSrc:=actorSrc) («ext»:=counts) (nodeBits:=nodeBits) («pick»:=pick)
local notation "cpu" => DescentTerminalPopulation.RAM.ticks H gs mPaid paidBits extBits popStart_ paidSrc counts +
  DescentTerminalActorRepack.ticks (a:=1) H gs mAct (actStart shape_ gs mPaid paidBits extBits popStart_) actorSrc
local notation "live" => fun (x : Block k) (h : Fin H) (g : Fin gs) =>
  (if ∃ v : (N).Site,b.target.home v=h ∧ ((A).pos v).1=g ∧ (A).block v=x then 1 else 0 : Cell 1)

private theorem cohortBankBounds (base frozen cap n h : ℕ) :
    base ≤ DescentTerminalCohortArena.stop base frozen cap n h ∧
    (DescentTerminalCohortArena.order base frozen cap n h).counts + 2^Nat.clog 2 h ≤
      DescentTerminalCohortArena.stop base frozen cap n h := by
  let rom := DescentTerminalFrozenRoster.ROM.size frozen cap
  let nr := 2 ^ Nat.clog 2 n
  let hr := 2 ^ Nat.clog 2 h
  have nrPos : 0 < nr := Nat.two_pow_pos _
  have hrPos : 0 < hr := Nat.two_pow_pos _
  change base ≤ base+rom+nr+hr+h+1+nr+hr+nr+4*n+h+1 ∧
    base+rom+nr+hr ≤ base+rom+nr+hr+h+1+nr+hr+nr+4*n+h+1
  omega

theorem prior_fields (before : Memory w) (within : next < 2^w)
    (hmPaid : 0< mPaid) (hmAct : 0< mAct) (wide : nodeBits*gs≤w)
    (hh : 0<S.height) (paidFmt : S.epochPower^S.localTokenExponent<2^paidBits)
    (nodeFmt : S.epochPower^S.localTokenExponent<2^nodeBits) (extFmt : cap_<2^extBits)
    (pEnd : ∀x, (paidSrc x).base+(paidSrc x).size≤cohortBase)
    (pRows : ∀x, H*chunks gs mPaid≤(paidSrc x).size)
    (aEnd : ∀x, (actorSrc x).base+(actorSrc x).size≤cohortBase)
    (aRows : ∀x, H*chunks gs mAct≤(actorSrc x).size)
    (pRead : ∀x, ∀j : Row H gs mPaid, before ((paidSrc x).base+(row H gs mPaid j).val)=
      ((data (fun h g=>(paid paidBits) h g x) j).val:Computability.VPVNP.BurstRAM.Word w))
    (aRead : ∀x, ∀j : Row H gs mAct, before ((actorSrc x).base+(row H gs mAct j).val)=
      ((data (live x) j).val:Computability.VPVNP.BurstRAM.Word w))
    (roster : ∀h : Fin H,before ((ord).counts+h.val)=(ext h:Computability.VPVNP.BurstRAM.Word w)) :
    let out := DescentTerminalPriorArena.final (s:=shape_) (groups:=gs) (mPaid:=mPaid) (mAct:=mAct)
      (paidBits:=paidBits) (extBits:=extBits) (actBits:=1) (origin:=popStart_)
      («paid»:=paidSrc) (actorSrc:=actorSrc) («ext»:=counts) (nodeBits:=nodeBits) («pick»:=pick) before
    (proc).Exec before out cpu ∧ CheapCode proc ∧ (shape_).Prior next popAddr occ ∧
    (∀v : (N).Site,digit nodeBits ((A).pos v).1.val
      (out (((shape_).subrow popAddr ((A).block v)).base+(b.target.home v).val)).val =
      Fintype.card ((arch).bit.recipe v).Node) ∧
    (∀x (h : Fin H),out ((occ x).base+h.val) = ((encode 1 gs (live x h)).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    ∀j, j<popStart_ → out j=before j := by
  dsimp only
  have bounds := cohortBankBounds cohortBase frozenLength capBits occurrences H
  have coarse : cohortBase ≤ popStart_ := bounds.1
  have countEnd : (counts).base+(counts).size ≤ popStart_ := bounds.2
  have earlier : Earlier shape_ gs mPaid mAct popStart_ paidSrc actorSrc counts :=
    ⟨fun x=>(pEnd x).trans coarse,pRows,countEnd,covered _,fun x=>(aEnd x).trans coarse,aRows⟩
  let hist := fun h:Fin H=>(⟨ext h,(cohort_cap X G S b hp base h).trans_lt extFmt⟩ : Cell extBits)
  have result := DescentTerminalPriorArena.issued shape_ gs mPaid mAct paidBits extBits 1 popStart_
    paidSrc actorSrc counts earlier within nodeBits pick before hmAct (fun _=>rfl)
    (fun x h g=>(paid paidBits) h g x) hist live pRead roster aRead
  have nodes := site_nodes X G S b hp hh
  have recFit (v : (N).Site) : ((A).records v).length < 2^paidBits := by
    have total := (nodes v).trans_lt paidFmt
    rw [node_population X G S b hp base v] at total
    exact (Nat.le_add_right _ _).trans_lt total
  refine ⟨result.1,result.2.1,prior shape_ gs mPaid mAct paidBits extBits 1 popStart_,?_,
    result.2.2.2.1,result.2.2.2.2⟩
  intro v
  rw [result.2.2.1 ((A).block v) (b.target.home v)]
  exact true_population_word X G S b hp base hmPaid wide recFit (fun z=>(nodes z).trans_lt nodeFmt) v

variable (homeSrc : Bank) (roomC : DescentTerminalCohortArena.stop cohortBase b.path.frozen (8+S.capGain*S.length)
      (Fintype.card (Port P X.width)*2^b.path.frozen) (S.hostSize S.length) < 2^w)
local notation "shelf_" => DescentTerminalCohortArena.shelf cohortBase frozenLength capBits occurrences H roomC
local notation "index_" => DescentTerminalCohortArena.indexBase cohortBase frozenLength capBits occurrences H
local notation "begin" => DescentTerminalCohortArena.machine cohortBase frozenLength capBits occurrences H roomC homeSrc
local notation "sortTicks" => DescentTerminalCohortArena.ticks cohortBase frozenLength capBits occurrences H roomC homeSrc

attribute [local irreducible] DescentTerminalCohortArena.machine DescentTerminalCohortArena.ticks
  DescentTerminalPriorArena.program DescentTerminalPriorArena.final

/-- Start before the frozen-cohort ROM installation, stable sort and tally. The three
physical outputs give the real population, presence and original frozen roster in one memory. -/
theorem after_cohorts_with_counts (initialMem : Memory w) (within : next < 2^w) (alive : 0<H)
    (srcFit : homeSrc.Fits w cohortBase) (homeRead : ∀u:Cohort,
      homeSrc.read initialMem (u.val:Computability.VPVNP.BurstRAM.Word w)=((homes u).val:Computability.VPVNP.BurstRAM.Word w))
    (hmPaid : 0< mPaid) (hmAct : 0< mAct) (wide : nodeBits*gs≤w)
    (hh : 0<S.height) (paidFmt : S.epochPower^S.localTokenExponent<2^paidBits)
    (nodeFmt : S.epochPower^S.localTokenExponent<2^nodeBits) (extFmt : cap_<2^extBits)
    (pEnd : ∀x, (paidSrc x).base+(paidSrc x).size≤cohortBase)
    (pRows : ∀x, H*chunks gs mPaid≤(paidSrc x).size)
    (aEnd : ∀x, (actorSrc x).base+(actorSrc x).size≤cohortBase)
    (aRows : ∀x, H*chunks gs mAct≤(actorSrc x).size)
    (pRead : ∀x, ∀j : Row H gs mPaid, initialMem ((paidSrc x).base+(row H gs mPaid j).val)=
      ((data (fun h g=>(paid paidBits) h g x) j).val:Computability.VPVNP.BurstRAM.Word w))
    (aRead : ∀x, ∀j : Row H gs mAct, initialMem ((actorSrc x).base+(row H gs mAct j).val)=
      ((data (live x) j).val:Computability.VPVNP.BurstRAM.Word w))
    : ∃ out,((begin).seq proc).Exec initialMem out (sortTicks+cpu) ∧ CheapCode ((begin).seq proc) ∧
      (shape_).Prior next popAddr occ ∧
      (∀v:(N).Site, digit nodeBits ((A).pos v).1.val
        (out (((shape_).subrow popAddr ((A).block v)).base+(b.target.home v).val)).val =
        Fintype.card ((arch).bit.recipe v).Node) ∧
      (∀x (h:Fin H),out ((occ x).base+h.val) = ((encode 1 gs (live x h)).val:Computability.VPVNP.BurstRAM.Word w)) ∧
      (∀h:Fin H,out ((shelf_).bins+h.val)=((DescentTerminalFrozenRoster.book homes
        (fun u:Cohort => (u.val:Fin (2^frozenLength))) h).val:Computability.VPVNP.BurstRAM.Word w)) ∧
      (∀i:Cohort,let u := (Computability.BorderVNP.FragmentBucket.dest homes).symm i
        out (index_+i.val)=(Computability.BorderVNP.FragmentBucket.prior homes u.val (homes u):Computability.VPVNP.BurstRAM.Word w)) ∧
      (∀h:Fin H,out ((ord).counts+h.val)=(ext h:Computability.VPVNP.BurstRAM.Word w)) ∧
      ∀j,j<cohortBase → out j=initialMem j := by
  obtain ⟨mid,built,cheap,history,slot,held⟩:=DescentTerminalCohortArena.produced
    cohortBase frozenLength capBits occurrences H roomC homeSrc initialMem alive srcFit homes homeRead
    (cohort_cap X G S b hp base)
  have previous (x) (j:Row H gs mPaid) : mid ((paidSrc x).base+(row H gs mPaid j).val) =
      ((data (fun h g=>(paid paidBits) h g x) j).val:Computability.VPVNP.BurstRAM.Word w) := by
    have lim := (row H gs mPaid j).isLt.trans_le (pRows x)
    have end_ := pEnd x
    exact (held _ (by omega)).trans (pRead x j)
  have actors (x) (j:Row H gs mAct) : mid ((actorSrc x).base+(row H gs mAct j).val) =
      ((data (live x) j).val:Computability.VPVNP.BurstRAM.Word w) := by
    have lim := (row H gs mAct j).isLt.trans_le (aRows x)
    have end_ := aEnd x
    exact (held _ (by omega)).trans (aRead x j)
  obtain ⟨run,good,chart,nodes,flags,keep⟩:=prior_fields X G S b hp base cohortBase columns pointerBits countBits
    mPaid mAct paidBits extBits nodeBits paidSrc actorSrc mid within hmPaid hmAct wide hh paidFmt nodeFmt extFmt
    pEnd pRows aEnd aRows previous actors (fun h=>(history h).2)
  let out := DescentTerminalPriorArena.final (s:=shape_) (groups:=gs) (mPaid:=mPaid) (mAct:=mAct)
    (paidBits:=paidBits) (extBits:=extBits) (actBits:=1) (origin:=popStart_)
    («paid»:=paidSrc) (actorSrc:=actorSrc) («ext»:=counts) (nodeBits:=nodeBits) («pick»:=pick) mid
  have execution : ((begin).seq proc).Exec initialMem out (sortTicks+cpu) := built.then run
  have code : CheapCode ((begin).seq proc) := cheap_seq cheap good
  refine ⟨out,execution,code,chart,nodes,flags,?_,?_,?_,?_⟩
  · intro h
    apply Eq.trans (keep _ ?_) (history h).1
    change (shelf_).bins+h.val < (shelf_).bins+H+1
    have hz:=h.isLt
    omega
  · intro i
    apply Eq.trans (keep _ ?_) (slot i)
    change index_+i.val < index_+2^Nat.clog 2 occurrences+4*occurrences+H+1
    have lim:=i.isLt.trans_le (Nat.le_pow_clog (by decide : 1<2) occurrences)
    omega
  · intro h
    apply Eq.trans (keep _ ?_) (history h).2
    exact (Nat.add_lt_add_left (h.isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) H)) _).trans_le
      (cohortBankBounds cohortBase frozenLength capBits occurrences H).2
  · intro j small
    have before := (cohortBankBounds cohortBase frozenLength capBits occurrences H).1
    exact (keep _ (small.trans_le before)).trans (held j small)

theorem after_cohorts (initialMem : Memory w) (within : next < 2^w) (alive : 0<H)
    (srcFit : homeSrc.Fits w cohortBase) (homeRead : ∀u:Cohort,
      homeSrc.read initialMem (u.val:Computability.VPVNP.BurstRAM.Word w)=((homes u).val:Computability.VPVNP.BurstRAM.Word w))
    (hmPaid : 0< mPaid) (hmAct : 0< mAct) (wide : nodeBits*gs≤w)
    (hh : 0<S.height) (paidFmt : S.epochPower^S.localTokenExponent<2^paidBits)
    (nodeFmt : S.epochPower^S.localTokenExponent<2^nodeBits) (extFmt : cap_<2^extBits)
    (pEnd : ∀x, (paidSrc x).base+(paidSrc x).size≤cohortBase)
    (pRows : ∀x, H*chunks gs mPaid≤(paidSrc x).size)
    (aEnd : ∀x, (actorSrc x).base+(actorSrc x).size≤cohortBase)
    (aRows : ∀x, H*chunks gs mAct≤(actorSrc x).size)
    (pRead : ∀x, ∀j : Row H gs mPaid, initialMem ((paidSrc x).base+(row H gs mPaid j).val)=
      ((data (fun h g=>(paid paidBits) h g x) j).val:Computability.VPVNP.BurstRAM.Word w))
    (aRead : ∀x, ∀j : Row H gs mAct, initialMem ((actorSrc x).base+(row H gs mAct j).val)=
      ((data (live x) j).val:Computability.VPVNP.BurstRAM.Word w))
    : ∃ out,((begin).seq proc).Exec initialMem out (sortTicks+cpu) ∧ CheapCode ((begin).seq proc) ∧
      (shape_).Prior next popAddr occ ∧
      (∀v:(N).Site, digit nodeBits ((A).pos v).1.val
        (out (((shape_).subrow popAddr ((A).block v)).base+(b.target.home v).val)).val =
        Fintype.card ((arch).bit.recipe v).Node) ∧
      (∀x (h:Fin H),out ((occ x).base+h.val) = ((encode 1 gs (live x h)).val:Computability.VPVNP.BurstRAM.Word w)) ∧
      (∀h:Fin H,out ((shelf_).bins+h.val)=((DescentTerminalFrozenRoster.book homes
        (fun u:Cohort => (u.val:Fin (2^frozenLength))) h).val:Computability.VPVNP.BurstRAM.Word w)) ∧
      (∀i:Cohort,let u := (Computability.BorderVNP.FragmentBucket.dest homes).symm i
        out (index_+i.val)=(Computability.BorderVNP.FragmentBucket.prior homes u.val (homes u):Computability.VPVNP.BurstRAM.Word w)) ∧
      ∀j,j<cohortBase → out j=initialMem j := by
  obtain ⟨out,run,cheap,prior,population,presence,books,slots,_,low⟩:=
    after_cohorts_with_counts X G S b hp base cohortBase columns pointerBits countBits
      mPaid mAct paidBits extBits nodeBits paidSrc actorSrc homeSrc roomC initialMem within alive
      srcFit homeRead hmPaid hmAct wide hh paidFmt nodeFmt extFmt pEnd pRows aEnd aRows pRead aRead
  exact ⟨out,run,cheap,prior,population,presence,books,slots,low⟩

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
