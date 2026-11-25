import OAI.Hierarchy.DescentTerminalNodePopulation
import OAI.Hierarchy.DescentTerminalPopulationPage
import OAI.Hierarchy.DescentTerminalFrozenCountBank

namespace OAI
/-! # Field three of the actual final scalar archive -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height (initialGroup X S.copies (S.firstWidth G.b p))}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p)

open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace NativeBranch
variable {tail : ℕ} (base : S.baseGroups=2^tail)
local notation "trace" => pinSpine X G S b hp base
local notation "E" => Fintype.card (Port P X.width)
local notation "H" => S.hostSize S.length
local notation "a" => S.groupWidth k tail S.length+k
local notation "N" => ((Epochs.finish G hu he r).state c).graph
local notation "A" => b.target.placement
local notation "f" => b.path.frozen
local notation "Cohort" => Fin (E*2^f)


local notation "W" => (Epochs.finish G hu he r).state c
local notation "cap_" => 2^(8+S.capGain*S.length)
local notation "homes" => cohortHome X G S b hp base

open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
local notation "gs" => S.groupCount S.length
local notation "hosts" => b.target.vertex.trans (Fin.castLEEmb b.target.valid.host)
local notation "paid" bits_ => Census.count A (Equiv.refl (Fin gs)) hosts bits_
local notation "ext" => Computability.BorderVNP.FragmentBucket.count homes
local notation "arch" => NativeBranch.archive X G S b hp

variable {paidBits nodeBits extBits M w lo : ℕ} (previous : Block k→Bank) (counts : Bank)
local notation "out" => lo+DescentTerminalPopulation.RAM.lease H gs M paidBits extBits lo
local notation "written" => DescentTerminalPopulation.RAM.done H gs M paidBits nodeBits extBits lo previous counts
local notation "page" => DescentTerminalPopulation.RAM.population H gs M paidBits extBits lo
local notation "code" => DescentTerminalPopulation.RAM.issue H gs M paidBits nodeBits extBits lo previous counts w

theorem population_page (m : Memory w) (hm : 0<M) (wide : nodeBits*gs≤w)
    (recFit : ∀v:(N).Site,((A).records v).length<2^paidBits)
    (nodeFit : ∀v:(N).Site,Fintype.card ((arch).bit.recipe v).Node<2^nodeBits)
    (exterior : cap_<2^extBits) (fit : ∀x:Block k,
      DescentTerminalPopulation.RAM.Fit H gs M paidBits extBits lo (previous x) counts out w)
    (space : out+2^k*H<2^w)
    (old : ∀x:Block k,∀j:Row H gs M,m ((previous x).base+(row H gs M j).val)=
      ((data (fun h g=>(paid paidBits) h g x) j).val:Computability.VPVNP.BurstRAM.Word w))
    (members : ∀h:Fin H,m (counts.base+h.val)=(ext h:Computability.VPVNP.BurstRAM.Word w)) :
    (code).Exec m (written m) (DescentTerminalPopulation.RAM.ticks H gs M paidBits extBits lo previous counts) ∧
    CheapCode code ∧
    (∀v:(N).Site,digit nodeBits ((A).pos v).1.val ((written m) ((page ((A).block v)).base+(b.target.home v).val)).val=
      Fintype.card ((arch).bit.recipe v).Node) ∧
    ∀i,i<lo ∨ out+2^k*H≤ i→written m i=m i := by
  obtain ⟨cpu,cheap,frame⟩:=DescentTerminalPopulation.RAM.run H gs M paidBits nodeBits extBits lo previous counts m fit space
  let cards:=fun h:Fin H=>(⟨ext h,(cohort_cap X G S b hp base h).trans_lt exterior⟩ : Cell extBits)
  refine ⟨cpu,cheap,?_,frame⟩
  intro v
  have stored:=DescentTerminalPopulation.RAM.read H gs M paidBits nodeBits extBits lo previous counts m fit space
    (fun x h j=>(paid paidBits) h j x) cards old members ((A).block v) (b.target.home v)
  rw [stored]
  exact true_population_word X G S b hp base hm wide recFit nodeFit v

include base in
/-- The public paper-level scalar bound bounds both possible numerical
formats when both the charged column and the terminal field use this width. -/
theorem population_page_limits (hh : 0<S.height) (localFit : S.epochPower^S.localTokenExponent<2^paidBits)
    (terminalFit : S.epochPower^S.localTokenExponent<2^nodeBits) :
    (∀v:(N).Site,((A).records v).length<2^paidBits) ∧
      ∀v:(N).Site,Fintype.card ((arch).bit.recipe v).Node<2^nodeBits := by
  have nodes:=site_nodes X G S b hp hh
  refine ⟨fun v=>?_,fun v=>(nodes v).trans_lt terminalFit⟩
  exact (Nat.le_add_right ((A).records v).length _).trans_lt
    ((node_population X G S b hp base v) ▸ (nodes v).trans_lt localFit)


open DescentTerminalPacketSlotRAM DescentTerminalExteriorPackets DescentTerminalFrozenRoster
variable (oldHome : Bank) (ord : ProtocolRAMEndpointSort.Layout) (prior : Memory w) (alive : 0<S.hostSize S.length)
local notation "num" => E*2^f
local notation "filled" => after ord num H (sorted oldHome ord H num alive prior)
local notation "histogram" => (⟨ord.counts,Nat.clog 2 H⟩ : Bank)
local notation "frozen" => fun t:Cohort=>(finProdFinEquiv.symm t : Fin E×Fin (2^f)).2
variable (shelf : DescentCensusRAM.Banks w (Fintype.card (Port P X.width) * 2 ^ b.path.frozen) (S.hostSize S.length + 1)) (fbank offs prod : Bank)
local notation "roster" => fromSort num H ord fbank offs prod
local notation "bill" => DescentCensusRAM.tallyCost shelf (tag roster shelf.bins H) (value roster)

theorem population_after_roster (sortRoom : SortRoom oldHome ord w num H)
    (sortEnd : DescentTerminalPacketSlotRAM.out ord num H+num<2^w)
    (home : ∀u,oldHome.read prior (u.val:Computability.VPVNP.BurstRAM.Word w)=((homes u).val:Computability.VPVNP.BurstRAM.Word w))
    (ids : ∀u:Cohort,fbank.read filled (u.val:Computability.VPVNP.BurstRAM.Word w)=((frozen u).val:Computability.VPVNP.BurstRAM.Word w))
    (before : ord.counts+H≤ shelf.first) (lits : Literals f cap_ roster filled)
    (keyFit : (tag roster shelf.bins H).Fits w shelf.first) (fieldFit : (value roster).Fits w shelf.first)
    (old : ∀x:Block k,∀j:Row H gs M,filled ((previous x).base+(row H gs M j).val)=
       ((data (fun h g=>(paid paidBits) h g x) j).val:Computability.VPVNP.BurstRAM.Word w))
    (oldSaved : ∀x:Block k,(previous x).base+H*chunks gs M≤ shelf.first)
    (booksAt : shelf.bins+H≤lo) (hm : 0<M) (wide : nodeBits*gs≤w)
    (recFit : ∀v:(N).Site,((A).records v).length<2^paidBits)
    (nodeFit : ∀v:(N).Site,Fintype.card ((arch).bit.recipe v).Node<2^nodeBits)
    (extFit : cap_<2^extBits)
    (fit : ∀x:Block k,DescentTerminalPopulation.RAM.Fit H gs M paidBits extBits lo
      (previous x) histogram out w) (room : out+2^k*H<2^w) :
    ∃mem,((DescentTerminalFrozenRoster.program shelf roster).seq
      (DescentTerminalPopulation.RAM.issue H gs M paidBits nodeBits extBits lo previous histogram w)).Exec
      filled mem (bill+DescentTerminalPopulation.RAM.ticks H gs M paidBits extBits lo previous histogram) ∧
      (∀v:(N).Site,digit nodeBits ((A).pos v).1.val (mem ((page ((A).block v)).base+(b.target.home v).val)).val=
        Fintype.card ((arch).bit.recipe v).Node) ∧
      (∀h:Fin H,mem (shelf.bins+h.val)=((book homes frozen h).val:Computability.VPVNP.BurstRAM.Word w)) ∧
      ∀x,x<shelf.first→x<lo→mem x=filled x := by
  obtain ⟨mid,built,ranks,same_⟩:=published_counts oldHome ord prior alive sortRoom sortEnd homes frozen
    home shelf cap_ (cohort_cap X G S b hp base) fbank offs prod ids before lits keyFit fieldFit
  have stored (x : Block k) (j : Row H gs M) : mid ((previous x).base+(row H gs M j).val)=
      ((data (fun h g=>(paid paidBits) h g x) j).val:Computability.VPVNP.BurstRAM.Word w) :=
    (same_ _ ((Nat.add_lt_add_left (row H gs M j).isLt _).trans_le (oldSaved x))).trans (old x j)
  obtain ⟨run,_,nodes,frame⟩:=population_page X G S b hp base previous histogram mid hm wide recFit nodeFit
    extFit fit room stored (fun h=>(ranks h).2)
  exact ⟨_,built.then run,nodes,fun h=>(frame _ (.inl ((Nat.add_lt_add_left h.isLt _).trans_le booksAt))).trans
    (ranks h).1,fun x hx low=>(frame x (.inl low)).trans (same_ x hx)⟩

end NativeBranch
end
end Hierarchy.DescentSixParty

end OAI
