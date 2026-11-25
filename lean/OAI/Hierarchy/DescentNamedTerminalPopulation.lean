import OAI.Hierarchy.DescentNamedNativeCaps
import OAI.Hierarchy.DescentTerminalPopulationIssue

namespace OAI
/-! # Paid terminal scalar-node populations in the physically named seed chronology -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical Fin.CommRing
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
local notation "exteriorCount" => Computability.BorderVNP.FragmentBucket.count homes
local notation "arch" => Branch.archive X G S b hp

theorem node_population (v : (N).Site) :
    Fintype.card ((arch).bit.recipe v).Node=((A).records v).length+exteriorCount (b.target.home v) := by
  have live:=(site_particles X G S b hp).nodes v
  have attached : (W).exteriorTokens v=exteriorCount (b.target.home v) := by
    rw [(W).exterior_token_card]
    simpa using Fintype.card_congr (densePinEquiv X G S b hp base v)
  exact live.trans (congrArg (((A).records v).length+·) attached)

private theorem invoice_lane {paidBits : ℕ} (v : (N).Site) (fits : ((A).records v).length<2^paidBits) :
    ((paid paidBits) (b.target.home v) ((A).pos v).1 ((A).block v)).val=((A).records v).length := by
  have witness : ∃h,hosts h=b.target.home v := ⟨((A).pos v).2,rfl⟩
  have name : witness.choose=((A).pos v).2 := (hosts).injective witness.choose_spec
  rw [Census.count,dite_eq_left witness,name]
  have mass : PackedCensus.histories W (A).pos (A).block (A).records ((A).pos v) ((A).block v)=((A).records v).length := by
    unfold PackedCensus.histories StarKeys.blockMass
    rw [Finset.sum_eq_single v]
    · simp
    · intro u _ neq
      apply ite_eq_right
      exact fun h=>neq (b.target.valid.coordinates (Prod.ext h.1 h.2))
    · simp
  change ((PackedCensus.histories W (A).pos (A).block (A).records ((A).pos v) ((A).block v) : ℕ):Cell paidBits).val=_
  rw [mass,Fin.val_cast_of_lt fits]

/-- A nonempty frozen home has an actual site. A vacant block at that
same host therefore still has a bounded common exterior digit. -/
private theorem all_exterior_lanes (nodeBits : ℕ) (all : ∀v : (N).Site,Fintype.card ((arch).bit.recipe v).Node<2^nodeBits)
    (h : Fin H) : exteriorCount h<2^nodeBits := by
  classical
  by_cases head : ∃t:Cohort,homes t=h
  · obtain ⟨t,rfl⟩:=head
    let v:=(N).attach (atCohort X G S b hp base 0 t)
    have named : b.target.home v=homes t := rfl
    have count:=node_population X G S b hp base v
    have room:=all v
    rw [named] at count
    omega
  · have blank : exteriorCount h=0 := by
      change (Finset.univ.filter (fun j=>homes j=h)).card=0
      have empty : Finset.univ.filter (fun j=>homes j=h)=∅ := by ext j;simp;exact fun belongs=>head ⟨j,belongs⟩
      simp [empty]
    rw [blank];exact Nat.two_pow_pos _

/-- A vacant block has zero charged records, even at a host occupied by a different block. -/
private theorem invoice_blank (paidBits : ℕ) (h : Fin H) (j : Fin gs) (x : Block k)
    (away : ¬ ∃ v : (N).Site, b.target.home v = h ∧ ((A).pos v).1 = j ∧ (A).block v = x) :
    ((paid paidBits) h j x).val = 0 := by
  classical
  unfold Census.count
  split
  · rename_i present
    have blank : PackedCensus.histories W (A).pos (A).block (A).records (j,present.choose) x = 0 := by
      unfold PackedCensus.histories StarKeys.blockMass
      apply Finset.sum_eq_zero
      intro v _
      apply ite_eq_right
      intro both
      apply away
      refine ⟨v, ?_, congrArg Prod.fst both.1, both.2⟩
      change hosts ((A).pos v).2 = h
      rw [both.1]
      exact present.choose_spec
    change (((PackedCensus.histories W (A).pos (A).block (A).records (j,present.choose) x : ℕ) : Cell paidBits)).val = 0
    exact (congrArg (fun count : ℕ => (count : Cell paidBits).val) blank).trans (by simp)
  · rfl

theorem true_population_word {paidBits nodeBits w M : ℕ} (hm : 0<M) (wide : nodeBits*gs≤w)
    (recordFit : ∀v : (N).Site,((A).records v).length<2^paidBits)
    (nodeFit : ∀v : (N).Site,Fintype.card ((arch).bit.recipe v).Node<2^nodeBits)
    (v : (N).Site) :
    digit nodeBits ((A).pos v).1.val ((DescentTerminalPopulation.words (M:=M) nodeBits
      (fun h j=>(paid paidBits) h j ((A).block v)) exteriorCount (b.target.home v):Fin (2^w)).val)=
      Fintype.card ((arch).bit.recipe v).Node := by
  have lane (x : Block k) (h : Fin H) (j : Fin gs) : ((paid paidBits) h j x).val + exteriorCount h < 2^nodeBits := by
    by_cases live : ∃ z : (N).Site, b.target.home z=h ∧ ((A).pos z).1=j ∧ (A).block z=x
    · obtain ⟨z, rfl, rfl, rfl⟩ := live
      rw [invoice_lane X G S b (v:=z) (recordFit z), ← node_population X G S b hp base z]
      exact nodeFit z
    · rw [invoice_blank X G S b paidBits h j x live, Nat.zero_add]
      exact all_exterior_lanes X G S b hp base nodeBits nodeFit h
  rw [DescentTerminalPopulation.digit_word _ _ _ _ hm wide (lane _) _ _,
    invoice_lane X G S b (v:=v) (recordFit v), node_population X G S b hp base]

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
    (members : ∀h:Fin H,m (counts.base+h.val)=(exteriorCount h:Computability.VPVNP.BurstRAM.Word w)) :
    (code).Exec m (written m) (DescentTerminalPopulation.RAM.ticks H gs M paidBits extBits lo previous counts) ∧
    CheapCode code ∧
    (∀v:(N).Site,digit nodeBits ((A).pos v).1.val ((written m) ((page ((A).block v)).base+(b.target.home v).val)).val=
      Fintype.card ((arch).bit.recipe v).Node) ∧
    ∀i,i<lo ∨ out+2^k*H≤ i→written m i=m i := by
  obtain ⟨cpu,cheap,frame⟩:=DescentTerminalPopulation.RAM.run H gs M paidBits nodeBits extBits lo previous counts m fit space
  let cards:=fun h:Fin H=>(⟨exteriorCount h,(cohort_cap X G S b hp base h).trans_lt exterior⟩ : Cell extBits)
  refine ⟨cpu,cheap,?_,frame⟩
  intro v
  have stored:=DescentTerminalPopulation.RAM.read H gs M paidBits nodeBits extBits lo previous counts m fit space
    (fun x h j=>(paid paidBits) h j x) cards old members ((A).block v) (b.target.home v)
  rw [stored]
  exact true_population_word X G S b hp base hm wide recFit nodeFit v

open DescentTerminalPacketSlotRAM DescentTerminalExteriorPackets DescentTerminalFrozenRoster
variable (oldHome : Bank) (ord : ProtocolRAMEndpointSort.Layout) (prior : Memory w) (alive : 0<S.hostSize S.length)
local notation "num" => E*2^f
local notation "filled" => after ord num H (sorted oldHome ord H num alive prior)
local notation "histogram" => (⟨ord.counts,Nat.clog 2 H⟩ : Bank)
local notation "frozen" => fun t:Cohort=>(finProdFinEquiv.symm t : Fin E×Fin (2^f)).2
variable (shelf : DescentCensusRAM.Banks w (Fintype.card (Port P X.width) * 2 ^ b.path.frozen) (S.hostSize S.length + 1)) (fbank offs prod : Bank)
local notation "roster" => fromSort num H ord fbank offs prod
local notation "bill" => DescentCensusRAM.tallyCost shelf (tag roster shelf.bins H) (value roster)

/-- Start in the actual frozen-home packet-sort output. The roster finishes before
the charged-count page is read; every named final site sees its actual scalar-node count. -/
theorem issued_f3 (sortRoom : SortRoom oldHome ord w num H)
    (sortEnd : DescentTerminalPacketSlotRAM.out ord num H+num<2^w)
    (home : ∀u,oldHome.read prior (u.val:Computability.VPVNP.BurstRAM.Word w)=((homes u).val:Computability.VPVNP.BurstRAM.Word w))
    (ids : ∀u:Cohort,fbank.read filled (u.val:Computability.VPVNP.BurstRAM.Word w)=((frozen u).val:Computability.VPVNP.BurstRAM.Word w))
    (before : ord.counts+H≤ shelf.first) (lits : Literals f cap_ roster filled)
    (keyFit : (tag roster shelf.bins H).Fits w shelf.first) (fieldFit : (value roster).Fits w shelf.first)
    (old : ∀x:Block k,∀j:Row H gs M,filled ((previous x).base+(row H gs M j).val)=
       ((data (fun h g=>(paid paidBits) h g x) j).val:Computability.VPVNP.BurstRAM.Word w))
    (oldSaved : ∀x:Block k,(previous x).base+H*chunks gs M≤ shelf.first)
    (booksAt : shelf.bins+H≤lo) (hm : 0<M) (wide : nodeBits*gs≤w)
    (hh : 0<S.height) (paidRoom : S.epochPower^S.localTokenExponent<2^paidBits)
    (nodeRoom : S.epochPower^S.localTokenExponent<2^nodeBits)
    (extFit : cap_<2^extBits)
    (fit : ∀x:Block k,DescentTerminalPopulation.RAM.Fit H gs M paidBits extBits lo
      (previous x) histogram out w) (room : out+2^k*H<2^w) :
    ∃mem,((DescentTerminalFrozenRoster.program shelf roster).seq
      (DescentTerminalPopulation.RAM.issue H gs M paidBits nodeBits extBits lo previous histogram w)).Exec
      filled mem (bill+DescentTerminalPopulation.RAM.ticks H gs M paidBits extBits lo previous histogram) ∧
      CheapCode ((DescentTerminalFrozenRoster.program shelf roster).seq
        (DescentTerminalPopulation.RAM.issue H gs M paidBits nodeBits extBits lo previous histogram w)) ∧
      (∀v:(N).Site,digit nodeBits ((A).pos v).1.val (mem ((page ((A).block v)).base+(b.target.home v).val)).val=
        Fintype.card ((arch).bit.recipe v).Node) ∧
      (∀h:Fin H,mem (shelf.bins+h.val)=((book homes frozen h).val:Computability.VPVNP.BurstRAM.Word w)) ∧
      ∀x,x<shelf.first→x<lo→mem x=filled x := by
  have nodes := site_nodes X G S b hp hh
  have nodeFit (v : (N).Site) := (nodes v).trans_lt nodeRoom
  have recFit (v : (N).Site) : ((A).records v).length < 2^paidBits := by
    have total := (nodes v).trans_lt paidRoom
    rw [node_population X G S b hp base v] at total
    exact (Nat.le_add_right _ _).trans_lt total
  obtain ⟨mid,built,ranks,same_⟩:=published_counts oldHome ord prior alive sortRoom sortEnd homes frozen
    home shelf cap_ (cohort_cap X G S b hp base) fbank offs prod ids before lits keyFit fieldFit
  have stored (x : Block k) (j : Row H gs M) : mid ((previous x).base+(row H gs M j).val)=
      ((data (fun h g=>(paid paidBits) h g x) j).val:Computability.VPVNP.BurstRAM.Word w) :=
    (same_ _ ((Nat.add_lt_add_left (row H gs M j).isLt _).trans_le (oldSaved x))).trans (old x j)
  obtain ⟨run,cheap,nodes,frame⟩:=population_page X G S b hp base previous histogram mid hm wide recFit nodeFit
    extFit fit room stored (fun h=>(ranks h).2)
  exact ⟨_,built.then run,@cheap_seq w (DescentTerminalFrozenRoster.program shelf roster)
      (DescentTerminalPopulation.RAM.issue H gs M paidBits nodeBits extBits lo previous histogram w)
      (DescentCensusRAM.tally_cheap shelf (tag roster shelf.bins H) (value roster)) cheap,nodes,fun h=>(frame _ (.inl ((Nat.add_lt_add_left h.isLt _).trans_le booksAt))).trans
    (ranks h).1,fun x hx low=>(frame x (.inl low)).trans (same_ x hx)⟩

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
