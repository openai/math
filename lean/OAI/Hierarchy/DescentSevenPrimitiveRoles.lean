import OAI.Hierarchy.DescentPostedPrimitiveRoles
import OAI.Hierarchy.DescentAcquiredSpanRegister
import OAI.Hierarchy.DescentRegisteredSevenSpans
import OAI.Hierarchy.DescentResetPublicationGeometry
import OAI.Hierarchy.DescentDateTaggedOrdinals

namespace OAI
/-! # Both funded census and primitive role pages from the actual seven-field publication -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentSixParty DescentCompiler DescentResetGates DescentKernelHistory DescentEpochTagKeys
open scoped Classical Fin.CommRing
open DescentSIMDLookup DescentPackedResetRotorRoles DescentPackedZip DescentPackedColony DescentPrimitivePalette
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000

variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "v₀" => a.successor
local notation "base" => a.rebased floor
local notation "F" => z.menu.F
local notation "G" => z.menu.gadget
local notation "s" => z.menu.stageBits
local notation "Z" => z.menu.grain
local notation "op" => z.menu.op
local notation "pr" => (v₀).primitive
local notation "chart" => (pr).chart
local notation "md₀" => (v₀).metadata
variable {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {q ε : ℝ} {S : AtomSchedule} {k i grain D wire hist n h C f g cut tail p : ℕ}
    {prev : Reached W G q ε S k i grain D wire s} {ctl : ResetRates G S k D n h C f g cut tail}
    (menu : Runnable F op) (closed : ClosedReset prev ctl) (hp : 0<p) (whole : p∣closed.reset.unit)
    (fixed : Chronology.resetSpec closed=op) (history : Chronology.Archive W)
    (old : Encoding (Label G s Z op) (dictionary G op menu p) history.bit)
local notation "next" => (Chronology.resetArchive closed p hp whole history).bit
local notation "enc" => Encoding.reset op menu closed hp whole fixed history old
local notation "gate" => reachedInput G s Z op menu closed hp whole history old

variable (earlier : DescentLocalArchiveOrder.Local history.bit)
    (blocks : (chart).blocks=2^k) (hosts : (chart).hosts=S.hostSize (i+1)) (groups : (chart).groups=S.groupCount (i+1))
local notation "current" => DescentLocalArchiveOrder.reset closed p hp whole history earlier

open DescentPacking.PackedMatch.Local.Stage DescentResetActorClass NodeOrder Reached.NodeCells
open DescentKernelHistory DescentResetMetadataInputs DescentPackedColony
open scoped Classical Fin.CommRing
local notation "B₀" => (v₀).birth
local notation "ℒ" => (B₀).placement
local notation "at₀" => (v₀).actor.directory ((v₀).middle.stop base)
local notation "T" => (v₀).metadata.chart
local notation "Y" => closed.next
local notation "m" => closed.reset.unit/p
local notation "fit₀" => (Nat.div_mul_cancel whole).symm
local notation "key" => DescentOrderedReset.grains W closed.count closed.order
local notation "prog" => closed.reset.laneRecipe key m p hp fit₀
local notation "plan" => closed.reset.laneShape key m p hp fit₀
local notation:max "rootSite" wing:arg g:arg vtx:arg => (⟨(wing,.inl g),⟨vtx,.inl false⟩⟩:closed.reset.bank.Site)
local notation "orig" => resetOrigin closed hp whole history
local notation "cell" => nodeCell z closed hp whole history earlier blocks hosts groups
local notation "rack" => (Y).vertex.trans (Fin.castLEEmb (Y).valid.host)
local notation "res" => closed.reset.k-closed.terminals.commonDepth

variable [Fintype P] (recorded:closed.Recorded p) (tokens:history.bit.Tokenized prev.placement.records)
variable (classSize:(B₀).classBits=indexBits closed.reset.n res)
    (rootCount:2*(2^res*2^closed.reset.n)=(B₀).roots)
    (fullHost:(chart).hosts=(ℒ).newHosts) (fullGroup:(chart).groups=(ℒ).groups)
    (sameBus:(chart).lanes=(ℒ).lanes) (sameRaw:(pr).rawBits=(B₀).rootBits)
local notation "ph" => fullHost.symm.trans hosts
local notation "pg" => fullGroup.symm.trans groups
local notation:max "cls" rr:arg => Fin.cast (congrArg (fun j : ℕ=>2^j) classSize.symm)
    ((ClosedReset.Window.paidActorAt closed (Fin.cast ph rr)).elim 0 (fun actor=>indexed closed.reset.graph res actor.val))
local notation:max "pay" x:arg rr:arg gg:arg => Census.count (Y).placement (Equiv.refl _) rack (B₀).paidBits
      (Fin.cast ph rr) (Fin.cast pg gg) (Fin.cast blocks x)
local notation:max "oldCell" x:arg n:arg rr:arg gg:arg => cell x n (Fin.cast fullHost.symm rr) (Fin.cast fullGroup.symm gg)

open DescentSixParty.Chronology.DatePorts
local notation "ports" => DescentSixParty.Chronology.DatePorts.reset a floor u
variable (places : RangeRoom ports closed.next next)
local notation "atOutput" => slotAt ports closed.next next current places

open DescentBundleHistory DescentLocalArchiveOrder DescentRetainedRangeDigits
variable {R : ℕ} (sh : WorldShape p R history.bit) (one : 1≤R)
    (pos : 0<closed.reset.unit) (wide : max 1 (max closed.reset.width (C*closed.reset.width))≤R)
local notation "split_" => sh.granular closed.count (grain*(G).b) closed.fit hp (closed.unit ▸ pos) (closed.unit ▸ whole)
local notation "installed" => reentryWorldShape split_ closed.reset closed.terminals key _ hp fit₀ (Chronology.resetMenu closed) one wide
local notation "after_" => WorldShape.follow hp pos whole closed.reblock closed.cuts installed
local notation "xx" x:arg => Fin.cast (blocks.trans (congrArg (2^·) places.radix)) x
local notation "ig" g:arg => Fin.cast ((fullGroup.symm.trans groups).trans places.groups) g

open DescentOperandStateBanks DescentDatedNodeMetadata
private theorem source_chart {H H' K K' b b' M M' : ℕ} (hostEq:H=H') (grpEq:K=K') (bits:b=b') (bus:M=M')
    (expr : Expr) (values:Fin H→Fin K→Cell b) (mem:Memory w) (read:Source expr values M mem):
    Source expr (fun h g=>(values (h.cast hostEq.symm) (g.cast grpEq.symm)).cast (congrArg (2^·) bits)) M' mem:=by
  subst H';subst K';subst b';subst M';exact read

local notation "c₀" => (ports).metadataChart
local notation "c₁" => (v₀).metadata.chart
local notation "actor" => (v₀).receiver
local notation "A" => u.operand
local notation "L₀" => (ports).rangeLayout
local notation "R₁" => (v₀).rangeLayout

include recorded tokens rootCount sameBus sameRaw in
theorem from_seven_paid_roles {before mid dst : Memory w} (done_ : (date z).Runs before dst)
    (spent : u.throughOperandDate.Runs before mid) (ready:u.Ready) (safe:z.Room)
    (allBlocks:(T).blocks≤2^(v₀).venue.next.k)
    (roots : RootRegister closed hp whole history earlier B₀ z.guards (z.classImage mid)
      (z.birthBlocks.symm.trans blocks) ph pg)
    (nonempty:0<(B₀).sourceLanes)
    (count:z.venueImage mid (at₀).count.base=(Fintype.card (Y).V:Computability.VPVNP.BurstRAM.Word w))
    (inverse:∀i:Fin (Fintype.card (Y).V),z.venueImage mid ((at₀).inverse.base+i.val)=((ClosedReset.Window.originalCompactName closed (S.hostSize _) prev.valid.host i).val:Computability.VPVNP.BurstRAM.Word w))
    (narrow:Fintype.card (Y).V<2^w) (room:(ℒ).newHosts≤2^w) (saved:Fintype.card (Y).V≤(at₀).inverse.size)
    (fits:∀v,((Y).placement.records v).length<2^(B₀).paidBits)
    (kinds:Source (classWord u) (fun h (_ : Fin (ℒ).groups) => cls h) (ℒ).lanes (z.classImage mid))
    (rawPaid:∀x : DescentColonies.Block k,Source (.lookup (((v₀).venue.sources (predecessor u) ((v₀).fundedEnd base)).paid x.val) .row)
      (fun h g=>Census.count (Y).placement (Equiv.refl _) rack (B₀).paidBits h g x) (ℒ).lanes (z.venueImage mid))
    (oldPorts : Chronology.DatePorts) {driftBudget : ℕ}
    (layout : ResetPublicationGeometry G S i driftBudget oldPorts ports u)
    (nodeCount:(ports).nodes=(chart).nodes) (racks:(ports).operandHosts=(chart).hosts)
    (hostAxis : (c₁).hosts=(ℒ).newHosts) (grpAxis : (c₁).groups=(ℒ).groups)
    (laneAxis : (c₁).lanes=(ℒ).lanes) (spanAxis : (md₀).spanBits=(B₀).spanBits)
    (paidAxis : (md₀).paidBits=(B₀).paidBits)
    (arity:∀v (atom:((prog) v).Node),((plan v).recipe hp).arity atom≤(B₀).arguments)
    (wordRoom : (actor).signedBits*(actor).lanes≤w) (actorMem:Memory w)
    (issued : u.ThroughActors before actorMem)
    (choice : ∀i,OrdinalRead u ready layout.small actorMem i)
    (nodeFeatures : SevenSpans u (Y) next current places after_ ready layout.small layout.axes actorMem choice)
    (vacant : SevenVacant u (Y) next current places ready layout.small layout.axes actorMem choice)
    (retained : ∀x n,Source (z.roles.retained x n) (fun h g=>DescentResetPrimitivePage.oldWord
      ((cell x n h g).elim .padding gate)) (chart).lanes (z.roleInput mid))
    (bits : (chart).bits=printedBits G s Z op) (width : roleBits closed.reset.n≤(pr).rawBits)
    :
    (∀x,Source (paid u x) (fun h g=>Census.count (Y).placement (Equiv.refl _) rack (md₀).paidBits
      ((h.cast (congrArg Chart.hosts layout.chart).symm).cast layout.hosts)
      ((g.cast (congrArg Chart.groups layout.chart).symm).cast places.groups.symm)
      ((x.cast (congrArg Chart.blocks layout.chart).symm).cast (congrArg (2^·) places.radix.symm)))
      (c₁).lanes (z.venueImage mid)) ∧
    PrimitiveRolesAt u (Y) next current places op (enc).atNode dst :=by
  obtain ⟨sp,reads,values⟩:=acquired_span_register u (Y) next current places after_ z ready safe spent
    layout.small layout.axes layout.chart actorMem issued choice nodeFeatures vacant layout.positiveLanes wordRoom
    layout.receiverHosts layout.receiverGroups layout.receiverLanes layout.spanBits
  let F6 (x:Fin (chart).blocks) (n:Fin (chart).nodes) (j:Fin (B₀).arguments) (h₀:Fin (ℒ).newHosts)
      (g₀:Fin (ℒ).groups) :=(sp (x.cast z.censusBlocks) (n.cast z.censusNodes) (j.cast z.birthArgs)
        (h₀.cast hostAxis.symm) (g₀.cast grpAxis.symm)).cast (congrArg (2^·) spanAxis)
  have posted x n j : Source (z.spans (Fin.cast z.censusBlocks x) (Fin.cast z.censusNodes n) (Fin.cast z.birthArgs j))
      (F6 x n j) (ℒ).lanes (z.venueImage mid):=source_chart hostAxis grpAxis spanAxis laneAxis _ _ _
        (reads (x.cast z.censusBlocks) (n.cast z.censusNodes) (j.cast z.birthArgs))
  have acquisition:=z.posted_paid_roles menu closed hp whole fixed history old earlier blocks hosts groups recorded tokens
    classSize rootCount fullHost fullGroup sameBus sameRaw places sh one pos wide done_ spent ready safe allBlocks
    roots nonempty count inverse narrow room saved fits F6 kinds rawPaid posted nodeCount racks arity
    (fun x slot j h₀ g₀=>by
      exact values (x.cast z.censusBlocks) (slot.cast z.censusNodes) (j.cast z.birthArgs)
        (h₀.cast hostAxis.symm) (g₀.cast grpAxis.symm)) retained bits width
  refine ⟨?_,acquisition.2⟩
  intro x
  have funded:=acquisition.1 (x.cast z.censusBlocks.symm)
  have forward:=source_chart hostAxis.symm grpAxis.symm paidAxis.symm laneAxis.symm _ _ _ funded
  have indexEq : (x.cast z.censusBlocks.symm).cast z.censusBlocks = x := Fin.ext rfl
  rw [indexEq] at forward
  convert forward using 1
  funext h g
  apply Fin.ext
  simp only [Fin.val_cast]
  exact congrArg (fun b : ℕ => (Census.count (Y).placement (Equiv.refl _) rack b
    ((h.cast (congrArg Chart.hosts layout.chart).symm).cast layout.hosts)
    ((g.cast (congrArg Chart.groups layout.chart).symm).cast places.groups.symm)
    ((x.cast (congrArg Chart.blocks layout.chart).symm).cast (congrArg (2^·) places.radix.symm))).val) paidAxis

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
