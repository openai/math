import OAI.Hierarchy.DescentDatedPrimitiveArchiveFromRoot
import OAI.Hierarchy.DescentResetArchiveCertificate
import OAI.Hierarchy.DescentRetainedResetRangeOrigin
import OAI.Hierarchy.DescentRootPrimitivePaidRead

namespace OAI
/-! # Primitive role and funded rows on the reached reset archive -/
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

omit [Fintype P] in
/-- A flattened f6 reading at the registered node gives the actual argument's
span on the original diagram, including operands above the node's arity. -/
theorem original_bank_width
    (nodeCount:(ports).nodes=(chart).nodes) (racks:(ports).operandHosts=(chart).hosts)
    (x:Fin (chart).blocks) (slot:Fin (chart).nodes) (h₀:Fin (ℒ).newHosts) (g₀:Fin (ℒ).groups)
    (atom : NodeOrder.All next) (v:NodeOrder.Global prog)
    (entered:oldCell x slot h₀ g₀=some atom) (owned:orig atom=.inr (.inr v)) (j:ℕ) :
    (atOutput (xx x) (slot.cast nodeCount.symm) (h₀.cast (fullHost.symm.trans racks.symm)) (ig g₀)).elim 0
      (fun y=>atSlot ((after_).sites y.1) y.2 j 2)=argumentSpan (plan v.1) v.2 j :=by
  have located:=z.registered_node_slot closed hp whole history earlier blocks hosts groups places nodeCount racks
    (xx x) (slot.cast nodeCount.symm) (h₀.cast (fullHost.symm.trans racks.symm)) (ig g₀)
  have atCell : atOutput (xx x) (slot.cast nodeCount.symm) (h₀.cast (fullHost.symm.trans racks.symm)) (ig g₀)=some atom:=
    located.symm.trans entered
  have nodeFeatures:=reset_range_origin closed hp whole history sh one pos wide atom
  change (after_).nodeFields atom=_ at nodeFeatures
  rw [owned] at nodeFeatures
  simp only [Sum.elim_inr] at nodeFeatures
  rw [atCell,Option.elim_some,←atSlot_count]
  exact of_fields _ _ _ _ nodeFeatures _ _

include recorded tokens rootCount sameBus sameRaw in
theorem posted_paid_roles {before mid dst : Memory w} (done_ : (date z).Runs before dst)
    (spent : u.throughOperandDate.Runs before mid) (ready:u.Ready) (safe:z.Room)
    (allBlocks:(T).blocks≤2^(v₀).venue.next.k)
    (roots : RootRegister closed hp whole history earlier B₀ z.guards (z.classImage mid)
      (z.birthBlocks.symm.trans blocks) ph pg)
    (nonempty:0<(B₀).sourceLanes)
    (count:z.venueImage mid (at₀).count.base=(Fintype.card (Y).V:Computability.VPVNP.BurstRAM.Word w))
    (inverse:∀i:Fin (Fintype.card (Y).V),z.venueImage mid ((at₀).inverse.base+i.val)=((ClosedReset.Window.originalCompactName closed (S.hostSize _) prev.valid.host i).val:Computability.VPVNP.BurstRAM.Word w))
    (narrow:Fintype.card (Y).V<2^w) (room:(ℒ).newHosts≤2^w) (saved:Fintype.card (Y).V≤(at₀).inverse.size)
    (fits:∀v,((Y).placement.records v).length<2^(B₀).paidBits)
    (F6:Fin (chart).blocks→Fin (chart).nodes→Fin (B₀).arguments→Fin (ℒ).newHosts→Fin (ℒ).groups→Cell (B₀).spanBits)
    (kinds:Source (classWord u) (fun h (_ : Fin (ℒ).groups) => cls h) (ℒ).lanes (z.classImage mid))
    (rawPaid:∀x : DescentColonies.Block k,Source (.lookup (((v₀).venue.sources (predecessor u) ((v₀).fundedEnd base)).paid x.val) .row)
      (fun h g=>Census.count (Y).placement (Equiv.refl _) rack (B₀).paidBits h g x) (ℒ).lanes (z.venueImage mid))
    (spans:∀x slot j,Source (z.spans (x.cast z.censusBlocks) (slot.cast z.censusNodes) (j.cast z.birthArgs)) (F6 x slot j)
      (ℒ).lanes (z.venueImage mid))
    (nodeCount:(ports).nodes=(chart).nodes) (racks:(ports).operandHosts=(chart).hosts)
    (arity:∀v (atom:((prog) v).Node),((plan v).recipe hp).arity atom≤(B₀).arguments)
    (spanAt:∀x slot j h g,(F6 x slot j h g).val=
      (atOutput (xx x) (slot.cast nodeCount.symm) (h.cast (fullHost.symm.trans racks.symm)) (ig g)).elim 0
        (fun y=>atSlot ((after_).sites y.1) y.2 j.val 2))
    (retained : ∀x n,Source (z.roles.retained x n) (fun h g=>DescentResetPrimitivePage.oldWord
      ((cell x n h g).elim .padding gate)) (chart).lanes (z.roleInput mid))
    (bits : (chart).bits=printedBits G s Z op) (width : roleBits closed.reset.n≤(pr).rawBits)
    :
    (∀x,Source (paid u (x.cast z.censusBlocks)) (fun h g=>pay x h g) (ℒ).lanes (z.venueImage mid)) ∧
    PrimitiveRolesAt u (Y) next current places op (enc).atNode dst :=by
  have paidRows:=z.root_funded_acquired (Y) blocks hosts groups fullHost fullGroup mid rawPaid
  refine ⟨paidRows,fun x=>?_⟩
  apply z.from_root_archive menu closed hp whole fixed history old earlier blocks hosts groups recorded tokens
    classSize rootCount fullHost fullGroup sameBus sameRaw places done_ spent ready safe allBlocks roots
    nonempty count inverse narrow room saved fits F6 kinds paidRows spans _ retained bits width nodeCount racks x
  intro blk slot h₀ g₀ atom v entered owned
  exact ⟨arity _ _,fun j=>(spanAt blk slot j h₀ g₀).trans
    (z.original_bank_width closed hp whole history earlier blocks hosts groups fullHost fullGroup places
      sh one pos wide nodeCount racks blk slot h₀ g₀ atom v entered owned j.val)⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
