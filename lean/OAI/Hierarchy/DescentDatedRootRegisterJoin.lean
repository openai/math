import OAI.Hierarchy.DescentDatedCanonicalBirthRegisters
import OAI.Hierarchy.DescentReachedRootRegister

namespace OAI
/-! # The reached root packet and the dated primitive role registers -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentSixParty DescentCompiler DescentResetGates DescentKernelHistory DescentEpochTagKeys
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
    {prev : Reached W G q ε S k i grain D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
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

include recorded tokens rootCount sameBus sameRaw in
theorem born_from_acquired (mid : Memory w) (ready:u.Ready) (safe:z.Room)
    (allBlocks:(T).blocks≤2^(v₀).venue.next.k)
    (roots : RootRegister closed hp whole history earlier B₀ z.guards (z.classImage mid)
      (z.birthBlocks.symm.trans blocks) ph pg)
    (nonempty:0<(B₀).sourceLanes)
    (count:z.venueImage mid (at₀).count.base=(Fintype.card (Y).V:Computability.VPVNP.BurstRAM.Word w))
    (inverse:∀i:Fin (Fintype.card (Y).V),z.venueImage mid ((at₀).inverse.base+i.val)=((ClosedReset.Window.originalCompactName closed (S.hostSize _) prev.valid.host i).val:Computability.VPVNP.BurstRAM.Word w))
    (narrow:Fintype.card (Y).V<2^w) (room:(ℒ).newHosts≤2^w) (saved:Fintype.card (Y).V≤(at₀).inverse.size)
    (fits:∀v,((Y).placement.records v).length<2^(B₀).paidBits)
    (x:Fin (chart).blocks) (slot:Fin (chart).nodes)
    (F6:Fin (B₀).arguments→Fin (ℒ).newHosts→Fin (ℒ).groups→Cell (B₀).spanBits)
    (kinds:Source (classWord u) (fun h (_ : Fin (ℒ).groups) => cls h) (ℒ).lanes (z.classImage mid))
    (funded:Source (paid u (x.cast z.censusBlocks)) (fun h g=>pay x h g) (ℒ).lanes (z.venueImage mid))
    (spans:∀j,Source (z.spans (x.cast z.censusBlocks) (slot.cast z.censusNodes) (j.cast z.birthArgs)) (F6 j)
      (ℒ).lanes (z.venueImage mid))
    (ranges:∀h g atom (v:NodeOrder.Global prog),oldCell x slot h g=some atom→ orig atom=.inr (.inr v)→
      ((plan v.1).recipe hp).arity v.2≤(B₀).arguments ∧ ∀j,(F6 j h g).val=argumentSpan (plan v.1) v.2 j.val) :
    Source (z.roles.fresh x slot) (fun h g=>(DescentResetPrimitivePage.localRole ((cell x slot h g).elim .padding gate):Cell (pr).rawBits))
      (chart).lanes (z.roleInput mid) ∧
    Source (z.roles.relay x slot) (fun h g=>DescentResetPrimitivePage.relayFlag ((cell x slot h g).elim .padding gate))
      (chart).lanes (z.roleInput mid) :=by
  refine z.born_registers menu closed hp whole history old earlier blocks hosts groups recorded tokens
    classSize rootCount fullHost fullGroup sameBus sameRaw mid ready safe allBlocks roots.population roots.words
    roots.seen nonempty roots.name count (fun v=>by simpa only [roots.name_val] using inverse v) narrow room saved fits x slot F6 kinds funded spans ranges ?_
  intro h g atom side good gateAt opAt row layer found origin number schedule
  exact roots.operation (slot.cast z.birthNodes) (x.cast z.birthBlocks) h g atom side good gateAt opAt row layer
    found origin number schedule

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
