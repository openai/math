import OAI.Hierarchy.DescentDatedPrimitiveBirthSource
import OAI.Hierarchy.DescentPhysicalBankPrimitive
import OAI.Hierarchy.DescentTerminalResetNodeCells

namespace OAI
/-! # Fresh and relay role registers on every coordinate of the installed date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentSixParty DescentCompiler DescentResetGates DescentKernelHistory DescentEpochTagKeys
open DescentSIMDLookup DescentPackedResetRotorRoles DescentPackedZip DescentPackedColony DescentPrimitivePalette
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false

theorem source_axes {w H H' G G' t t' L L' : ℕ} (e : Expr) (ram : Memory w)
    (sh:H'=H) (sg:G'=G) (st:t'=t) (sl:L'=L)
    (a:Fin H→Fin G→Cell t) (b:Fin H'→Fin G'→Cell t')
    (read:Source e a L ram) (agree:∀h g,((b h g).val)=(a (h.cast sh) (g.cast sg)).val) :
    Source e b L' ram:=by
  subst H';subst G';subst t';subst L'
  have same:b=a:=funext fun h=>funext fun g=>Fin.ext (agree h g)
  exact same.symm ▸ read

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
/-- The authentic prepared root pages, compact count/inverse, paid count, class and F6
registers suffice. Inactive positions are settled by the actual funded population. -/
theorem born_registers {U : ℕ} (mid : Memory w) (ready:u.Ready) (safe:z.Room)
    (allBlocks:(T).blocks≤2^(v₀).venue.next.k) (depth:(B₀).Population) (original:(B₀).Original)
    (prepared:(B₀).Observed z.guards (z.classImage mid) depth original)
    (nonempty:0<(B₀).sourceLanes) (name:Fin U→Fin (ℒ).sparse)
    (count:z.venueImage mid (at₀).count.base=(U:Computability.VPVNP.BurstRAM.Word w))
    (inverse:∀i:Fin U,z.venueImage mid ((at₀).inverse.base+i.val)=((name i).val:Computability.VPVNP.BurstRAM.Word w))
    (narrow:U<2^w) (room:(ℒ).newHosts≤2^w) (saved:U≤(at₀).inverse.size)
    (fits:∀v,((Y).placement.records v).length<2^(B₀).paidBits)
    (x:Fin (chart).blocks) (slot:Fin (chart).nodes)
    (F6:Fin (B₀).arguments→Fin (ℒ).newHosts→Fin (ℒ).groups→Cell (B₀).spanBits)
    (kinds:Source (classWord u) (fun h (_ : Fin (ℒ).groups) => cls h) (ℒ).lanes (z.classImage mid))
    (funded:Source (paid u (x.cast z.censusBlocks)) (fun h g=>pay x h g) (ℒ).lanes (z.venueImage mid))
    (spans:∀j,Source (z.spans (x.cast z.censusBlocks) (slot.cast z.censusNodes) (j.cast z.birthArgs)) (F6 j)
      (ℒ).lanes (z.venueImage mid))
    (ranges:∀h g atom (v:NodeOrder.Global prog),oldCell x slot h g=some atom→ orig atom=.inr (.inr v)→
      ((plan v.1).recipe hp).arity v.2≤(B₀).arguments ∧ ∀j,(F6 j h g).val=argumentSpan (plan v.1) v.2 j.val)
    (rotations:∀h g atom wing₀ good vtx (o:(prog (rootSite wing₀ good vtx)).Node) (row:Fin (B₀).roots)
      (r:Fin (closed.reset.circuit wing₀ good).layers), oldCell x slot h g=some atom→
      orig atom=.inr (.inr ⟨rootSite wing₀ good vtx,o⟩)→
      (originClass closed hp whole history (.inr (.inr ⟨rootSite wing₀ good vtx,o⟩))).val=6+row.val→
      slot.val/m=r.val→(B₀).rootActual depth original name (slot.cast z.birthNodes) (x.cast z.birthBlocks) row h g=
      (rotorNumber ((closed.reset.circuit wing₀ good).rotation r) vtx:Cell (B₀).rootBits)) :
    Source (z.roles.fresh x slot) (fun h g=>(DescentResetPrimitivePage.localRole ((cell x slot h g).elim .padding gate):Cell (pr).rawBits))
      (chart).lanes (z.roleInput mid) ∧
    Source (z.roles.relay x slot) (fun h g=>DescentResetPrimitivePage.relayFlag ((cell x slot h g).elim .padding gate))
      (chart).lanes (z.roleInput mid):=by
  have raw:=z.birth_sources mid ready safe allBlocks depth original prepared nonempty name count inverse narrow room saved x slot
    (fun h (_ : Fin (ℒ).groups) => cls h) (fun h g=>pay x h g) F6 kinds funded spans
  constructor
  · apply source_axes _ _ fullHost fullGroup sameRaw sameBus _ _ raw.1
    intro h g
    let h':=h.cast fullHost
    let g':=g.cast fullGroup
    let words:=fun row=>(B₀).rootActual depth original name (slot.cast z.birthNodes) (x.cast z.birthBlocks) row h' g'
    have actual:=physical_birth_word closed hp whole history earlier recorded tokens (B₀) classSize rootCount fits
      (x.cast blocks) (slot.cast z.birthNodes) (h'.cast ph) (g'.cast pg) (fun j=>F6 j h' g') words
      (ranges h' g') (rotations h' g')
    have sameCell : whereAt (Y) next current (x.cast blocks) (slot.cast z.birthNodes)
        (h'.cast ph) (g'.cast pg) = cell x slot h g := rfl
    rw [actual,sameCell]
    cases found:cell x slot h g with
    | none=>rfl
    | some atom=>
      dsimp only [Option.elim_some]
      cases tag:orig atom with
      | inl v=>simp [reachedInput,tag,DescentResetPrimitivePage.localRole]
      | inr v=>
        rcases v with edge|v
        · simp [reachedInput,tag,DescentResetPrimitivePage.localRole]
        · simp [reachedInput,tag,DescentResetPrimitivePage.localRole,sameRaw]
  · apply source_axes _ _ fullHost fullGroup rfl sameBus _ _ raw.2
    intro h g
    have actual := relay_at_slot closed hp whole history earlier recorded tokens fits
      (x.cast blocks) slot (h.cast hosts) (g.cast groups)
    rw [DescentPrimitiveBirth.Layout.relay_at]
    refine Eq.trans ?_ (congrArg Fin.val actual.symm)
    have sameCell : whereAt (Y) next current (x.cast blocks) slot (h.cast hosts) (g.cast groups) =
        cell x slot h g := rfl
    rw [sameCell]
    cases found:cell x slot h g with
    | none=>rfl
    | some atom=>
      dsimp only [Option.elim_some]
      cases tag:orig atom with
      | inl v=>simp [reachedInput,tag,DescentResetPrimitivePage.relayFlag]
      | inr v=>rcases v with edge|v <;>simp [reachedInput,tag,DescentResetPrimitivePage.relayFlag]

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
