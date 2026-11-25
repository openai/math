import OAI.Hierarchy.DescentRetainedPrivateSlotBook
import OAI.Hierarchy.DescentInstalledPrivateDonors

namespace OAI
/-! Original private words at an occupied primary of the normalized reset. -/
set_option quotPrecheck false
namespace Hierarchy.DescentRetainedPrivateSlotBook
open DescentBundleHistory DescentKernelHistory DescentSixParty DescentResetTrunks DescentRouterBank DescentNamedContact Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F P H Q Y : Type} [Field F] [Fintype H] [Fintype Q] {n d p bound L : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F n P bits} {B : BitDescription W} (src : WorldShape p bound B) (hp : 0<p) (one : 1≤bound)
variable (home : W.graph.Site→H) (group : Bool→W.graph.Edge→Q) (hub : H→Bool)
variable {w : W.graph.Edge→ℕ} (same : w=W.graph.width) (board : Network d (Bool×Q) (publicWidth group w))
variable (legacy sorted : board.Tables F) (ids : W.graph.Edge↪Fin L) (scalar : Y→List (List Bool)→F)
variable (prog : SiteBits (U:=Y) board) (valid : ReadsBits board scalar prog sorted) (device : ∀v,Shape p (prog v))
variable (limit : ∀v u j g,((device v).chunk u j g).stride≤bound) (widths : ∀e,p∣board.width e)
local notation "out" => installedWorldShape src hp one home group hub same board legacy sorted ids scalar prog valid device limit widths
local notation "siteAt" => (DescentResetTrunks.installedNames W home group hub same board legacy).symm
local notation "used" q:arg => (((out).sites (siteAt q)).recipe hp).UsedWord


def installed (h:H) : Donors (((out).sites (siteAt (.inl (false,h)))).recipe hp)
    (fun i:Fibre home h=>(src.sites i.val).recipe hp):=by
  subst w
  let actual:=gathered hp W.graph home group board ids src.edges B.recipe src.sites h
  refine ⟨actual.slots,actual.words,?_⟩
  rintro ⟨u,j⟩ word
  refine Iff.trans ?_ (actual.uses ⟨u,j⟩ word)
  exact (DescentLocalPrivateNames.read_some _ u j word).trans
    (DescentLocalPrivateNames.read_some ((inShape W.graph home group board ids src.edges B.recipe src.sites h).recipe hp) u j word).symm

local notation "installedIds" =>
  NodeOrder.installedNames B home group hub same board legacy sorted ids scalar prog valid

omit [Fintype Q] in
private theorem installed_owner_site (x : NodeOrder.All (B.installed home group hub same board legacy sorted ids scalar prog valid))
    (y : NodeOrder.All B) (origin : installedIds x=.inl y) :
    x.1=siteAt (.inl (false,home y.1)) := by
  have hx : x = (installedIds).symm (.inl y) :=
    (installedIds).injective (origin.trans ((installedIds).apply_symm_apply _).symm)
  subst x
  subst w
  obtain ⟨v,u⟩ := y
  rfl

omit [Fintype Q] in
private theorem installed_slot_origin (h : H)
    (s : DescentLocalPrivateNames.Slot (((out).sites (siteAt (.inl (false,h)))).recipe hp)) :
    let d := installed src hp one home group hub same board legacy sorted ids scalar prog valid device limit widths h
    installedIds ⟨siteAt (.inl (false,h)),s.1⟩=Sum.inl ⟨(d.slots s).1.val,(d.slots s).2.1⟩ ∧
      (d.slots s).2.2.val=s.2.val:=by
  subst w
  rcases s with ⟨⟨⟨v,eqn⟩,u⟩,j⟩
  subst h
  exact ⟨rfl,rfl⟩
end
end Hierarchy.DescentRetainedPrivateSlotBook

namespace Hierarchy.DescentRetainedPrivateSlotBook
open DescentSixParty DescentSixParty.ResetInput DescentKernelHistory DescentBundleHistory DescentNamedContact DescentRotor
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {n p bound : ℕ} {bits : P→ℕ} {W : MarkedWorld F n P bits} {B : BitDescription W}
    {price ε : ℝ} {h C Ht L : ℕ} (Z : ResetInput W price ε h C Ht) (T : Terminals Z)
variable (src : WorldShape p bound B) (ids : W.graph.Edge↪Fin L) (m : ℕ) (hp : 0<p) (fits : Z.unit=m*p)
variable (menu : ∀π,Configures F Z.graph.arcs C Z.width π) (one : 1≤bound) (wide : max 1 (max Z.width (C*Z.width))≤bound)
local notation "out" => reentryWorldShape src Z T ids m hp fits menu one wide
local notation "siteAt" => (resetNames Z T).symm
local notation "used" q:arg => (((out).sites (siteAt q)).recipe hp).UsedWord


local notation "laneScalar" => DescentLaneGates.scalar Z.graph.arcs C Z.width p
  (rom Z.graph.arcs C Z.width (fixedTable menu))
local notation "laneShapes" => (fun v => ofProgram (fun b => boundaryWidth Z.bank v b / p)
  (Z.laneWidth_eq m p fits v) hp (Z.laneProgram ids m p hp fits v))
local notation "laneLimit" => (fun v u j _ => (Z.lane_stride ids m p hp fits v u j).trans wide)
local notation "laneWidths" => (fun e => Z.lane_dvd m p fits (Z.bank.src e) (.inl ⟨e,Or.inl rfl⟩))

def reentry (t:Z.Fallback) : Donors (((out).sites (siteAt (.inl (false,t)))).recipe hp)
    (fun v:Fibre T.home t=>(src.sites v.val).recipe hp) :=
  installed src hp one T.home Z.placement.input T.hub (funext fun e => (Z.allWidths e).symm)
    Z.bank Z.tables (Z.orderedBank ids) ids laneScalar (Z.laneRecipe ids m p hp fits)
    (Z.lane_valid ids m p hp fits menu) laneShapes laneLimit laneWidths t

end
end Hierarchy.DescentRetainedPrivateSlotBook

namespace Hierarchy.DescentRetainedPrivateSlotBook
open DescentRetainedResetPinPointer
open DescentSixParty DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open ThreeFlat.Routing DescentResetPointerFields
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {B : BitDescription W}

variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (b : ClosedReset cap ctl) (hp : 0<p) (one : 1≤R) (pos : 0<b.reset.unit) (whole : p∣b.reset.unit)
    (wide : max 1 (max b.reset.width (C*b.reset.width))≤R) (a : Archive W) (sh : WorldShape p R a.bit)
local notation "split_" => sh.granular b.count (z*G.b) b.fit hp (b.unit ▸ pos) (b.unit ▸ whole)
local notation "key_" => DescentOrderedReset.grains W b.count b.order
local notation "fit_" => ((Nat.div_mul_cancel whole).symm : b.reset.unit=b.reset.unit/p*p)
local notation "installed" => reentryWorldShape split_ b.reset b.terminals key_ _ hp fit_ (resetMenu b) one wide
local notation "after_" => WorldShape.follow hp pos whole b.reblock b.cuts installed
local notation "next_" => (resetArchive b p hp whole a).bit
local notation "coarse" => b.reset.orderedReentry b.terminals key_
local notation "count_" => fun e=>(coarse).graph.width e/b.reset.unit

local notation "vertices" => b.frame.host.symm.toEmbedding.trans cap.vertex
local notation "hostRank" => (b.reset.rawHostRank b.terminals vertices).trans Fin.valEmbedding
local notation "siteRank" => b.raw.siteFrom
  (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) hostRank) b.valid.coordinates
local notation "oldRank" => (b.reset.nativeResetEdges b.terminals vertices key_).order.trans Fin.valEmbedding
local notation "edgeRank" => DescentResetLocalOrder.allCode b.raw oldRank S b.valid siteRank
local notation "cutFit" => b.reset.counts_fit b.terminals
local notation "books" => closedBooks b hp one pos whole wide a sh
local notation "grains" => grainBooks W b.count (z*G.b) b.fit hp (b.unit ▸ pos) (b.unit ▸ whole) sh
local notation "site" t => (b.reset.resetNames b.terminals).symm (.inl (false,t))

local notation "splitBits" => BitDescription.granular W b.count (z*G.b) b.fit a.bit
local notation "idMap" => NodeOrder.installedNames splitBits b.terminals.home b.reset.placement.input
  b.terminals.hub (funext fun e=>(b.reset.allWidths e).symm) b.reset.bank b.reset.tables
  (b.reset.orderedBank key_) key_ _ (b.reset.laneRecipe key_ _ p hp fit_)
  (b.reset.lane_valid key_ _ p hp fit_ (resetMenu b))

theorem retained_site (x : NodeOrder.All next_) (y : NodeOrder.All a.bit)
    (origin : resetOrigin b hp whole a x=Sum.inl y) :
    (books).home x.1=site (b.terminals.home y.1):=by
  have middle := closedBooks_node b hp one pos whole wide a sh x
  exact (congrArg Sigma.fst middle).trans (installed_owner_site (B:=splitBits) b.terminals.home b.reset.placement.input
    b.terminals.hub (funext fun e => (b.reset.allWidths e).symm) b.reset.bank b.reset.tables
    (b.reset.orderedBank key_) key_ _ (b.reset.laneRecipe key_ _ p hp fit_)
    (b.reset.lane_valid key_ _ p hp fit_ (resetMenu b)) (NodeOrder.followNames b.reblock _ x) y origin)

local notation "preBits" => (splitBits).batchedReset b.reset b.terminals key_ (b.reset.unit/p) p hp fit_ (resetMenu b)
local notation "primaryBook" t => reentry b.reset b.terminals split_ key_ (b.reset.unit/p) hp fit_ (resetMenu b) one wide t

private def primary {Tag A : Type} (r : Recipe Tag A) (v : (coarse).graph.Site) (t : b.reset.Fallback)
    (atPrimary : v=site t) (carrier : WordBook r (((installed).sites v).recipe hp)) :
    Donors r (fun i:Fibre b.terminals.home t=>(sh.sites i.val).recipe hp) :=
  ((primaryBook t).rebase (atPrimary ▸ carrier)).previous (fun i=>(grains).atSite i.val)

/-- The exact node-argument and private-word bijections at this reached
primary, including the initial edge splitting and both final naming operations. -/
def reached (x : NodeOrder.All next_) (y : NodeOrder.All a.bit)
    (origin : resetOrigin b hp whole a x=Sum.inl y) :
    Donors (((after_).sites x.1).recipe hp)
      (fun v:Fibre b.terminals.home (b.terminals.home y.1)=>(sh.sites v.val).recipe hp):=by
  exact primary b hp one pos whole wide a sh (((after_).sites x.1).recipe hp) ((books).home x.1)
    (b.terminals.home y.1) (retained_site b hp one pos whole wide a sh x y origin) ((books).atSite x.1)

/-- Moving the carrier to its primary changes only its dependent site index. The
chronological donor node and the finite argument ordinal both survive. -/
private theorem primary_slot {Tag A : Type} (r : Recipe Tag A)
    (v : (coarse).graph.Site) (t : b.reset.Fallback) (atPrimary : v=site t)
    (carrier : WordBook r (((installed).sites v).recipe hp)) (s : DescentLocalPrivateNames.Slot r) :
    let donor := primary b hp one pos whole wide a sh r v t atPrimary carrier
    idMap ⟨v,carrier.node s.1⟩=Sum.inl ⟨(donor.slots s).1.val,(donor.slots s).2.1⟩ ∧
      (donor.slots s).2.2.val=s.2.val :=by
  subst v
  exact installed_slot_origin split_ hp one b.terminals.home b.reset.placement.input b.terminals.hub
    (funext fun e=>(b.reset.allWidths e).symm) b.reset.bank b.reset.tables (b.reset.orderedBank key_)
    key_ _ _ _ _ _ _ t (carrier.slotsTo s)

private theorem carry_slot {W' : MarkedWorld F d P bits} {B' : BitDescription W'} {Z : Type}
    {first : WorldShape p R B} {last : WorldShape p R B'} (hp : 0<p) (book : SiteBooks hp first last)
    (v : W.graph.Site) (u : (B.recipe v).Node) (label : NodeOrder.All B' → Z) {expected : Z} {extra : Prop}
    (record : label ⟨book.home v,(book.atSite v).node u⟩ = expected ∧ extra)
    {raw : NodeOrder.All B'} (eqn : book.nodeAt hp ⟨v,u⟩=raw) :
    label raw=expected ∧ extra := by
  subst raw
  exact record

attribute [local irreducible] primary closedBooks NodeOrder.installedNames NodeOrder.followNames
set_option maxHeartbeats 750000 in
/-- Every argument of every node on this reached primary has its actual old
donor node under the same chronological reset equivalence and its old argument number. -/
theorem reached_slot_origin (x : NodeOrder.All next_) (y : NodeOrder.All a.bit)
    (origin : resetOrigin b hp whole a x=Sum.inl y)
    (s : DescentLocalPrivateNames.Slot (((after_).sites x.1).recipe hp)) :
    let d := reached b hp one pos whole wide a sh x y origin
    resetOrigin b hp whole a ⟨x.1,s.1⟩=Sum.inl ⟨(d.slots s).1.val,(d.slots s).2.1⟩ ∧
      (d.slots s).2.2.val=s.2.val :=by
  intro d
  let row : NodeOrder.All next_ := ⟨x.1,s.1⟩
  have index := closedBooks_node b hp one pos whole wide a sh row
  have step := primary_slot b hp one pos whole wide a sh (((after_).sites x.1).recipe hp) ((books).home x.1)
    (b.terminals.home y.1) (retained_site b hp one pos whole wide a sh x y origin) ((books).atSite x.1) s
  have result := carry_slot hp books x.1 s.1 (fun v : NodeOrder.All preBits => idMap v) step index
  exact result

end
end Hierarchy.DescentRetainedPrivateSlotBook

end OAI
