import OAI.Hierarchy.DescentPrimaryTokenCoordinates
import OAI.Hierarchy.DescentRetainedPhysicalTarget
import OAI.Hierarchy.DescentPhysicalBankPrimitive

namespace OAI
/-! # Predecessor coordinates on every primary row of the actual reset -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentLocalArchiveOrder DescentCompiler DescentRotor
open DescentResetLocalNodes DescentNamedContact
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (hp : 0<p) (whole : p∣b.reset.unit) (a : Archive W) (earlier : Local a.bit)
set_option quotPrecheck false
local notation "split" => BitDescription.granular W b.count (z*G.b) b.fit a.bit
local notation "key" => DescentOrderedReset.grains W b.count b.order
local notation "fit" => (Nat.div_mul_cancel whole).symm
local notation "m" => b.reset.unit/p
local notation "pre" => (split).batchedReset b.reset b.terminals key m p hp fit (resetMenu b)
local notation "prog" => b.reset.laneRecipe key m p hp fit
local notation "next" => (resetArchive b p hp whole a).bit
local notation "names" => resetOrigin b hp whole a
local notation "oldId" => cap.placement.site cap.vertex cap.valid.coordinates
local notation "prior" => (fun v=>(earlier v).toEmbedding.trans Fin.valEmbedding)
local notation "fresh" => b.reset.laneNodeOrder key m p hp fit
local notation "order" => DescentLocalArchiveOrder.reset b p hp whole a earlier


open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentResetActorClass DescentCommonHost
open Reached.NodeCells DescentColonies
open scoped Classical Fin.CommRing
local notation "Y" => b.next
local notation "H" => S.hostSize (i+1)
local notation "Groups" => S.groupCount (i+1)
local notation "prevRank" => (Y).vertex.trans (Fin.castLEEmb (Y).valid.host)
local notation "census" precision => Census.count (Y).placement (Equiv.refl _) prevRank precision
local notation "cell" => whereAt Y next order
local notation "res" => b.reset.k-b.terminals.commonDepth
local notation "cls" rack => (ClosedReset.Window.paidActorAt b rack).elim 0 (fun u=>indexed b.reset.graph res u.val)
local notation "leftSite" u => b.reblock.destination ((b.reset.resetNames b.terminals).symm u)
local notation "original" => W.granular b.count (z*G.b) b.fit

open DescentPackedResetRotorRoles DescentResetMetadataInputs DescentBundleHistory
variable (layout : DescentPrimitiveBirth.Layout)
local notation "rootSite" wing g v => (⟨(wing,.inl g),⟨v,.inl false⟩⟩:b.reset.bank.Site)

open DescentPrimitiveBirth DescentCommonHost DescentRotorRootPresence DescentSIMDLookup
open DescentPacking.PackedMatch.Local
local notation "Z" => b.reset
local notation "T" => b.terminals
local notation "rr" => (Z).placement
local notation "dim" => (T).commonDepth
local notation "oldDigits" => S.resetOutputDigits ctl.base ctl.radix b.age b.commonDepth
local notation "rootLow" g => ((Z).goodLabel T g).val.2

local notation "home" v:arg => (T).home v
local notation "rawHome" side:arg t:arg => ((Z).resetNames T).symm (.inl (side,t))
local notation "actor" t:arg => (Z).placed T (rawHome false t)
local notation "hostName" prev:arg => ((b.frame.host.symm.toEmbedding.trans cap.vertex).trans (Fin.castLEEmb prev))
local notation "ht" => GroupStage.depthBound D n f g

open DescentFallbackShapeTable DescentRelativeContacts
local notation "label" t:arg => (shortName dim ((T).code t))
local notation "code" t:arg => DescentFallbackShapeTable.cell res (label t).2
local notation "fid" t:arg => (((Z).homeTicket T oldId t).trans Fin.valEmbedding)
local notation "nodesAt" t:arg => (fun u:DescentNamedContact.Fibre (T).home t=>(a.bit.recipe u.val).Node)
local notation "fprior" t:arg => (fun u:DescentNamedContact.Fibre (T).home t=>(earlier u.val).toEmbedding.trans Fin.valEmbedding)

/-- Every common position recognized as a primary by the actual finite table
has a physical old terminal. The terminal may belong to another group. -/
theorem primary_claim (act:(Y).V) {code₀:ℕ} (seen:primaryTarget (Z).graph res act.val=some code₀) :
    ∃t:(Z).Fallback,act=actor t ∧ code t=code₀:=by
  obtain ⟨s,_,at_⟩:=Finset.mem_image.mp act.property
  have where_ : (Z).placed T s=act:=Subtype.ext at_
  rw [←where_] at seen ⊢
  obtain ⟨st,rfl⟩:=((Z).resetNames T).symm.surjective s
  rw [placed_reset_actor_value] at seen
  rcases st with ⟨side,t⟩|⟨⟨side,g|t⟩,site⟩
  · cases side
    · exact ⟨t,rfl,Option.some.inj seen⟩
    · contradiction
  · contradiction
  · contradiction

/-- Combining the old host word and the short shape code distinguishes every
physical primary in the common palette; their high blocks are allowed to differ. -/
theorem same_primary (t u : (Z).Fallback) (host:((T).code t).1=((T).code u).1) (same:code t=code u) :
    actor t=actor u:=by
  have depth (s : (Z).Fallback): (label s).2.1.1≤res:=Nat.sub_le_sub_right ((T).codeLegal s).2.1 dim
  have bound (s : (Z).Fallback): (label s).2.1.2<2^(label s).2.1.1:=Nat.mod_lt _ (Nat.two_pow_pos _)
  have digits:=congrArg (decode res (2^(Z).n)) same
  rw [decode_cell res _ (depth t) (bound t),decode_cell res _ (depth u) (bound u)] at digits
  have labels : label t = label u := Prod.ext host digits
  apply Subtype.ext
  rw [placed_reset_actor_value, placed_reset_actor_value]
  exact congrArg (DescentCommonHost.Node.trunk false) labels

set_option maxHeartbeats 600000 in
/-- A primary with more previous primitive nodes than the queried local index
necessarily has a real reached atom at that index, even at an unfunded hub. -/
theorem primary_at_slot {N : ℕ} (slot:Fin N) (x:Block k) (hi:Fin H) (grp:Fin Groups)
    (t:(Z).Fallback) (host:((Y).vertex (actor t)).val=hi.val)
    (coarse:oldDigits ((Z).rootBlock T (.inr t))=(grp,x))
    (live:slot.val<∑u:DescentNamedContact.Fibre (T).home t,Fintype.card ((nodesAt t) u)) :
    ∃atom,cell x slot hi grp=some atom ∧ ∃former,names atom=.inl former:=by
  let rank:=oldOrder (nodesAt t) (fid t) (fprior t)
  let id:Fin (Fintype.card (Σu,(nodesAt t) u)):=⟨slot.val,by simpa only [Fintype.card_sigma] using live⟩
  obtain ⟨⟨⟨v,hv⟩,node⟩,eqn⟩:=rank.surjective id
  subst t
  let former : NodeOrder.All a.bit:=⟨v,node⟩
  let atom:NodeOrder.All next:=(names).symm (.inl former)
  have who:names atom=.inl former:=(names).apply_symm_apply _
  have address:=physical_primary_home b hp whole a former atom who
  rw [coarse] at address
  have hostEq : ((Y).placement.pos atom.1).2 = actor ((T).home v) :=
    congrArg (fun z : (Fin Groups × (Y).V) × Block k => z.1.2) address
  have groupEq : ((Y).placement.pos atom.1).1 = grp :=
    congrArg (fun z : (Fin Groups × (Y).V) × Block k => z.1.1) address
  have blockEq : (Y).placement.block atom.1 = x :=
    congrArg (fun z : (Fin Groups × (Y).V) × Block k => z.2) address
  have hostIndex : (((Y).vertex ((Y).placement.pos atom.1).2).castLE (Y).valid.host) = hi :=
    Fin.ext ((congrArg (fun j : (Y).V => ((Y).vertex j).val) hostEq).trans host)
  have place : coordinate (Y) atom.1=(hi,grp,x) := Prod.ext hostIndex (Prod.ext groupEq blockEq)
  have num:=reached_node_rank b hp whole a earlier atom
  rw [who] at num
  have same : (order atom.1 atom.2).val=id.val:=num.trans (congrArg Fin.val eqn)
  exact ⟨atom,whereAt_at (Y) next order x slot hi grp _ _ place same.symm,former,who⟩

end
end Hierarchy.DescentPrimitivePalette

end OAI
