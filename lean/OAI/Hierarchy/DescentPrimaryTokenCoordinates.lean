import OAI.Hierarchy.DescentResetOriginRank
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

theorem placed_reset_actor_value (st : (Bool × (Z).Fallback) ⊕ (Z).bank.Site) :
    ((Z).placed T (((Z).resetNames T).symm st)).val =
      DescentCommonHost.rawName (Z).placement (Z).graph dim (T).code (Z).positive (Z).pay (Z).circuit d st :=
  congrArg (DescentCommonHost.rawName (Z).placement (Z).graph dim (T).code (Z).positive (Z).pay (Z).circuit d)
    (((Z).resetNames T).apply_symm_apply st)

theorem physical_primary_home (former : NodeOrder.All a.bit) (atom : NodeOrder.All next)
    (earlierAt : names atom=.inl former) :
    DescentSharedCableNames.Stage.home (Y).placement atom.1=
      (((oldDigits ((Z).rootBlock T (.inr (home former.1)))).1,actor (home former.1)),
       (oldDigits ((Z).rootBlock T (.inr (home former.1)))).2):=by
  have homeSite:=reached_node_site b hp whole a atom
  rw [earlierAt] at homeSite
  rw [←homeSite]
  let t := (T).home former.1
  have coarse : (Z).blockId T (rawHome false t) = (Z).rootBlock T (.inr t) := by
    apply Fin.ext
    change DescentCommonHost.rawCoordinate (Z).placement (Z).graph dim (T).code (Z).positive (Z).pay (Z).circuit d
      (((Z).resetNames T) (((Z).resetNames T).symm (.inl (false,t)))) = _
    rw [Equiv.apply_symm_apply]
    rfl
  have placed := ClosedReset.Window.named_home b (rawHome false t)
  rw [coarse] at placed
  exact placed

theorem physical_primary_fields {oldHosts : ℕ} (enough : Fintype.card cap.V≤oldHosts)
    (former : NodeOrder.All a.bit) (atom : NodeOrder.All next) (earlierAt:names atom=.inl former) :
    let h:=((Y).placement.pos atom.1).2
    let f:=(Z).hostFields T (hostName enough) h
    f.1=(cap.vertex (cap.placement.pos former.1).2).castLE enough ∧
      DescentResetActorClass.targetBook ctl.board k ht (f.2.cast b.public_hub_slots)=
        some (DescentFallbackShapeTable.cell res (DescentRelativeContacts.shortName (T).commonDepth ((T).code (home former.1))).2):=by
  intro h hostFields
  have home_:=physical_primary_home b hp whole a former atom earlierAt
  have same:h=actor (home former.1):=congrArg (fun v=>v.1.2) home_
  constructor
  · change (((hostName enough) (DescentDenseHostOrder.position (Z).graph h.val)))=_
    rw [same,placed_reset_actor_value]
    change ((cap.vertex (b.frame.host.symm ((T).code (home former.1)).1)).castLE enough)=_
    have host:=b.frame.homeHost former.1
    rw [host,Equiv.symm_apply_apply]
  · rw [ClosedReset.Window.calendar_primary_target b enough h,same,placed_reset_actor_value]
    change DescentResetActorClass.primaryTarget (Z).graph res
      (.trunk false (DescentRelativeContacts.shortName (T).commonDepth ((T).code (home former.1))))=_
    rfl

/-- The installed group and block are exactly the two public digits of the old
terminal's measured high block, even when several physical sites share a primary. -/
theorem primary_raw_digits (former : NodeOrder.All a.bit) (atom : NodeOrder.All next)
    (earlierAt:names atom=.inl former) :
    oldDigits ((Z).rootBlock T (.inr (home former.1)))=
      (((Y).placement.pos atom.1).1,(Y).placement.block atom.1):=by
  have here:=physical_primary_home b hp whole a former atom earlierAt
  exact (congrArg (fun v=>(v.1.1,v.2)) here).symm

/-- The same public numerical target table rejects relay, rotor and fallback
actors. This concerns every scalar on the actual common host, independent of
the amount of its selected data. -/
theorem physical_target_origin {oldHosts : ℕ} (enough : Fintype.card cap.V≤oldHosts) (atom : NodeOrder.All next) :
    let h:=((Y).placement.pos atom.1).2
    DescentResetActorClass.targetBook ctl.board k ht (((Z).hostFields T (hostName enough) h).2.cast b.public_hub_slots)=
      Sum.elim (fun former : NodeOrder.All a.bit=>some (DescentFallbackShapeTable.cell res
        (DescentRelativeContacts.shortName (T).commonDepth ((T).code (home former.1))).2))
        (fun _=>none) (names atom):=by
  intro h
  rcases origin:names atom with former|rest
  · exact (physical_primary_fields b hp whole a enough former atom origin).2
  · rw [ClosedReset.Window.calendar_primary_target b enough h]
    have site:=reached_node_site b hp whole a atom
    rw [origin] at site
    have raw:=congrArg (fun v=>((Y).placement.pos v).2)
      site
    have located:=congrArg (fun v=>v.1.2) (ClosedReset.Window.named_home b (chosenOwner b hp whole a (.inr rest)))
    have atSite : h=(Z).placed T (chosenOwner b hp whole a (.inr rest)):=raw.symm.trans located
    rw [atSite]
    rcases rest with edge | bank
    · exact congrArg (DescentResetActorClass.primaryTarget (Z).graph res)
        (placed_reset_actor_value b (.inl (true,DescentResetTrunks.moved (original).graph (T).home edge)))
    · rcases bank with ⟨⟨⟨side,g|t⟩,v⟩,o⟩
      · exact congrArg (DescentResetActorClass.primaryTarget (Z).graph res)
          (placed_reset_actor_value b (.inr ⟨(side,.inl g),v⟩))
      · exact congrArg (DescentResetActorClass.primaryTarget (Z).graph res)
          (placed_reset_actor_value b (.inr ⟨(side,.inr t),v⟩))

end
end Hierarchy.DescentPrimitivePalette

end OAI
