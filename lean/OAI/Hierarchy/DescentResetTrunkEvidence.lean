import OAI.Hierarchy.DescentResetTrunkShapeRead
import OAI.Hierarchy.DescentResetTrunkChip
import OAI.Hierarchy.DescentResetPeerFamilySupport

namespace OAI
/-! # The raw short marker witnesses exactly the real trunk neighbors, even without grains -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "addresses" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))



local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "same" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables


open DescentResetFieldAssembler DescentIssuedFallbackPanel DescentNextSignedWindow
local notation "rows" => blocks B
local notation "End" => (old).graph.Edge
local notation "Home" => (T).home
local notation "full" => totalLocal B
local notation "AC" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "before" => input.order.trans Fin.valEmbedding
local notation "half" => 2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*(AC).cap)



open DescentPackedZip DescentSIMDLookup DescentResetTrunkIssue ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
local notation "Node₀" => Node (Z).V ((Z).V×DescentContacts.Endpoint (2^(Z).n)) (DescentCommonPalette.rotor (Z).graph).Site
local notation "short" t => DescentRelativeContacts.shortName (T).commonDepth ((T).code t)
local notation "high_" u => (addresses).symm ((u).1.1,(u).2)
local notation "hi_" t => DescentChosenRouter.coarseName (T).commonDepth ((T).code t)
local notation "touch" u t => ((rows).src (trunkParent B t)=u ∨ (rows).dst (trunkParent B t)=u)


local notation "rank" => (Z).rawHostRank T vertexCode


local notation "radius" => (Z).k-(T).commonDepth
local notation "depth_" => GroupStage.depthBound D n f g
local notation "shapeRank" => localRank (Z).graph radius depth_
local notation "roster_" => DescentDenseHostOrder.roster (Z).graph radius depth_


open DescentPackedColony DescentSortedRoster
local notation "rawWord" => DescentResetFieldAssembler.raw
local notation "pitch" => Fintype.card input.V*(roster_).card
local notation "description" => DescentResetTrunkPalette.description (Z).graph radius depth_


local notation "order_" => DescentResetTrunkPalette.order (Z).graph radius depth_
local notation "other_" => DescentResetTrunkChip.other (Z).graph radius depth_
local notation "shapeIdx" => fun (v : Fin pitch) => ((finProdFinEquiv.symm v : Fin (Fintype.card input.V)×Fin (roster_).card).2)
local notation "oldIdx" => fun (v : Fin pitch) => ((finProdFinEquiv.symm v : Fin (Fintype.card input.V)×Fin (roster_).card).1)

theorem other_read (v : B.next.V) (s : Bool) (key) (kind : v.val=.trunk s key) :
    (DescentResetTrunkPalette.pointer (Z).graph radius depth_ (!s) (rank v)).map
      (fun z=>shapeIdx z)=other_ (shapeIdx (rank v)):=by
  have split : (finProdFinEquiv.symm (rank v) : Fin (Fintype.card input.V)×Fin (roster_).card)=
      (vertexCode (position (Z).graph v.val),order_ ((Z).localShape T v)):=Equiv.symm_apply_apply ..
  have shapeAt : ((Z).localShape T v).val=.trunk s ((),key.2):=by
    change shape (Z).graph v.val=_;rw [kind];rfl
  have allowed:=DescentResetTrunkPalette.flip_live (Z).graph radius depth_ ((Z).localShape T v) s (!s) _ shapeAt
  simp [DescentResetTrunkPalette.pointer,DescentResetTrunkPalette.flip,DescentResetTrunkChip.other,split,
    shapeAt,allowed]
  exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply _)

theorem trunk_peer_words (t : (Z).Fallback) (x y : ℕ) :
    let e:=trunkParent B t
    rawPeer B e x y ↔
      (((rank ((rows).src e).1.2).val=x ∧ (rank ((rows).dst e).1.2).val=y) ∨
       ((rank ((rows).dst e).1.2).val=x ∧ (rank ((rows).src e).1.2).val=y)) := by
  intro e
  unfold rawPeer incidentWords
  change 1=1 ∧ _ ↔ _
  rw [and_iff_right rfl]
  rw [show (rows).src e=Stage.home B.next.placement (hop ((coarse).graph.src e)) by rfl,
    show (rows).dst e=Stage.home B.next.placement (hop ((coarse).graph.dst e)) by rfl,named_home,named_home]
  rfl

private theorem same_parent (t : (Z).Fallback) :
    let e:=trunkParent B t
    oldIdx (rank ((rows).src e).1.2)=oldIdx (rank ((rows).dst e).1.2) := by
  intro e
  have eqn (u : Host): oldIdx (rank u.1.2)=vertexCode (position (Z).graph u.1.2.val):=
    congrArg Prod.fst (Equiv.symm_apply_apply finProdFinEquiv _)
  have l:=(trunk_side B t false).1
  have r:=(trunk_side B t true).1
  change ((rows).src e).1.2.val=_ at l
  change ((rows).dst e).1.2.val=_ at r
  let project := fun node : Node₀ => vertexCode (position (Z).graph node)
  exact (eqn ((rows).src e)).trans ((congrArg project l).trans
    ((congrArg project r).symm.trans (eqn ((rows).dst e)).symm))

private theorem trunk_link (t : (Z).Fallback) (s : Bool) (u : Host)
    (x : Host) (src : u=(if s then (rows).dst (trunkParent B t) else (rows).src (trunkParent B t)))
    (dst : x=(if s then (rows).src (trunkParent B t) else (rows).dst (trunkParent B t))) :
    (oldIdx (rank u.1.2)=oldIdx (rank x.1.2)) ∧
      other_ (shapeIdx (rank u.1.2))=some (shapeIdx (rank x.1.2)):=by
  subst u;subst x
  cases s
  · have loc:=trunk_side B t false
    obtain ⟨p,slot,left,right,_⟩:=trunk_labels_at B ((rows).src (trunkParent B t)) t false loc.1 loc.2
    have ol:=other_read B ((rows).src (trunkParent B t)).1.2 false (short t) loc.1
    rw [trunk_pointer B ((rows).src (trunkParent B t)).1.2 (!false),slot] at ol
    change some (shapeIdx (rank p.right))=other_ (shapeIdx (rank ((rows).src (trunkParent B t)).1.2)) at ol
    have opposite : p.right=((rows).dst (trunkParent B t)).1.2:=congrArg (fun q : Host=>q.1.2) right
    exact ⟨same_parent B t,ol.symm.trans (congrArg (fun v : B.next.V=>some (shapeIdx (rank v))) opposite)⟩
  · have loc:=trunk_side B t true
    obtain ⟨p,slot,left,right,_⟩:=trunk_labels_at B ((rows).dst (trunkParent B t)) t true loc.1 loc.2
    have ol:=other_read B ((rows).dst (trunkParent B t)).1.2 true (short t) loc.1
    rw [trunk_pointer B ((rows).dst (trunkParent B t)).1.2 (!true),slot] at ol
    change some (shapeIdx (rank p.left))=other_ (shapeIdx (rank ((rows).dst (trunkParent B t)).1.2)) at ol
    have opposite : p.left=((rows).src (trunkParent B t)).1.2:=congrArg (fun q : Host=>q.1.2) left
    exact ⟨(same_parent B t).symm,ol.symm.trans (congrArg (fun v : B.next.V=>some (shapeIdx (rank v))) opposite)⟩

/-- Width and mark never enter this equivalence. The original actor scan's
one bit at the given coarse coordinate and the shared shape pointer suffice. -/
theorem trunk_evidence (v : B.next.V) (y : Fin pitch) :
    (∃t : (Z).Fallback,rawPeer B (trunkParent B t) (rank v).val y.val) ↔
      oldIdx (rank v)=oldIdx y ∧ other_ (shapeIdx (rank v))=some (shapeIdx y) ∧
        ∃(g : Fin groups) (lo : Block k),trunkTest B ((g,v),lo) := by
  constructor
  · rintro ⟨t,row⟩
    let e:=trunkParent B t
    rcases (trunk_peer_words B t _ _).1 row with left|right
    · have eqv:=(rank).injective (Fin.ext left.1)
      have eqy := Fin.ext left.2
      subst v;subst y
      exact ⟨(trunk_link B t false _ _ rfl rfl).1,(trunk_link B t false _ _ rfl rfl).2,
        ((rows).src e).1.1,((rows).src e).2,(trunk_test B _).2 ⟨t,Or.inl rfl⟩⟩
    · have eqv:=(rank).injective (Fin.ext right.1)
      have eqy := Fin.ext right.2
      subst v;subst y
      exact ⟨(trunk_link B t true _ _ rfl rfl).1,(trunk_link B t true _ _ rfl rfl).2,
        ((rows).dst e).1.1,((rows).dst e).2,(trunk_test B _).2 ⟨t,Or.inr rfl⟩⟩
  · rintro ⟨hParent,hShape,g,lo,bit⟩
    obtain ⟨t,atEnd⟩:=(trunk_test B _).1 bit
    let e:=trunkParent B t
    refine ⟨t,(trunk_peer_words B t _ _).2 ?_⟩
    have opposite (u x : Host) (s : Bool) (host : u.1.2=v)
        (org : u=(if s then (rows).dst e else (rows).src e))
        (oth : x=(if s then (rows).src e else (rows).dst e)) :
        rank x.1.2=y:=by
      have lk:=trunk_link B t s u x org oth
      rw [←host] at hParent hShape
      apply finProdFinEquiv.symm.injective
      exact Prod.ext (lk.1.symm.trans hParent) (Option.some.inj (lk.2.symm.trans hShape))
    rcases atEnd with l|r
    · have eqn:=congrArg (fun x : Host=>x.1.2) l
      exact Or.inl ⟨congrArg (fun x=>(rank x).val) eqn,
        congrArg Fin.val (opposite _ _ false eqn rfl rfl)⟩
    · have eqn:=congrArg (fun x : Host=>x.1.2) r
      exact Or.inr ⟨congrArg (fun x=>(rank x).val) eqn,
        congrArg Fin.val (opposite _ _ true eqn rfl rfl)⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
