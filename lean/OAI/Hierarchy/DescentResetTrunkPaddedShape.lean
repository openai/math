import OAI.Hierarchy.DescentResetTrunkShapeRead
import OAI.Hierarchy.DescentResetWindowEmittedSources
import OAI.Hierarchy.DescentResetPeerUnionRAM

namespace OAI
/-! # Raw pointers and signed class ranks under any physical old-host padding -/
namespace Hierarchy.DescentResetTrunkPalette
open DescentDenseHostOrder DescentCommonHost
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {n h H H' : ℕ} (board : NonlinearExpanders.Graph n h) (r depth : ℕ)
local notation "S_" => (roster board r depth).card

def extend (le : H≤H') : Fin (H*S_)↪Fin (H'*S_):=Fin.castLEEmb (Nat.mul_le_mul_right S_ le)

theorem pointer_extend (le : H≤H') (s : Bool) (x : Fin (H*S_)) :
    pointer board r depth s (extend board r depth le x)=(pointer board r depth s x).map (extend board r depth le):=by
  obtain ⟨⟨p,z⟩,rfl⟩:=finProdFinEquiv.surjective x
  have lift (a : Fin H) (f : Fin S_) : extend board r depth le (finProdFinEquiv (a,f))=finProdFinEquiv (a.castLE le,f):=rfl
  rw [lift]
  unfold pointer
  simp only [Equiv.symm_apply_apply]
  cases tag : flip board s (((order board r depth).symm z).val) with
  | none=>simp
  | some v=>
    by_cases named : v∈roster board r depth
    · simp [named,lift]
    · simp [named]

theorem badge_extend (le : H≤H') (x : Fin (H*S_)) : badge board r depth (extend board r depth le x)=badge board r depth x:=rfl

private theorem description_extend (le : H ≤ H') (x : Fin (H*S_)) :
    description board r depth (extend board r depth le x) =
      (description board r depth x).map
        (fun q => (extend board r depth le q.1, extend board r depth le q.2.1, q.2.2)) := by
  unfold description
  rw [pointer_extend, pointer_extend, badge_extend]
  cases pointer board r depth false x <;> cases pointer board r depth true x <;> rfl
end
end Hierarchy.DescentResetTrunkPalette
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetLocalRoster DescentParallelBase DescentResetAttachments
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
local notation "key" => DescentOrderedReset.grains W B.count B.order


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


local notation:max "lift_" le:arg => DescentResetTrunkPalette.extend (Z).graph radius depth_ le
local notation:max "named" le:arg => (Z).rawHostRank T ((vertexCode).trans (Fin.castLEEmb le))

theorem trunk_padded_pointer {H : ℕ} (pad : Fintype.card input.V≤H) (v : B.next.V) (s : Bool) :
    DescentResetTrunkPalette.pointer (Z).graph radius depth_ s (named pad v)=
      (trunkLabels B v).map (fun p=>named pad (if s then p.right else p.left)):=by
  change DescentResetTrunkPalette.pointer _ _ _ s (lift_ pad (rank v))=_
  rw [DescentResetTrunkPalette.pointer_extend,trunk_pointer,Option.map_map]
  rfl

theorem trunk_padded_desc {H : ℕ} (pad : Fintype.card input.V≤H) (v : B.next.V) :
    DescentResetTrunkPalette.description (Z).graph radius depth_ (named pad v)=
      (trunkLabels B v).map (fun p=>(named pad p.left,named pad p.right,p.core)):=by
  change DescentResetTrunkPalette.description _ _ _ (lift_ pad (rank v)) = _
  rw [DescentResetTrunkPalette.description_extend, trunk_description B v, Option.map_map]
  rfl

/-- Three genuine raw-neighbor columns suffice despite inserted self and the
separate original loop flag. Neither the local class nor the core code changes
when all external old actor names are cast into a wider physical rectangle. -/
theorem trunk_original_scalar {H p : ℕ} (pad : Fintype.card input.V≤H) (record : B.Recorded p)
    (ns : Fin (H*(roster_).card)→Fin 3→Option (Fin (H*(roster_).card))) (v : B.next.V)
    (tape : present (DescentResetPeerUnionRAM.selfPeers ns) (named pad v)=(insert v ((Z).emittedNear T v)).map (named pad))
    (loops : (∀j,ns (named pad v) j≠some (named pad v)) ↔ v∉(Z).emittedNear T v) :
    DescentResetTrunkScalar.integer ns (named pad v)
      (DescentResetTrunkPalette.description (Z).graph radius depth_ (named pad v))=hostShape B v:=by
  rw [trunk_padded_desc]
  cases tag : trunkLabels B v with
  | none=>simp [tag,DescentResetTrunkScalar.integer,hostShape]
  | some obj=>
    let near:=B.next.placement.near v
    have issued : present (DescentResetTrunkScalar.peers ns) (named pad v)=(insert v near).map (named pad):=by
      have rowsEq : DescentResetTrunkScalar.peers ns = DescentResetPeerUnionRAM.selfPeers ns := by
        funext h₀ j
        cases j using Fin.cases <;> rfl
      have exactNear : near = (Z).emittedNear T v := congrFun (rendered_near B record) v
      calc
        _ = present (DescentResetPeerUnionRAM.selfPeers ns) (named pad v) :=
          congrArg (fun peerRows => present peerRows (named pad v)) rowsEq
        _ = _ := tape
        _ = _ := by
          apply congrArg (Finset.map (named pad))
          ext a
          rw [exactNear]
          constructor <;> intro mem <;> exact Finset.mem_insert.mpr (Finset.mem_insert.mp mem)
    have extract (t : B.next.V) :
        DescentSortedRoster.before (DescentResetTrunkScalar.peers ns) (named pad v) (named pad t)=
          stemOrdinal (rank v).val (near.map ((rank).trans Fin.valEmbedding)) (rank t).val:=by
      have mapped {V : Type} [DecidableEq V] (name : V ↪ ℕ) (N : Finset V) (a b : V) :
          stemOrdinal (name a) (N.map name) (name b) =
            ((insert a N).filter (fun x => name x < name b)).card := by
        unfold stemOrdinal
        rw [←Finset.map_insert,Finset.filter_map,Finset.card_map]
        rfl
      exact (DescentResetSourceClassRAM.local_class (named pad) (insert v near) t
        (DescentResetTrunkScalar.peers ns) (named pad v) issued).trans
        (mapped ((rank).trans Fin.valEmbedding) near v t).symm
    have hnear : (named pad v)∉present ns (named pad v) ↔ (rank v).val∉near.map ((rank).trans Fin.valEmbedding):=by
      have absent : (named pad v)∉present ns (named pad v) ↔ ∀j,ns (named pad v) j≠some (named pad v):=by
        simp [present]
      rw [absent,loops]
      have pe := congrFun (rendered_near B record) v
      change near=_ at pe
      rw [←pe]
      exact not_congr (Finset.mem_map' ((rank).trans Fin.valEmbedding)).symm
    simp [hostShape,tag,DescentResetTrunkScalar.integer,extract,hnear,near]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
