import OAI.Hierarchy.DescentResetSourceClassRAM
import OAI.Hierarchy.DescentResetTrunkHostPointer
import OAI.Hierarchy.DescentResetTrunkScalar
import OAI.Hierarchy.DescentResetStemHeaderAlias

namespace OAI
/-! # The issued scalar class descriptor on the original geometric host family -/
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

theorem trunk_description (v : B.next.V) :
    description (rank v)=(trunkLabels B v).map (fun p=>(rank p.left,rank p.right,p.core)):=by
  have left:=trunk_pointer B v false
  have right:=trunk_pointer B v true
  cases live : trunkLabels B v with
  | none=>simp [DescentResetTrunkPalette.description,left,right,live]
  | some p=>
    obtain ⟨key,kind,l,r,core⟩:=trunk_labels_here B ((((addresses) (0:Block (T).commonDepth)).1,v),0) p live
    have badge : DescentResetTrunkPalette.badge (Z).graph radius depth_ (rank v)=p.core:=by
      rcases kind with kind|kind
      all_goals
        rw [core]
        exact DescentResetTrunkPalette.at_badge _ _ _ _ ((Z).localShape T v) _ _
          (by change shape _ v.val=_;rw [kind];rfl)
    simp [DescentResetTrunkPalette.description,left,right,badge,live]

private theorem peer_ordinal {V : Type} [Fintype V] [DecidableEq V] {H : ℕ}
    (name : V ↪ Fin H) (near : Finset V) (peer : Fin H → Fin 3 → Option (Fin H)) (v z : V)
    (actual : present peer (name v) = near.map name) :
    DescentSortedRoster.before (DescentResetTrunkScalar.peers peer) (name v) (name z) =
      stemOrdinal (name v).val (near.map (name.trans Fin.valEmbedding)) (name z).val := by
  have booked : present (DescentResetTrunkScalar.peers peer) (name v) = (insert v near).map name := by
    rw [DescentResetTrunkScalar.present_peers,actual,Finset.map_insert]
  rw [DescentResetSourceClassRAM.local_class name (insert v near) z _ _ booked]
  unfold stemOrdinal
  let natName := name.trans Fin.valEmbedding
  change _ = ((insert (natName v) (near.map natName)).filter _).card
  rw [←Finset.map_insert,Finset.filter_map,Finset.card_map]
  rfl

/-- Only the three genuine primitive neighbor words enter this comparison.
Duplicate edges and self-loops are included by the original emitted geometry. -/
theorem trunk_scalar (v : B.next.V) (neighbors : Fin pitch→Fin 3→Option (Fin pitch))
    (actual : present neighbors (rank v)=(B.next.placement.near v).map (rank)) :
    DescentResetTrunkScalar.integer neighbors (rank v) (description (rank v))=hostShape B v :=by
  rw [trunk_description]
  cases label : trunkLabels B v with
  | none=>simp [hostShape,label,DescentResetTrunkScalar.integer]
  | some p=>
    let near:=B.next.placement.near v
    have yes (z : B.next.V) :
        DescentSortedRoster.before (DescentResetTrunkScalar.peers neighbors) (rank v) (rank z)=
          stemOrdinal (rank v).val (near.map ((rank).trans Fin.valEmbedding)) (rank z).val:=by
      exact peer_ordinal (rank) near neighbors v z actual
    have miss : rank v∉present neighbors (rank v) ↔ (rank v).val∉near.map ((rank).trans Fin.valEmbedding):=by
      rw [actual]
      exact not_congr ((Finset.mem_map' (rank)).trans (Finset.mem_map' ((rank).trans Fin.valEmbedding)).symm)
    simp [hostShape,label,DescentResetTrunkScalar.integer,yes,miss,near]

/-- Broadcast the measured small word through the very same shape-only pages
already installed by the original stem procedure. No extra SIMD header page. -/
theorem trunk_shape_source {G₀ M b w₀ raw head : ℕ} (neighbors : Fin pitch→Fin 3→Option (Fin pitch)) (m : Memory w₀)
    (actual : ∀v,present neighbors (rank v)=(B.next.placement.near v).map (rank))
    (stored : ∀i : Fin pitch,m (raw+i.val)=((rawWord b (DescentResetTrunkScalar.integer neighbors i (description i))).val:Word w₀))
    (mount : DescentResetStemHeaders.TablesOK pitch G₀ M (b*7) head m)
    (prior : raw+pitch+DescentDyadicSpan.span pitch≤head)
    (room : DescentResetStemHeaders.outputBase pitch G₀ M (b*7) head+(pitch*chunks G₀ M)<2^w₀)
    (wide : b*7*M≤w₀) :
    let e:=DescentResetStemHeaders.body pitch G₀ M (b*7) raw head 0
    e.Fits w₀ (DescentResetStemHeaders.outputBase pitch G₀ M (b*7) head) ∧
      Source e (fun i (_ : Fin G₀)=>rawWord b (DescentResetTrunkScalar.integer neighbors i (description i))) M m ∧
      (∀v,rawWord b (DescentResetTrunkScalar.integer neighbors (rank v) (description (rank v)))=rawWord b (hostShape B v)) :=by
  let β : Fin 1→Fin pitch→Cell (b*7):=fun _ i=>rawWord b (DescentResetTrunkScalar.integer neighbors i (description i))
  have real : DescentResetStemHeaders.Raw raw β m:=by
    intro j i;fin_cases j;simpa [β] using stored i
  have got:=DescentResetStemHeaders.runtime_word (G:=G₀) (M:=M) β m real mount (by simpa using prior) (by simpa using room) wide 0
  exact ⟨got.1,got.2,fun v=>congrArg (rawWord b) (trunk_scalar B v neighbors (actual v))⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
