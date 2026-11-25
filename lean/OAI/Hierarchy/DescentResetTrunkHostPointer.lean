import OAI.Hierarchy.DescentResetTrunkPalette
import OAI.Hierarchy.DescentResetTrunkRaster

namespace OAI
/-! # The physically mounted pointer is the genuine opposite terminal at every old host -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
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
local notation "short" t:arg => DescentRelativeContacts.shortName (T).commonDepth ((T).code t)
local notation "high_" u:arg => (addresses).symm ((u).1.1,(u).2)
local notation "hi_" t:arg => DescentChosenRouter.coarseName (T).commonDepth ((T).code t)
local notation "touch" u:arg t:arg => ((rows).src (trunkParent B t)=u ∨ (rows).dst (trunkParent B t)=u)


local notation "rank" => (Z).rawHostRank T vertexCode


local notation "radius" => (Z).k-(T).commonDepth
local notation "depth_" => GroupStage.depthBound D n f g
local notation "shapeRank" => localRank (Z).graph radius depth_
local notation "roster_" => DescentDenseHostOrder.roster (Z).graph radius depth_

private theorem realized_terminal (v : B.next.V) (side : Bool) (z) (kind : v.val=.trunk side z) :
    ∃t : (Z).Fallback,short t=z:=by
  obtain ⟨a,_,eqn⟩:=Finset.mem_image.mp v.property
  have yes:=(Z).reset_occupied T (.trunk side z) ((Z).blockId T a)
  obtain ⟨t,key,_⟩:=yes.1 ⟨a,eqn.trans kind,rfl⟩
  exact ⟨t,key⟩

theorem trunk_pointer (v : B.next.V) (side : Bool) :
    DescentResetTrunkPalette.pointer (Z).graph radius depth_ side (rank v)=
      (trunkLabels B v).map (fun p=>rank (if side then p.right else p.left)):=by
  let sh:=(Z).localShape T v
  let hostRank:=vertexCode (position (Z).graph v.val)
  change DescentResetTrunkPalette.pointer (Z).graph radius depth_ side (finProdFinEquiv (hostRank,shapeRank sh))=_
  cases kind : v.val with
  | trunk s key=>
    obtain ⟨t,name⟩:=realized_terminal B v s key kind
    let e:=trunkParent B t
    let u:=(rows).src e
    let key':=short t
    have a:=trunk_side B t false
    have b:=trunk_side B t true
    have a₀ : .trunk false key∈(Z).commonNames T:=by
      rw [←name,←a.1];exact u.1.2.property
    have b₀ : .trunk true key∈(Z).commonNames T:=by
      rw [←name,←b.1];exact ((rows).dst e).1.2.property
    let left : B.next.V:=⟨.trunk false key,a₀⟩
    let right : B.next.V:=⟨.trunk true key,b₀⟩
    have seen : trunkLabels B v=some ⟨left,right,key.2.2.isSome⟩:=by simp [trunkLabels,kind,a₀,b₀,left,right]
    rw [seen]
    cases side
    · have fh : DescentResetTrunkPalette.flip (Z).graph false sh.val=some ((Z).localShape T left).val:=by
        change DescentResetTrunkPalette.flip _ _ (shape _ v.val)=_
        rw [kind];rfl
      rw [DescentResetTrunkPalette.at_label _ _ _ _ _ _ _ fh]
      simp only [Option.map_some,Bool.false_eq_true]
      apply congrArg some
      change finProdFinEquiv (hostRank,_) = finProdFinEquiv (vertexCode (position _ left.val),_)
      rw [show hostRank=vertexCode (position _ left.val) by simp [hostRank,kind,left,DescentDenseHostOrder.position]]
      rfl
    · have fh : DescentResetTrunkPalette.flip (Z).graph true sh.val=some ((Z).localShape T right).val:=by
        change DescentResetTrunkPalette.flip _ _ (shape _ v.val)=_
        rw [kind];rfl
      rw [DescentResetTrunkPalette.at_label _ _ _ _ _ _ _ fh]
      simp only [Option.map_some]
      apply congrArg some
      change finProdFinEquiv (hostRank,_) = finProdFinEquiv (vertexCode (position _ right.val),_)
      rw [show hostRank=vertexCode (position _ right.val) by simp [hostRank,kind,right,DescentDenseHostOrder.position]]
      rfl
  | good=>
    have off : DescentResetTrunkPalette.flip (Z).graph side sh.val=none:=by change DescentResetTrunkPalette.flip _ _ (shape _ v.val)=_;rw [kind];rfl
    simp [DescentResetTrunkPalette.off_label _ _ _ _ _ _ off,trunkLabels,kind]
  | fall=>
    have off : DescentResetTrunkPalette.flip (Z).graph side sh.val=none:=by change DescentResetTrunkPalette.flip _ _ (shape _ v.val)=_;rw [kind];rfl
    simp [DescentResetTrunkPalette.off_label _ _ _ _ _ _ off,trunkLabels,kind]

theorem trunk_relay_alias {w₀ : ℕ} (base : ℕ) (m : Memory w₀)
    (space : base+3*(Fintype.card input.V*(roster_).card)<2^w₀) (v : B.next.V) :
    let size:=Fintype.card input.V*(roster_).card
    let done:=DescentResetTrunkPalette.memory (Z).graph radius depth_ base (Fintype.card input.V) m
    done (base+size+(rank v).val)=((((trunkLabels B v).map (fun p=>rank p.right)).elim size Fin.val : ℕ) : Word w₀) :=by
  intro size done
  have mounted:=(DescentResetTrunkPalette.run (Z).graph radius depth_ base (Fintype.card input.V) m space).2.1 1 (rank v)
  simpa [DescentResetTrunkPalette.value,trunk_pointer,done,size] using mounted

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
