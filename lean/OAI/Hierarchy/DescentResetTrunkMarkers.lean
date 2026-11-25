import OAI.Hierarchy.DescentResetTrunkShapeRead
import OAI.Hierarchy.DescentResetTrunkChip
import OAI.Hierarchy.DescentResetPeerCodes
import OAI.Hierarchy.DescentResetTrunkEvidence

namespace OAI
/-! # The raw short marker witnesses exactly the real trunk neighbors, even without grains -/
namespace Hierarchy.DescentResetTrunkChip
open DescentDenseHostOrder DescentSIMDLookup DescentResetPeerUnionRAM.Candidates
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {n h H D b : ℕ} (board : NonlinearExpanders.Graph n h) (r depth : ℕ)
local notation "S_" => (roster board r depth).card

theorem marker_socket (old : Fin H→Fin D→Option (Fin H)) (v x : Fin (H*S_)) (chip : Cell 1)
    (word : (D+1)*S_ < 2^b) :
    (∃j : Fin (count S_ D),candidate old v j=some x ∧
      (bits board r depth D ((finProdFinEquiv.symm v).2) chip : Cell b).val=j.val+1) ↔
      chip.val=1 ∧ (finProdFinEquiv.symm v).1=(finProdFinEquiv.symm x).1 ∧
        other board r depth (finProdFinEquiv.symm v).2=some (finProdFinEquiv.symm x).2:=by
  obtain ⟨⟨p,a⟩,rfl⟩:=finProdFinEquiv.surjective v
  obtain ⟨⟨t,c⟩,rfl⟩:=finProdFinEquiv.surjective x
  simp only [Equiv.symm_apply_apply]
  by_cases live : chip.val=1
  · cases key : other board r depth a with
    | none=>simp [bits,live,marker,key]
    | some z=>
      have small : D*S_+z.val+1<2^b:=by
        have h:=z.isLt
        rw [Nat.succ_mul] at word
        omega
      simp only [bits,live,ite_true,marker,key,Option.elim_some,Fin.val_cast_of_lt small,true_and]
      rw [self_value]
      simp [Equiv.symm_apply_apply,eq_comm]
  · simp [bits,live]
end
end Hierarchy.DescentResetTrunkChip
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
local notation "oldGraph" => W.granular B.count (z*G.b) B.fit
local notation "same" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (oldGraph) (T).home (placement).input (T).hub same (Z).bank (Z).tables
local notation "key" => DescentOrderedReset.grains W B.count B.order


open DescentResetFieldAssembler DescentIssuedFallbackPanel DescentNextSignedWindow
local notation "rows" => blocks B
local notation "End" => (oldGraph).graph.Edge
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
local notation "shapeIdx" v:arg => ((finProdFinEquiv.symm v : Fin (Fintype.card input.V)×Fin (roster_).card).2)
local notation "oldIdx" v:arg => ((finProdFinEquiv.symm v : Fin (Fintype.card input.V)×Fin (roster_).card).1)


open DescentResetPeerUnionRAM.Candidates
/-- Exact marker on arbitrary candidate ROM sockets, including the three
padding cells at the end of the public roster. -/
theorem trunk_marker_all {D₀ b : ℕ} (old : Fin (Fintype.card input.V)→Fin D₀→Option (Fin (Fintype.card input.V)))
    (v : B.next.V) (y : Fin pitch) (chip : Fin groups→Block k→Cell 1)
    (seen : ∀g₀ lo,(chip g₀ lo).val=1 ↔ trunkTest B ((g₀,v),lo))
    (word : (D₀+1)*(roster_).card<2^b) :
    (∃(j : Fin (DescentResetPeerUnionRAM.Candidates.count (roster_).card D₀)) (g₀ : Fin groups) (lo : Block k),
      candidate old (rank v) j=some y ∧
      (DescentResetTrunkChip.bits (Z).graph radius depth_ D₀ (shapeIdx (rank v)) (chip g₀ lo):Cell b).val=j.val+1) ↔
      ∃t : (Z).Fallback,rawPeer B (trunkParent B t) (rank v).val y.val:=by
  rw [trunk_evidence]
  constructor
  · rintro ⟨j,g₀,lo,physical,digit⟩
    obtain ⟨mark,root,shape⟩:=(DescentResetTrunkChip.marker_socket (Z).graph radius depth_ old (rank v) y (chip g₀ lo) word).1 ⟨j,physical,digit⟩
    exact ⟨root,shape,g₀,lo,(seen g₀ lo).1 mark⟩
  · rintro ⟨root,shape,g₀,lo,signal⟩
    obtain ⟨j,physical,digit⟩:=(DescentResetTrunkChip.marker_socket (Z).graph radius depth_ old (rank v) y (chip g₀ lo) word).2
      ⟨(seen g₀ lo).2 signal,root,shape⟩
    exact ⟨j,g₀,lo,physical,digit⟩


/-- Widening the old actor pitch preserves both radix digits on every actual
endpoint. The criterion remains exact on all numeric receiver probes. -/
theorem trunk_marker_padded {H D₀ b : ℕ} (pad : Fintype.card input.V≤H)
    (old : Fin H→Fin D₀→Option (Fin H)) (v : B.next.V) (y : Fin (H*(roster_).card))
    (chip : Fin groups→Block k→Cell 1)
    (seen : ∀g₀ lo,(chip g₀ lo).val=1 ↔ trunkTest B ((g₀,v),lo))
    (word : (D₀+1)*(roster_).card<2^b) :
    let named:=(Z).rawHostRank T ((vertexCode).trans (Fin.castLEEmb pad))
    (∃(j : Fin (DescentResetPeerUnionRAM.Candidates.count (roster_).card D₀)) (g₀ : Fin groups) (lo : Block k),
      candidate old (named v) j=some y ∧
      (DescentResetTrunkChip.bits (Z).graph radius depth_ D₀ ((finProdFinEquiv.symm (named v)).2) (chip g₀ lo):Cell b).val=j.val+1) ↔
      ∃t : (Z).Fallback,rawPeer B (trunkParent B t) (named v).val y.val:=by
  intro named
  let a:=(finProdFinEquiv.symm (rank v) : Fin (Fintype.card input.V)×Fin (roster_).card)
  let a':=(finProdFinEquiv.symm (named v) : Fin H×Fin (roster_).card)
  let t:=(finProdFinEquiv.symm y : Fin H×Fin (roster_).card)
  have first : a.1.val=a'.1.val:=rfl
  have second : a.2=a'.2:=rfl
  have sameName : (rank v).val=(named v).val:=rfl
  constructor
  · rintro ⟨j,g₀,lo,ptr,digit⟩
    obtain ⟨occupied,hRoot,hShape⟩:=(DescentResetTrunkChip.marker_socket (Z).graph radius depth_ old (named v) y (chip g₀ lo) word).1 ⟨j,ptr,digit⟩
    let y₀ : Fin pitch:=finProdFinEquiv (a.1,t.2)
    have value : y₀.val=y.val:=by
      change t.2.val+(roster_).card*a.1.val=y.val
      rw [first,show a'.1=t.1 from hRoot]
      exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply y)
    have sig : ∃e,rawPeer B (trunkParent B e) (rank v).val y₀.val:=(trunk_evidence B v y₀).2
      ⟨by simp [y₀,a],by
        simp only [y₀,Equiv.symm_apply_apply]
        exact (congrArg (other_) second).trans hShape,
        g₀,lo,(seen g₀ lo).1 occupied⟩
    rwa [sameName,value] at sig
  · rintro ⟨e,orig⟩
    have bounds:=(peer_word_range B (trunkParent B e) (named v).val y.val orig).2
    let y₀ : Fin pitch:=⟨y.val,bounds⟩
    obtain ⟨hRoot,hShape,g₀,lo,bit⟩:=(trunk_evidence B v y₀).1 ⟨e,orig⟩
    have hRoot' : a'.1=t.1:=Fin.ext ((first.symm).trans (congrArg Fin.val hRoot))
    have hShape' : other_ a'.2=some t.2:=by rw [←second];exact hShape
    obtain ⟨j,ptr,digit⟩:=(DescentResetTrunkChip.marker_socket (Z).graph radius depth_ old (named v) y (chip g₀ lo) word).2
      ⟨(seen g₀ lo).2 bit,hRoot',hShape'⟩
    exact ⟨j,g₀,lo,ptr,digit⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
