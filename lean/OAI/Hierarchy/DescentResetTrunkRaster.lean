import OAI.Hierarchy.DescentResetTrunkSource
import OAI.Hierarchy.DescentResetStemMetadata

namespace OAI
/-! # Resolving the trunk on a public host pair, for occupied and empty groups -/
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
local notation "touch" => fun (u : Host) (t : (Z).Fallback) => ((rows).src (trunkParent B t)=u ∨ (rows).dst (trunkParent B t)=u)


local notation "rank" => (Z).rawHostRank T vertexCode

structure TrunkPorts (V : Type) where
  left : V
  right : V
  core : Bool

/-- This address map is the same in every group and low digit. The two names
are read off the public receiver by swapping its Boolean terminal side. -/
def trunkLabels (v : B.next.V) : Option (TrunkPorts B.next.V):=
  match v.val with
  | .trunk _ key =>
    if good : .trunk false key∈(Z).commonNames T ∧ .trunk true key∈(Z).commonNames T then
      some ⟨⟨_,good.1⟩,⟨_,good.2⟩,key.2.2.isSome⟩
    else none
  | _ => none

def portAt (u : Host) (v : B.next.V) : Host:=((u.1.1,v),u.2)

theorem trunk_labels_at (u : Host) (t : (Z).Fallback) (s : Bool)
    (here : (trunkCoordinate B u).1=.trunk s (short t)) (hi : (high_ u).val=hi_ t) :
    ∃p,trunkLabels B u.1.2=some p ∧ portAt B u p.left=(rows).src (trunkParent B t) ∧
      portAt B u p.right=(rows).dst (trunkParent B t) ∧ p.core=((T).code t).2.2.isSome := by
  let left:=(rows).src (trunkParent B t)
  let right:=(rows).dst (trunkParent B t)
  have l:=trunk_side B t false
  have r:=trunk_side B t true
  have lm : .trunk false (short t)∈(Z).commonNames T:= l.1 ▸ left.1.2.property
  have rm : .trunk true (short t)∈(Z).commonNames T:= r.1 ▸ right.1.2.property
  let p : TrunkPorts B.next.V:=⟨⟨_,lm⟩,⟨_,rm⟩,((T).code t).2.2.isSome⟩
  refine ⟨p,?_,trunkCoordinate_injective B (Prod.ext l.1.symm (Fin.ext (hi.trans l.2.symm))),
     trunkCoordinate_injective B (Prod.ext r.1.symm (Fin.ext (hi.trans r.2.symm))),rfl⟩
  change u.1.2.val=_ at here
  simp only [trunkLabels,here]
  exact dite_eq_left ⟨lm,rm⟩

theorem trunk_labels_here (u : Host) (p : TrunkPorts B.next.V) (status : trunkLabels B u.1.2=some p) :
    ∃key,((u.1.2.val=.trunk false key ∨ u.1.2.val=.trunk true key) ∧
      p.left.val=.trunk false key ∧ p.right.val=.trunk true key ∧ p.core=key.2.2.isSome) := by
  unfold trunkLabels at status
  cases h : u.1.2.val with
  | good=>simp [h] at status
  | fall=>simp [h] at status
  | trunk s key=>
    simp only [h] at status
    split at status
    next yes=>
      injection status with exactP
      subst p
      exact ⟨key,by cases s <;> simp⟩
    next no=>simp at status

def hostShape (v : B.next.V) : Meta:=
  match trunkLabels B v with
  | none=>.blank
  | some p=>
    let here:=(rank v).val
    let neighbors:=(B.next.placement.near v).map ((rank).trans Fin.valEmbedding)
    ⟨true,stemOrdinal here neighbors ((rank p.left).val),stemOrdinal here neighbors ((rank p.right).val),
     stemOrdinal here neighbors here,decide (here∉neighbors),p.core,0⟩

def hostStem (u : Host) (j : Fin half) : Meta:=
  match trunkLabels B u.1.2 with
  | none=>.blank
  | some p=>let donor:=portAt B u p.right
            «meta» B donor (localOrigin B donor (incomingCandidate B j))

private theorem stem_trunk (u : Host) (j : Fin half) (bit : face false (hostStem B u j)=true) :
    ∃t : (Z).Fallback,touch u t:=by
  cases status : trunkLabels B u.1.2 with
  | none=>simp [hostStem,status,face,Meta.blank] at bit
  | some p=>
    let donor:=portAt B u p.right
    have b : face false («meta» B donor (localOrigin B donor (incomingCandidate B j)))=true:=by
      simpa [hostStem,status,donor] using bit
    cases hit : localOrigin B donor (incomingCandidate B j) with
    | none=>simp [hit,«meta»,face,Meta.blank] at b
    | some x=>
      rw [hit] at b
      have src:=(meta_face B donor x false).1 b
      obtain ⟨e,tag,_⟩:=incoming_origin B donor j x hit
      rw [tag] at src
      let t:=(T).home ((old).graph.dst e)
      have atRelay : (rows).dst (trunkParent B t)=donor:=((incoming_home B t e).2 rfl).symm.trans src
      have coords:=trunk_side B t true
      change (trunkCoordinate B ((rows).dst (trunkParent B t))).1=_ ∧
        (trunkCoordinate B ((rows).dst (trunkParent B t))).2.val=_ at coords
      rw [atRelay] at coords
      obtain ⟨key,atU,left,right,core⟩:=trunk_labels_here B u p status
      have names : key=short t:=(Node.trunk.inj (right.symm.trans coords.1)).2
      rcases atU with atU|atU
      · refine ⟨t,Or.inl (trunkCoordinate_injective B ?_)⟩
        have lh:=trunk_side B t false
        exact Prod.ext (lh.1.trans ((congrArg (Node.trunk false) names.symm).trans atU.symm))
          (Fin.ext (lh.2.trans coords.2.symm))
      · refine ⟨t,Or.inr (trunkCoordinate_injective B ?_)⟩
        exact Prod.ext ((trunk_side B t true).1.trans ((congrArg (Node.trunk true) names.symm).trans atU.symm))
          (Fin.ext ((trunk_side B t true).2.trans coords.2.symm))

private theorem host_stem_sum (u : Host) (t : (Z).Fallback) (p : TrunkPorts B.next.V)
    (status : trunkLabels B u.1.2=some p) (right : portAt B u p.right=(rows).dst (trunkParent B t)) :
    (∑j,(face false (hostStem B u j)).toNat)=trunkUnits B t := by
  calc
    _ = ∑j,(incomingBit B (portAt B u p.right) j).toNat := by simp only [hostStem,status,incomingBit]
    _ = _ := congrArg (fun h : Host => ∑j,(incomingBit B h j).toNat) right

theorem trunk_raster (u : Host) :
    DescentResetTrunkIssue.complete (hostShape B u.1.2) (∑j,(face false (hostStem B u j)).toNat)=«meta» B u (localOrigin B u (trunkCandidate B)):=by
  by_cases positive : ∃j,face false (hostStem B u j)=true
  · obtain ⟨j,bit⟩:=positive
    obtain ⟨t,ends⟩:=stem_trunk B u j bit
    obtain ⟨p,status,left,right,core⟩ : ∃p,trunkLabels B u.1.2=some p ∧
        portAt B u p.left=(rows).src (trunkParent B t) ∧ portAt B u p.right=(rows).dst (trunkParent B t) ∧
        p.core=((T).code t).2.2.isSome:=by
      rcases ends with l|r
      · subst u;exact trunk_labels_at B _ t false (trunk_side B t false).1 (trunk_side B t false).2
      · subst u;exact trunk_labels_at B _ t true (trunk_side B t true).1 (trunk_side B t true).2
    have tally := host_stem_sum B u t p status right
    have nonzero : 0<trunkUnits B t:=by
      rw [←tally]
      have le:=Finset.single_le_sum (fun a _=>Nat.zero_le (face false (hostStem B u a)).toNat)
        (Finset.mem_univ j)
      exact lt_of_lt_of_le (show 0 < (face false (hostStem B u j)).toNat from bit ▸ Nat.zero_lt_one) le
    let x : Local rows u:=⟨trunkParent B t,⟨by rw [trunk_units];exact nonzero,ends⟩⟩
    have sl:=stem_ordinal_read B u ((rows).src x.val) (DescentResetWindowResidentSources.source_mem B.next.placement
      (B.next.order.trans Fin.valEmbedding) (blocks B) u x)
    have dl:=stem_ordinal_read B u ((rows).dst x.val) (destination_mem B u x)
    have hl:=stem_ordinal_read B u u (Finset.mem_insert_self ..)
    have ls : p.left=((rows).src x.val).1.2:=congrArg (fun a : Host=>a.1.2) left
    have rs : p.right=((rows).dst x.val).1.2:=congrArg (fun a : Host=>a.1.2) right
    rw [trunk_meta B u t ends,tally]
    change DescentResetTrunkIssue.complete (hostShape B u.1.2) (trunkUnits B t)=_
    have isHost : (B.next.placement.near u.1.2).map ((rank).trans Fin.valEmbedding)=stemNeighbors B u:=rfl
    simp [hostShape,status,DescentResetTrunkIssue.complete,trunkHeader,Nat.ne_of_gt nonzero,nonzero,ls,rs,core,
      isHost,sl,dl,hl,stem_absent_read,x]
  · have zero (j : Fin half) : face false (hostStem B u j)=false:=Bool.eq_false_iff.mpr (fun y=>positive ⟨j,y⟩)
    have blank (sh : Meta) : DescentResetTrunkIssue.complete sh 0=.blank := by
      simp [DescentResetTrunkIssue.complete]
    simp only [zero,Bool.toNat_false,Finset.sum_const_zero,blank]
    cases act : acceptedTrunk B u with
    | none=>
      apply Eq.symm
      apply trunk_no_row
      intro t
      exact not_or.mp (fun y=>Option.some_ne_none t (((accepted_hit B u t).2 y).symm.trans act))
    | some t=>
      have ends:=(accepted_hit B u t).1 act
      obtain ⟨p,status,left,right,core⟩ : ∃p,trunkLabels B u.1.2=some p ∧
          portAt B u p.left=(rows).src (trunkParent B t) ∧ portAt B u p.right=(rows).dst (trunkParent B t) ∧
          p.core=((T).code t).2.2.isSome:=by
        rcases ends with l|r
        · subst u;exact trunk_labels_at B _ t false (trunk_side B t false).1 (trunk_side B t false).2
        · subst u;exact trunk_labels_at B _ t true (trunk_side B t true).1 (trunk_side B t true).2
      have all : trunkUnits B t=0:=by
        have e := host_stem_sum B u t p status right
        simpa only [zero,Bool.toNat_false,Finset.sum_const_zero] using e.symm
      rw [trunk_meta B u t ends,trunkHeader,ite_eq_left all]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
