import OAI.Hierarchy.DescentOrdinaryCapturePaths

namespace OAI
/-! # Each positive raw edge has both genuine rooted endpoint walks, including captures -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup DescentCableDonorNames
open scoped Classical BigOperators Fin.CommRing
noncomputable section

namespace Stage
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
local notation "names" => cableNames k rank
local notation "next" => rotor A rank
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "N" => W.graph
local notation "traffic" => nativeTraffic N W.core home
local notation "Positive" => DescentSharedCableNames.Stage.Positive A
local notation "out" => DescentSharedCableNames.Stage.outgoing A native S ready
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (profile : ℕ) (same : ∀e∈W.core,scanColorAt he A.stage (W.graph.src e)=scanColorAt he A.stage (W.graph.dst e)) (lay : Bool)
local notation "s" => shape (2^k) A.degree (2*A.cap) profile
local notation "pick" => colorPick N W.core home color A.cap
local notation "Packs" => coloredPack N W.core home color A.cap
local notation "venue" => newSite N pick lay Packs
local notation "key" => nativeKey N W.core home color A.cap addr same lay
local notation "here" => fun h x=>resolved A.cap profile (panel h) lay x
local notation "peers" => fun h v x=>Option.elim (next h v) (0,0,0) (fun other=>here other x)

def rawParentRows (e : Positive) : Fin 11→Option (Walk×Walk) :=
  let v:=(N).src e.val
  let h:=A.pos v
  let x:=A.block v
  let z:=parentHeads (short:=short) A native S ready rank win profile lay e
  let dst:=look (here h) (peers h) ((sourceHandle A native S ready rank e).neighbor.val+1,x.val)
  ParentIncidence.rawIssue (parentChosen (short:=short) A native S ready rank win profile e) z.old dst z.born
local notation "rows" => rawParentRows (short:=short) A native S ready rank win profile lay
local notation "heads" => parentHeads (short:=short) A native S ready rank win profile lay
local notation "Pairs" => NativePair N W.core home color A.cap

set_option maxHeartbeats 1200000 in
include coord named fit winner df edgeOrder in
theorem raw_parent_actual (edge : DescentRawCablePanel.Live A pick) :
    let donor : Positive:=⟨anchor pick edge.val,edge.property⟩
    let x:=venue (GadgetNetwork.source N edge.val)
    let y:=venue (GadgetNetwork.target N pick edge.val)
    ∃t,rows donor (role edge.val)=some t ∧ ParentIncidence.Actual next (A.pos ((N).src donor.val)) t (key x) (key y) := by
  obtain ⟨e,pos⟩:=edge
  rcases e with e|⟨p,j⟩|⟨p,j⟩
  · let z : Positive:=⟨e,pos⟩
    let h:=A.pos ((N).src e)
    let x:=A.block ((N).src e)
    let w:=look (here h) (peers h) ((sourceHandle A native S ready rank z).neighbor.val+1,x.val)
    have src:=prior_head A native S ready names win next he rank coord named fit winner
      (rotor_sorted A rank) (rotor_routes A native S ready rank) df edgeOrder profile same lay ((N).src e) (headSlot A native S ready z)
    have dst:=physical_walk A native S ready rank win he coord named fit winner df edgeOrder profile same lay z true
    have chosen:=parent_chosen A native S ready rank win he coord named fit winner df edgeOrder profile z
    have row : rows z 0 = some ((heads z).old,if parentChosen (short:=short) A native S ready rank win profile z then (heads z).old else w) := rfl
    cases selected : GadgetNetwork.selected N pick e with
    | none =>
      have no := chosen.trans (congrArg Option.isSome selected)
      change parentChosen (short:=short) A native S ready rank win profile z=false at no
      rw [no] at row
      refine ⟨((heads z).old,w),row,src,?_⟩
      have endpoint : GadgetNetwork.target N pick (.inl e) = .inl ((N).dst e) := by
        simp only [GadgetNetwork.target,selected]
      change walked next h w (key (venue (GadgetNetwork.target N pick (.inl e))))
      rw [endpoint]
      exact dst
    | some i =>
      have yes := chosen.trans (congrArg Option.isSome selected)
      change parentChosen (short:=short) A native S ready rank win profile z=true at yes
      rw [yes] at row
      let collapsed (v : (N).Edge) :=
        venue (GadgetNetwork.source N (.inl v))=venue (GadgetNetwork.target N pick (.inl v))
      have old : collapsed (pick i) := DescentRawCablePanel.picked_old N pick lay Packs i.1 i.2
      have loc : collapsed e := (congrArg collapsed (GadgetNetwork.selected_spec N pick selected)).mp old
      refine ⟨((heads z).old,(heads z).old),row,src,?_⟩
      change walked next h ((heads z).old) (key (venue (GadgetNetwork.target N pick (.inl e))))
      rw [←loc]
      exact src
  · let z : Positive:=⟨pick (p,0),pos⟩
    obtain ⟨f,hf,live⟩:=parent_born A native S ready rank win he coord named fit winner df edgeOrder profile same lay z p rfl
    let idx := role (.inr (.inl (p,j)) : Raw (N).Edge Pairs)
    have index_eq : idx=Fin.succ (Fin.castAdd 8 j) := Fin.ext (by simp [idx,role];omega)
    let step:=f (demandDst j)
    have row : rows z idx=some (step,step) := by
      rw [index_eq]
      change ParentIncidence.rawIssue _ _ _ (heads z).born _=_
      rw [ParentIncidence.raw_arm,hf]
      rfl
    refine ⟨(step,step),row,live _,?_⟩
    have loc:=DescentRawCablePanel.picked_arm N pick lay Packs p j
    change walked next _ step (key (venue (GadgetNetwork.target N pick (.inr (.inl (p,j))))))
    rw [←loc]
    exact live _
  · let z : Positive:=⟨pick (p,0),pos⟩
    obtain ⟨f,hf,live⟩:=parent_born A native S ready rank win he coord named fit winner df edgeOrder profile same lay z p rfl
    let idx := role (.inr (.inr (p,j)) : Raw (N).Edge Pairs)
    have index_eq : idx=Fin.succ (Fin.natAdd 2 j) := Fin.ext (by simp [idx,role];omega)
    have row : rows z idx=some (f (supplySrc j),f (supplyDst j)) := by
      rw [index_eq]
      change ParentIncidence.rawIssue _ _ _ (heads z).born _=_
      rw [ParentIncidence.raw_supply,hf]
      rfl
    exact ⟨_,row,live _,live _⟩

end Stage
end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
