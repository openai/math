import OAI.Hierarchy.DescentPackedActorVenue

namespace OAI
/-! # Literal old quotient key read from the packed local matching panel -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup DescentOldOccurrenceRAM PackedLocalMatch
open scoped Classical BigOperators
noncomputable section

def located {Z : Type} {D : ℕ} (next : Z→Fin D→Option Z) (root : Z) (q : Address)
    (trueKey : DescentHostDirectory.Key Z) : Prop :=
  location next root q=some trueKey.1 ∧ q.2=(heap trueKey.2.1,trueKey.2.2)

private def atReport {r D p b : ℕ} (B profile : ℕ) (u : Panel r D p b) (lay : Bool)
    (leafAt slot : ℕ) : Address :=
  let shapeAt := shape r D p profile
  let source := inputs shapeAt B leafAt u (fun _=>0)
  let output := decodeOutput shapeAt (lookupCell shapeAt (encodeInput source))
  if bounds : 0 < slot ∧ slot ≤ shapeAt.packs then
    match headRow source output ⟨slot-1,by omega⟩ with
    | none => (0,leafAt,slot)
    | some j => thickAddress u lay (centerAt lay output j).val
  else (0,leafAt,slot)

namespace Stage
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (names : DescentSharedCableNames.Stage.Host J V k↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (next : (J×V)→Fin A.degree→Option (J×V)) (he : 0≤ε)
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "N" => W.graph
local notation "T" => nativeTraffic N W.core home
local notation "n" => binCount (2^k) A.degree
variable (rank : (J×V)↪ℕ) (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 +
        (scanColorAt he A.stage u).toNat)
    (sorted : RosterSorted A next rank) (route : Routes A native S ready names next) (df : A.degree<2^short)
    (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f) (profile : ℕ) (c : ScanColonies he A.stage)
local notation "s" => shape (2^k) A.degree (2*A.cap) profile
local notation "pk" => slabPacking T A.cap (thinList home color c) (thickList home color c)
local notation "Pair" => Matched T A.cap (thinList home color c) (thickList home color c)


variable (same : ∀e∈W.core, scanColorAt he A.stage (W.graph.src e) = scanColorAt he A.stage (W.graph.dst e)) (lay : Bool)
local notation "P" => coloredPack N W.core home color A.cap
local notation "pick" => colorPick N W.core home color A.cap
local notation "venue" => newSite N pick lay P
local notation "key" => nativeKey N W.core home color A.cap addr same lay
local notation "raw" => packAddress N W.core home color A.cap addr
local notation "owner" => resolve (chosenSlot N W.core home color A.cap) (chosenCenter N W.core home color A.cap lay)

private theorem old_key (u : (N).Site) : key (venue (.inl u))=raw (owner (P u)) := rfl

private theorem pack_case (u : (N).Site) :
    P u=.inl (home u) ∨ ∃j,P u=.inr ⟨home u,j⟩ := by
  unfold coloredPack packLabel
  split
  · exact Or.inr ⟨_,rfl⟩
  · exact Or.inl rfl

private theorem thin_global {u : (N).Site} (q : Fin (slabPacking T A.cap (thinList home color (home u)) (thickList home color (home u))).decisions.length) (absent : ¬∃e : Matched T A.cap (thinList home color (home u))
      (thickList home color (home u)),e.2.1.val.val=q.val) :
    ¬∃p,chosenSlot N W.core home color A.cap p=⟨home u,q⟩ := by
  rintro ⟨⟨c,e⟩,eqn⟩
  have groupEq : c=home u:=congrArg Sigma.fst eqn
  subst c
  exact absent ⟨e,congrArg (fun slot : NativeSlot N W.core home color A.cap => slot.2.val) eqn⟩

set_option maxHeartbeats 650000 in
include rank coord named fit winner sorted route df edgeOrder in
theorem old_location (u : (N).Site) :
    let input:=panel (A.pos u)
    located next (A.pos u) (resolved A.cap profile input lay (A.block u)) (key (venue (.inl u))) := by
  dsimp only
  let c:=home u
  let f:=fun _ : Fin (s).pairs=>(0:Cell (s).digit)
  let input:=panel (addr c).1
  let x:=inputs s A.cap (heap (addr c).2) input f
  let data:=decodeOutput s (lookupCell s (encodeInput x))
  have baseSpace := (measured_inputs A native S ready names win next he rank coord named fit winner route df profile c f).1
  have small : (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions.length≤(s).packs := by
    have h:=congrArg List.length (slabPacking T A.cap (thinList home color c) (thickList home color c)).order
    simp only [List.length_map] at h
    exact h.le.trans baseSpace
  have side:=source_host A he u
  have leafAt:=winner_leaf A native S ready names win next he fit winner u
  have slot:=original_pack A native S ready names win next he fit winner s coord (block_order A rank coord named) df
    (fun h x e=>subword A native S ready names win next he fit winner h x e route) u
  rw [old_key]
  let leafAtOld := leaf ((panel (A.pos u)).winner (A.block u)).val
  change located next (A.pos u) (atReport A.cap profile (panel (A.pos u)) lay leafAtOld
    (readPack (packs (panel (A.pos u)) (s).bins A.cap leafAtOld) (A.block u))) _
  dsimp only [leafAtOld]
  rw [leafAt,slot,←side]
  rcases pack_case A he u with thick | ⟨j,thin⟩
  · simp only [thick]
    exact ⟨rfl,rfl⟩
  · simp only [thin]
    let v : Fin (s).packs := j.castLE small
    have branch : 0<j.val+1 ∧ j.val+1≤(s).packs := ⟨Nat.succ_pos _,Nat.succ_le_of_lt (j.isLt.trans_le small)⟩
    change located next (addr c).1 (atReport A.cap profile input lay (heap (addr c).2) (j.val+1))
      (raw (owner (.inr ⟨c,j⟩)))
    dsimp only [atReport]
    rw [dite_eq_left branch]
    have hrow : (⟨j.val+1-1,by omega⟩ : Fin (s).packs)=v := Fin.ext (by simp [v])
    cases head : headRow x data v with
    | none=>
      simp only [hrow,show headRow
        (inputs s A.cap (heap (addr c).2) input (fun _=>0))
        (decodeOutput s (lookupCell s (encodeInput
          (inputs s A.cap (heap (addr c).2) input (fun _=>0))))) v = none from head]
      have empty:=(head_miss A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c f v).mp head
      have no:=thin_global A he (u:=u) j empty
      rw [resolve,dite_eq_right no]
      exact ⟨rfl,rfl⟩
    | some q=>
      simp only [hrow,show headRow
        (inputs s A.cap (heap (addr c).2) input (fun _=>0))
        (decodeOutput s (lookupCell s (encodeInput
          (inputs s A.cap (heap (addr c).2) input (fun _=>0))))) v = some q from head]
      obtain ⟨e,which,_,read⟩:=head_issued A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c f v q head
      let pair : NativePair N W.core home color A.cap := ⟨c,e⟩
      have atSlot : chosenSlot N W.core home color A.cap pair=⟨c,j⟩ := by
        apply congrArg (Sigma.mk c)
        exact Fin.ext which
      have active : owner (.inr (chosenSlot N W.core home color A.cap pair)) =
          .inl (chosenCenter N W.core home color A.cap lay pair) :=
        resolve_active _ _ (native_coherent _ A.cap _ _ (fun _ c=>c) lay) pair
      rw [←atSlot,active]
      change located next (addr c).1 (thickAddress input lay (centerAt lay data q).val) _
      rw [read lay,raw_val A native S ready names he profile c true (picked A he c e true) _]
      have engine := thick_location A native S ready names win next he fit winner route c e lay
      let receiver:=thickCenter N pick lay pair
      have oldEq : (if lay then (N).dst (picked A he c e true).val else (N).src (picked A he c e true).val)=receiver := by
        rw [picked_old A he c e true]
        rfl
      dsimp only at engine
      rw [oldEq] at engine
      have dest := packed_home N W.core home color A.cap addr receiver
      rw [native_centerAt N W.core home color A.cap same lay pair] at dest
      have spatial : addr (chosenCenter N W.core home color A.cap lay pair)=addr (home receiver) := dest
      rw [show raw (.inl (chosenCenter N W.core home color A.cap lay pair))=
          ((addr (home receiver)).1,(addr (home receiver)).2,0) by
        change ((addr _).1,(addr _).2,0)=_
        rw [spatial]]
      exact ⟨engine.1.trans (congrArg some (source_host A he receiver).symm),engine.2⟩

end Stage
end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
