import OAI.Hierarchy.DescentPrivateCandidateShelf
import OAI.Hierarchy.DescentContactCoordinateJoint

namespace OAI
/-! # The original masked private row at every receiver, including unused slots -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks DescentSharedCableNames
open scoped Classical
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
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))


open DescentSIMDLookup DescentResetLocalRoster DescentPackedFallbackTree DescentPackedPrivateMenu DescentParallelBase

private theorem slot_address (u : Host) (s : Bool) (t : (Z).RootTicket T) (l : Fin capacity)
    (p : PrivateOccurrence B) :
    privateRawAt B (vertexCode (receiverRoot B u).1) (receiverRoot B u).2 s t l p ↔
      receiverRoot B u=((Z).rootVertex T p.1.2,(Z).rootBlock T p.1.2) ∧ privateTicket B p=(s,t,l) :=by
  constructor
  · rintro ⟨side,location,wire⟩
    exact ⟨Prod.ext ((vertexCode).injective (congrArg Prod.fst location).symm)
        (congrArg (fun v=>v.2.1) location).symm,
      Prod.ext side (Prod.ext (congrArg (fun v=>v.2.2) location) wire)⟩
  · rintro ⟨location,ticket⟩
    exact ⟨congrArg Prod.fst ticket,
      Prod.ext (congrArg vertexCode (congrArg Prod.fst location).symm)
        (Prod.ext (congrArg Prod.snd location).symm (congrArg (fun x=>x.2.1) ticket)),
      congrArg (fun x=>x.2.2) ticket⟩

set_option maxHeartbeats 600000 in
/-- The equality test in the compiled private mask uses a common old root
and an injective successor shape digit on each side. Its flag and grain
column both read the width of the original five-field record. -/
theorem private_reached_meta {b n₀ : ℕ} (u : Host) (s : Bool) (t : (Z).RootTicket T) (l : Fin capacity)
    (panel : (Z).Fallback→Panel height n₀) (row : Fin 5→ℕ) («fields» : Fin 9→Cell b)
    (unit : 0<(Z).unit)
    (numbers : row=values (Z).graph ((Z).k-(T).commonDepth) height n₀ (Z).layerBits C (Z).width s l.val
      ((Z).rootsOf T vertexCode unit s panel t (vertexCode (receiverRoot B u).1) (receiverRoot B u).2))
    (issued : ∀p, privateRawAt B (vertexCode (receiverRoot B u).1) (receiverRoot B u).2 s t l p →
      (Z).expand T vertexCode p.1.2 row=(Z).actualRecord T vertexCode (privateWire B p))
    (rad halo : ℕ) (radPos : 0<rad)
    (flag : («fields» 0).val=if row 0=1 then row 3 else 0)
    (units : («fields» 8).val=(«fields» 0).val)
    (source : («fields» 1).val=rad*(if row 0=1 then row 1 else 0)+halo)
    (target : («fields» 2).val=rad*(if row 0=1 then row 2 else 0)+halo)
    (current : («fields» 3).val=rad*relativeShape B u+halo)
    (ranks : ∀p,localOrigin B u (privateShelfIndex B (localPrivateId _ _ capacity (s,t,l)))=some p →
      («fields» 4).val=localClass B u ((blocks B).src p.val) ∧
      («fields» 5).val=localClass B u ((blocks B).dst p.val) ∧ («fields» 6).val=localClass B u u)
    (self : («fields» 7).val≠0 ↔ u∉Stage.near B.next.placement u) :
    DescentCandidateMaskRAM.render «fields»=DescentResetFieldAssembler.raw b
      («meta» B u (localOrigin B u (privateShelfIndex B (localPrivateId _ _ capacity (s,t,l))))) := by
  let id₀:=localPrivateId ((Z).k-(T).commonDepth) (2^(Z).n) capacity
  let j:=privateShelfIndex B (id₀ (s,t,l))
  have shapes:=private_raw_presence B unit s t (vertexCode (receiverRoot B u).1) (receiverRoot B u).2 l panel row numbers issued
  by_cases has : ∃p,privateRawAt B (vertexCode (receiverRoot B u).1) (receiverRoot B u).2 s t l p
  · obtain ⟨p,atRow⟩:=has
    obtain ⟨home,ticket⟩:=(slot_address B u s t l p).1 atRow
    have installed:=issued p atRow
    have stamp:=(issued_relative B p row installed unit).1
    have vis : DescentCandidateMaskRAM.visible «fields» ↔ active (blocks B) u (privateWire B p) :=by
      rw [←private_mask_iff B u p row installed unit home]
      have cancel (a b : ℕ) : rad*a+halo=rad*b+halo ↔ a=b:=
        ⟨fun eqn=>Nat.mul_left_cancel radPos (Nat.add_right_cancel eqn),fun eqn=>congrArg (rad*·+halo) eqn⟩
      simp only [DescentCandidateMaskRAM.visible,units,flag,source,target,current,stamp,ite_true,cancel,true_and]
      omega
    have idEq : id₀ (privateTicket B p)=id₀ (s,t,l):=congrArg id₀ ticket
    have chosen:=private_selected_origin B u p home
    dsimp only at chosen
    rw [idEq] at chosen
    by_cases live : active (blocks B) u (privateWire B p)
    · rw [dite_eq_left live] at chosen
      have roster : localRoster B u ⟨privateWire B p,live⟩=j:=(local_read B u j _).1 chosen
      have three:=ranks _ chosen
      have amount:=(issued_relative B p row installed unit).2.2.2.1
      have final:=private_at_slot B u p live «fields» (vis.2 live) three.1 three.2.1 three.2.2 self
        (by rw [units,flag,ite_eq_left stamp];exact amount)
      dsimp only at final
      rwa [roster] at final
    · rw [dite_eq_right live] at chosen
      apply (DescentCandidateMaskRAM.masked «fields» (mt vis.1 live)).trans
      change DescentResetFieldAssembler.raw b («meta» B u none) = DescentResetFieldAssembler.raw b («meta» B u (localOrigin B u j))
      exact congrArg (fun z => DescentResetFieldAssembler.raw b («meta» B u z)) chosen.symm
  · have empty:=shapes.2.1 (fun p atRow=>has ⟨p,atRow⟩)
    have silent : («fields» 0).val=0:=by simp [flag,empty]
    have noSlot : localOrigin B u j=none :=by
      cases found:localOrigin B u j with
      | none=>rfl
      | some a=>
        obtain ⟨p,eqn,key⟩:=(private_shelf_iff B u _ a).1 found
        have activeP : active (blocks B) u (privateWire B p):=by rw [←eqn]; exact a.property
        exact (has ⟨p,(slot_address B u s t l p).2
          ⟨private_owner B u p activeP.2,id₀.injective key⟩⟩).elim
    rw [DescentCandidateMaskRAM.vacant_or_empty «fields» (Or.inl silent)]
    change _=DescentResetFieldAssembler.raw b («meta» B u (localOrigin B u j))
    rw [noSlot]
    rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
