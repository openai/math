import OAI.Hierarchy.DescentDonorNumericHeads
import OAI.Hierarchy.DescentPackedDonorPrimitives
import OAI.Hierarchy.DescentPackedPhysicalWalk
import OAI.Hierarchy.DescentPackedDonorGrains

namespace OAI
/-! # Decode the donor selection and chosen row at the actual old source -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 1000000
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
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 +
        (scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (profile : ℕ) (same : ∀e∈W.core,scanColorAt he A.stage (W.graph.src e) = scanColorAt he A.stage (W.graph.dst e)) (lay : Bool)
local notation "pick" => colorPick N W.core home color A.cap

local notation "T" => nativeTraffic N W.core home
local notation "s" => shape (2^k) A.degree (2*A.cap) profile

def donorAddress (e : DescentSharedCableNames.Stage.Positive A) :=
  (A.block ((N).src e.val)).val*(2*A.cap)+(DescentSharedCableNames.Stage.outgoing A native S ready e).val

theorem source_bound (e : DescentSharedCableNames.Stage.Positive A) :
    donorAddress A native S ready e<2^(s).digit := by
  let j:=DescentSharedCableNames.Stage.outgoing A native S ready e
  let x:=A.block ((N).src e.val)
  have low : j.val<2*A.cap := j.isLt.trans_le (by omega)
  have small : x.val*(2*A.cap)+j.val<(x.val+1)*(2*A.cap) := by rw [Nat.add_mul,Nat.one_mul];omega
  apply lt_trans _ (shape_width (2^k) A.degree (2*A.cap) profile).2.2.1
  exact (small.trans_le (Nat.mul_le_mul_right _ x.isLt)).trans_le (Nat.le_add_left ..)

theorem source_handle_eq (c : ScanColonies he A.stage) (side : Bool) (e : Active A he c side) :
    rawTriple A native S ready names he c side e 0=
      donorAddress A native S ready ⟨e.val,A.quantum_positive _ e.property.1⟩ := by
  let z:=event A he c side e
  unfold rawTriple donorAddress
  change z.1.val*(2*A.cap)+(address A native S ready ((addr c).1,z.1) z.2).val=_
  rw [source_wire A native S ready]
  rfl

theorem source_handle_identifies (q : DescentSharedCableNames.Stage.Positive A) (side : Bool)
    (c : ScanColonies he A.stage) (atRack : (addr c).1=A.pos ((N).src q.val))
    (e : Active A he c side) :
    rawTriple A native S ready names he c side e 0=donorAddress A native S ready q ↔ e.val=q.val := by
  rw [source_handle_eq]
  let epos : DescentSharedCableNames.Stage.Positive A:=⟨e.val,A.quantum_positive _ e.property.1⟩
  constructor
  · intro same_
    let a:=DescentSharedCableNames.Stage.outgoing A native S ready epos
    let b:=DescentSharedCableNames.Stage.outgoing A native S ready q
    let x:=A.block ((N).src e.val)
    let y:=A.block ((N).src q.val)
    change x.val*(2*A.cap)+a.val=y.val*(2*A.cap)+b.val at same_
    have sa : a.val<2*A.cap := a.isLt.trans_le (by omega)
    have sb : b.val<2*A.cap := b.isLt.trans_le (by omega)
    have rad : 0<2*A.cap:=by omega
    have high:=congrArg (·/(2*A.cap)) same_
    have low:=congrArg (·%(2*A.cap)) same_
    change (x.val*(2*A.cap)+a.val)/(2*A.cap)=(y.val*(2*A.cap)+b.val)/(2*A.cap) at high
    rw [Nat.mul_comm x.val, Nat.mul_comm y.val, Nat.mul_add_div rad, Nat.mul_add_div rad, Nat.div_eq_of_lt sa, Nat.div_eq_of_lt sb] at high
    change (x.val*(2*A.cap)+a.val)%(2*A.cap)=(y.val*(2*A.cap)+b.val)%(2*A.cap) at low
    rw [Nat.mul_add_mod_of_lt sa, Nat.mul_add_mod_of_lt sb] at low
    have why : A.pos ((N).src e.val)=A.pos ((N).src q.val) := by
      rw [←source_host A he ((N).src e.val),e.property.2.1,atRack]
    exact congrArg Subtype.val (DescentSharedCableNames.Stage.outgoing_identify_home A native S ready
      (e:=epos) (f:=q) (Prod.ext why (Fin.ext high)) (Fin.ext low))
  · intro h
    exact congrArg (donorAddress A native S ready) (Subtype.ext h)

include coord named fit winner df edgeOrder in
theorem query_iff (q : DescentSharedCableNames.Stage.Positive A) (side : Bool) :
    let u:=(N).src q.val
    (query A.cap profile (panel (A.pos u)) (A.block u) (DescentSharedCableNames.Stage.outgoing A native S ready q).val side).isSome=true ↔
      ∃j : NativePair N W.core home color A.cap,pick (j,if side then 0 else 1)=q.val := by
  intro u
  let c:=home u
  let leafTag:=heap (addr c).2
  let id:=word (s).digit (donorAddress A native S ready q)
  have tag:=winner_leaf A native S ready names win next he fit winner u
  have pos:=source_host A he u
  let x:=inputs s A.cap leafTag (panel (addr c).1) (fun _=>0)
  let tbl:=decodeOutput s (lookupCell s (encodeInput x))
  have eqv := reverse_absent A native S ready names win next he rank coord named fit winner
    (rotor_sorted A rank) (rotor_routes A native S ready rank) df edgeOrder profile c (fun _=>0) side id
  have val_:id.val=donorAddress A native S ready q:=Nat.mod_eq_of_lt (source_bound A native S ready profile q)
  have agree : query A.cap profile (panel (A.pos u)) (A.block u) (DescentSharedCableNames.Stage.outgoing A native S ready q).val side=reverse tbl side id := by
    unfold query
    dsimp only
    rw [tag]
    unfold tbl x
    rw [pos]
    rfl
  rw [agree]
  rw [val_] at eqv
  have characterize : (∃e : Matched T A.cap (thinList home color c) (thickList home color c),
      rawTriple A native S ready names he c side (picked A he c e side) 0=donorAddress A native S ready q) ↔
      ∃j : NativePair N W.core home color A.cap,pick (j,if side then 0 else 1)=q.val := by
    constructor
    · rintro ⟨e,h⟩
      refine ⟨⟨c,e⟩,?_⟩
      exact (picked_old A he c e side).symm.trans
        ((source_handle_identifies A native S ready rank he q side c pos _).mp h)
    · rintro ⟨⟨v,e⟩,h⟩
      have edge_:=picked_old A he v e side
      have at_ : (picked A he v e side).val=q.val:=edge_.trans h
      have source_ : v=c := by simpa only [at_] using (picked A he v e side).property.2.1.symm
      subst v
      exact ⟨e,(source_handle_identifies A native S ready rank he q side c pos _).mpr at_⟩
  exact Option.isSome_iff_ne_none.trans ((not_congr eqv).trans (Classical.not_not.trans characterize))

include coord named fit winner df edgeOrder in
theorem marked_choice_read (q : DescentSharedCableNames.Stage.Positive A) :
    let u:=(N).src q.val
    markedChoice A.cap profile (panel (A.pos u)) (A.block u) (DescentSharedCableNames.Stage.outgoing A native S ready q).val=
      (GadgetNetwork.selected N pick q.val).isSome := by
  intro u
  have hits (side : Bool) :
      (query A.cap profile (panel (A.pos u)) (A.block u)
        (DescentSharedCableNames.Stage.outgoing A native S ready q).val side).isSome = true ↔
        ∃ j : NativePair N W.core home color A.cap, pick (j, if side then 0 else 1) = q.val :=
    query_iff A native S ready rank win he coord named fit winner df edgeOrder profile q side
  have criterion : (GadgetNetwork.selected N pick q.val).isSome=true ↔ ∃j,pick j=q.val := by
    unfold GadgetNetwork.selected
    split
    next h => exact iff_of_true rfl h
    next h => exact iff_of_false Bool.false_ne_true h
  apply Bool.eq_iff_iff.mpr
  rw [markedChoice,Bool.or_eq_true,hits false,hits true,criterion]
  constructor
  · rintro (⟨j,h⟩|⟨j,h⟩)
    · exact ⟨(j,1),h⟩
    · exact ⟨(j,0),h⟩
  · rintro ⟨⟨j,t⟩,h⟩
    fin_cases t
    · exact Or.inr ⟨j,h⟩
    · exact Or.inl ⟨j,h⟩

end Stage
end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
