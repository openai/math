import OAI.Hierarchy.DescentPackedFlowStage
import OAI.Hierarchy.DescentMeasuredPortTapes
import OAI.Hierarchy.DescentIssuedNativeReset

namespace OAI
/-! # The previous signed flow columns and the numbered reset header have the same physical socket order -/
namespace Hierarchy.DescentSixParty.PackedFlow
open DescentColonies DescentPackedExchange DescentMeasuredWeights DescentGL
open scoped Classical
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k m H : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W G q ε J V k) (name : V≃Fin H)

omit [Fintype V] [DecidableEq V] in
theorem numbered_rank (ns : Finset V) (v : ↥ns) :
    ((neighborOrder name ns) v).val=(ns.filter (fun x=>name x<name v.val)).card := by
  let l:=ns.map name.toEmbedding
  have size:l.card=Fintype.card ns:=by simp [l]
  let ix:=(l.orderIsoOfFin size).symm
  let lift (a:ns):↥l:=⟨name a.val,Finset.mem_map.mpr ⟨a.val,a.property,rfl⟩⟩
  change (ix (lift v)).val=_
  rw [←Fin.card_Iio (ix (lift v))]
  symm
  apply Finset.card_bij (fun e he=>ix (lift ⟨e,(Finset.mem_filter.mp he).1⟩))
  · intro e he;exact Finset.mem_Iio.mpr (ix.strictMono (Finset.mem_filter.mp he).2)
  · intro x _ y _ eqn;exact name.injective (congrArg Subtype.val (ix.injective eqn))
  · intro j hj
    let z:=ix.symm j
    obtain ⟨e,he,eqn⟩:=Finset.mem_map.mp z.property
    have zeq : lift ⟨e,he⟩=z:=Subtype.ext eqn
    have first : name e<name v.val := by
      change lift ⟨e,he⟩<lift v
      rw [zeq,←ix.lt_iff_lt,ix.apply_symm_apply]
      exact Finset.mem_Iio.mp hj
    exact ⟨e,Finset.mem_filter.mpr ⟨he,first⟩,by rw [zeq,ix.apply_symm_apply]⟩

theorem mutual_near : A.mutual=A.near := by
  funext v;ext u
  simp only [GroupStage.mutual,Finset.mem_filter]
  exact ⟨And.left,fun h=>⟨h,(A.symmetric v u).mp h⟩⟩

theorem socket_val (v : V) (u : ↥(A.near v)) :
    (socket A (name.toEmbedding.trans Fin.valEmbedding) v u).val=((neighborOrder name (A.near v)) u).val := by
  rw [socket,DescentPacking.PackedMatch.Local.Stage.nb_val,numbered_rank]
  rfl

theorem next_numbered (v : Fin H) (s : Fin A.degree) :
    next A name v s=neighborSlot name A.mutual (v,s) := by
  rw [mutual_near A]
  let h := name.symm v
  let place := socket A (name.toEmbedding.trans Fin.valEmbedding) h
  change (if hit : ∃a,place a=s then some (name hit.choose.val) else none)=
    (if hi : s.val<Fintype.card (A.near h) then
      some (name (((neighborOrder name (A.near h)).symm ⟨s.val,hi⟩).val)) else none)
  by_cases hi : s.val<Fintype.card (A.near h)
  · let u : ↥(A.near h) := (neighborOrder name (A.near h)).symm ⟨s.val,hi⟩
    have atSlot : place u=s := Fin.ext ((socket_val A name h u).trans
      (congrArg Fin.val ((neighborOrder name (A.near h)).apply_symm_apply _)))
    have hit : ∃a,place a=s := ⟨u,atSlot⟩
    rw [dite_eq_left hit,dite_eq_left hi]
    exact congrArg (fun a : ↥(A.near h) => some (name a.val))
      (place.injective (hit.choose_spec.trans atSlot.symm))
  · have miss : ¬∃a,place a=s := by
      rintro ⟨a,atSlot⟩
      apply hi
      rw [←atSlot]
      exact (socket_val A name h a).trans_lt ((neighborOrder name (A.near h)) a).isLt
    rw [dite_eq_right miss,dite_eq_right hi]

theorem raw_contact (digits : Block m≃J×Block k) (bound : ∀v,(A.mutual v).card≤A.degree)
    (c : Contacts A.mutual) (x : Block m) :
    raw A name digits ((atPort name A.mutual bound c).2) ((atPort name A.mutual bound c).1) x=
      A.resetFlow digits c.1 c.2.val x := by
  have seen:=atPort_read name A.mutual bound c
  rw [raw,next_numbered,Prod.mk.eta,seen]
  change A.resetFlow digits (name.symm (name c.1)) (name.symm (name c.2.val)) x = _
  simp only [Equiv.symm_apply_apply]

end
end Hierarchy.DescentSixParty.PackedFlow

end OAI
