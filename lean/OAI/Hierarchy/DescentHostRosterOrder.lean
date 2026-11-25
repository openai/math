import OAI.Hierarchy.DescentSharedCableSerial
import OAI.Hierarchy.DescentGroupStageData

namespace OAI
/-! # Distinct-neighbor ordinals and their fixed-capacity host table -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSharedCableNames
open scoped Classical
noncomputable section
theorem nb_val {X : Type} [DecidableEq X] {D : ℕ} (f : X→Finset X) (n : X↪ℕ) (room : ∀h,(f h).card≤D)
    (h : X) (v : ↥(f h)) : (Ends.neighborOrder f n room h v).val=((f h).filter (fun x=>n x<n v.val)).card := by
  let l := (f h).map n
  let ix := (l.orderIsoOfFin rfl).symm
  let lift (j : ↥(f h)) : ↥l := ⟨n j.val,Finset.mem_map.mpr ⟨j.val,j.property,rfl⟩⟩
  change (ix (lift v)).val=_
  rw [←Fin.card_Iio (ix (lift v))]
  symm
  apply Finset.card_bij (fun e he=>ix (lift ⟨e,(Finset.mem_filter.mp he).1⟩))
  · intro e he;exact Finset.mem_Iio.mpr (ix.strictMono (Finset.mem_filter.mp he).2)
  · intro x _ y _ same;exact n.injective (congrArg Subtype.val (ix.injective same))
  · intro j hj
    let z:=ix.symm j
    obtain ⟨e,mem,eqn⟩ := Finset.mem_map.mp z.property
    have zEq : lift ⟨e,mem⟩=z := Subtype.ext eqn
    have before : n e<n v.val := by
      change lift ⟨e,mem⟩<lift v
      rw [zEq,←ix.lt_iff_lt,ix.apply_symm_apply]
      exact Finset.mem_Iio.mp hj
    exact ⟨e,Finset.mem_filter.mpr ⟨mem,before⟩,by rw [zEq,ix.apply_symm_apply]⟩

variable {V : Type} [Fintype V] [DecidableEq V] {H D : ℕ}

def hostRotor (host : V ↪ Fin H) (near : V→Fin D→Option V) (h : Fin H) (j : Fin D) : Option (Fin H) :=
  if live : ∃v,host v=h then (near live.choose j).map host else none

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

namespace Hierarchy.DescentGroupPeerOrder
open DescentSixParty DescentSharedCableNames DescentPacking.PackedMatch.Local.Stage
open scoped Classical
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
variable (A : GroupStage W G q ε J V k) (vertex : V↪ℕ)

def hostSlot (v : V) := Ends.neighborOrder A.near vertex A.degreeBound v
def hostRoster (v : V) (s : Fin A.degree) : Option V :=
  if active : ∃u,hostSlot A vertex v u=s then some active.choose.val else none

theorem at_host (v : V) (u : ↥(A.near v)) : hostRoster A vertex v (hostSlot A vertex v u)=some u.val := by
  let embed:=hostSlot A vertex v
  have hit : ∃w,embed w=embed u:=⟨u,rfl⟩
  unfold hostRoster
  rw [dite_eq_left hit,embed.injective hit.choose_spec]

theorem hostRoster_mem (v u : V) : u∈A.near v ↔ ∃j,hostRoster A vertex v j=some u := by
  constructor
  · intro h
    exact ⟨_,at_host A vertex v ⟨u,h⟩⟩
  · rintro ⟨j,h⟩
    unfold hostRoster at h
    split at h
    · rename_i live
      exact (Option.some.inj h) ▸ live.choose.property
    · contradiction

theorem hostSlot_val (v : V) (u : ↥(A.near v)) :
    (hostSlot A vertex v u).val=((A.near v).filter (fun t=>vertex t<vertex u.val)).card :=
  nb_val A.near vertex A.degreeBound v u

end
end Hierarchy.DescentGroupPeerOrder

end OAI
