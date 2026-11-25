import OAI.Hierarchy.DescentOrdinaryOriginMask
import OAI.Hierarchy.DescentOrdinaryRoleControlFields

namespace OAI
/-! Counting the one-based origins already written by the ordinary operand pass. -/
namespace Hierarchy.DescentOrdinaryOriginMask
open DescentSIMDLookup DescentPackedLocalAtoms DescentPhysicalOrder
open DescentOrdinaryAtomFieldRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {X : Type} [Fintype X] {N K b : ℕ} (ids : X ↪ Fin N) (bits : Cell (1*N))
    (cover : ∀j, (encode 1 N).symm bits j≠0 ↔ ∃x,ids x=j)

section
include cover

theorem earlier_index (x : X) :
    earlier ((encode 1 N).symm bits) (ids x)=(physical (ids.trans Fin.valEmbedding) x).val :=by
  have image : (present ((encode 1 N).symm bits)).filter (·< ids x)=
      (Finset.univ.filter (fun y=>ids y< ids x)).map ids :=by
    ext j
    simp only [present,Finset.mem_filter,Finset.mem_univ,true_and,cover,Finset.mem_map]
    constructor
    · rintro ⟨⟨v,rfl⟩,lt⟩;exact ⟨v,lt,rfl⟩
    · rintro ⟨v,lt,rfl⟩;exact ⟨⟨v,rfl⟩,lt⟩
  rw [earlier,image,Finset.card_map,physical_val]
  rfl

/-- Padding reads zero; every actual node reads its one-based original donor or birth slot. -/
theorem population_iff (fits : N<2^b) (n : Fin K) :
    ((encode b K).symm (selection N K b bits) n≠0) ↔ n.val<Fintype.card X :=by
  by_cases live : n.val<Fintype.card X
  · let rank:=physical (ids.trans Fin.valEmbedding)
    let x:=rank.symm ⟨n.val,live⟩
    have ord : earlier ((encode 1 N).symm bits) (ids x)=n.val :=
      (earlier_index ids bits cover x).trans (congrArg Fin.val (rank.apply_symm_apply _))
    have val_:=stamp_at N K b bits n (ids x) ((cover _).2 ⟨_,rfl⟩) ord fits
    exact ⟨fun _=>live,fun _ eqn=>by rw [eqn] at val_; change 0=_ at val_; omega⟩
  · have absent : ¬∃j,(encode 1 N).symm bits j≠0 ∧ earlier ((encode 1 N).symm bits) j=n.val :=by
      rintro ⟨j,hj,rank⟩
      obtain ⟨x,rfl⟩:=(cover j).1 hj
      have equal := (earlier_index ids bits cover x).symm.trans rank
      exact live (equal ▸ (physical (ids.trans Fin.valEmbedding) x).isLt)
    simp [selection,selected_none N K b bits n absent,live]

/-- The native counting LUT reads the saved origins of *all* nodes, including nullary and unpaid nodes. -/
theorem population_count (size : Fintype.card X≤K) (fits : N<2^b)
    {d : ℕ} (room : K<2^d) :
    (RoleCounts.count (a:=b) (K:=K) d (selection N K b bits)).val=Fintype.card X :=by
  let ranks: X ↪ Fin K := (physical (ids.trans Fin.valEmbedding)).toEmbedding.trans (Fin.castLEEmb size)
  apply RoleCounts.exact_count (a:=b) ranks (selection N K b bits)
  · intro j
    rw [population_iff ids bits cover fits]
    constructor
    · intro hj
      exact ⟨(physical (ids.trans Fin.valEmbedding)).symm ⟨j.val,hj⟩,Fin.ext (by simp [ranks])⟩
    · rintro ⟨x,rfl⟩;exact (physical (ids.trans Fin.valEmbedding) x).isLt
  · exact room

end

/-- A vacant destination has no positive actor stamp, for any old donor counts. -/
theorem vacant {D old cap a mb K' b : ℕ} (wanted : Cell a)
    (address : Fin (DescentPackedActorMask.actors D cap)→Cell a) (counts : Fin D→Cell mb)
    (miss : ∀j,address j≠wanted) :
    selection (DescentPackedActorMask.nodes D old cap) K' b
      (DescentPackedActorMask.occupied D old cap mb (DescentPackedActorMask.target a _ wanted (encode a _ address))
         (encode mb D counts))=0 :=by
  have flags : DescentPackedActorMask.target a _ wanted (encode a _ address)=encode 1 _ (fun _=>0) :=by
    unfold DescentPackedActorMask.target
    simp [miss]
  have none_ : DescentPackedActorMask.occupied D old cap mb (encode 1 _ (fun _=>0))
      (encode mb D counts)=encode 1 _ (fun _=>0) :=by
    unfold DescentPackedActorMask.occupied
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    congr 1
    funext j
    obtain ⟨⟨d,i⟩,rfl⟩:=finProdFinEquiv.surjective j
    obtain ⟨s,rfl⟩:=finSumFinEquiv.surjective i
    cases s <;> simp [DescentPackedActorMask.bitAt]
  rw [flags,none_]
  have z : encode 1 (DescentPackedActorMask.nodes D old cap) (fun _=>0)=0 :=by
    apply Fin.ext
    change (finFunctionFinEquiv (fun _=>(0 : Cell 1))).val=0
    simp []
  rw [z]
  exact dead _ _ _ 0


end
end Hierarchy.DescentOrdinaryOriginMask

end OAI
