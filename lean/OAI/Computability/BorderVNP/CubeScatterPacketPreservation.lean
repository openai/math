import OAI.Computability.BorderVNP.CubeScatterPacketReadback

/-! # Retaining already scattered vertices when both endpoint groups share a team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA Physical Physical.Owned Physical.VertexIndex VPVNP.MotifBase VPVNP.BurstRAM DiagonalResidueRAM Tally
open RoutingISA.OwnedVertex (bankAt)

/-- A reserved unused slot has no physical store. Its original word survives the list of opcodes. -/
theorem image_unused {w : ℕ} (ps : List Position) (dst : ℕ) (m : Memory w) (k : Fin ps.length)
    (none : ps[k].value = Option.none) : image ps dst m (dst+k.val) = m (dst+k.val) := by
  induction ps generalizing dst m with
  | nil => exact Fin.elim0 k
  | cons p ps ih =>
    refine Fin.cases ?_ (fun j => ?_) k none
    · intro h
      have e : p.value = Option.none := h
      rw [image,image_outside _ _ _ (Or.inl (by simp)),Position.write,e]
    · intro h
      have preserved := ih (dst+1) (p.write dst m) j h
      have other : p.write dst m (dst+1+j.val) = m (dst+1+j.val) := by
        cases p <;> simp [Position.write,Position.value,Function.update_of_ne (show dst+1+j.val ≠ dst by omega)]
      simpa [image,Nat.add_assoc,Nat.add_comm 1] using preserved.trans other

namespace PacketRowData

variable {n d blocks b h K s w : ℕ} (D : PacketRowData n d blocks b h K s)

private theorem visit_keeps_body (p : Packet n d blocks) (z : State w) (hw : 0 < w)
    (q : BodySlot n b h s) (bit : Bool)
    (ok : (ownedPosition (D.select p) D.axis (ownerBit D.axis p.1.2 D.high) (D.demand p) (D.supply p) q).value ∈
      ([some bit,none] : List (Option Bool)))
    (old : (z.mem (bankAt D.base D.stride p+selectorWidth n K h+(bodyOrder n b h s q).val)).val = bit.toNat) :
    ((D.visit p z).mem (bankAt D.base D.stride p+selectorWidth n K h+(bodyOrder n b h s q).val)).val = bit.toNat := by
  let base := bankAt D.base D.stride p
  let sel := image (selectorPositions (D.select p)) base z.mem
  let j := bodyOrder n b h s q
  have len : (D.body p).length = bodyWidth n b h s := List.length_ofFn
  let k : Fin (D.body p).length := ⟨j.val, by rw [len]; exact j.isLt⟩
  have state : (D.body p)[k].value ∈ ([some bit,none] : List (Option Bool)) := by
    simpa only [body,bodyPositions,List.getElem_ofFn,Fin.getElem_fin,k,j,Fin.eta,Equiv.symm_apply_apply] using ok
  change (image (D.body p) (base+selectorWidth n K h) sel (base+selectorWidth n K h+k.val)).val = bit.toNat
  simp only [List.mem_cons,List.not_mem_nil,or_false] at state
  obtain assigned | skipped := state
  · rw [image_at _ _ _ k assigned]
    exact Nat.mod_eq_of_lt (bit.toNat_le.trans_lt (one_lt_pow₀ (by decide) hw.ne'))
  · rw [image_unused _ _ _ k skipped]
    have pre : (selectorPositions (D.select p)).length = selectorWidth n K h := List.length_ofFn
    have stay := image_outside (selectorPositions (D.select p)) base z.mem (a := base+selectorWidth n K h+k.val)
      (Or.inr (by rw [pre]; omega))
    exact (congrArg Fin.val stay).trans old

/-- Visiting the same packet from either symbol side preserves every previously correct
vertex lookup. Crossing and selector words are shared, and an unused local slot has no store. -/
theorem visit_preserves_vertexAt (p : Packet n d blocks) (v : Vertex (n+1)) (z : State w)
    (hw : 0 < w)
    (old : VertexAt z.mem (bankAt D.base D.stride p) (D.select p) v (D.demand p) (D.supply p)) :
    VertexAt (D.visit p z).mem (bankAt D.base D.stride p) (D.select p) v (D.demand p) (D.supply p) := by
  let base := bankAt D.base D.stride p
  constructor
  · intro j
    have body := image_outside (D.body p) (base+selectorWidth n K h) (image (selectorPositions (D.select p)) base z.mem)
      (a := base+j.val) (Or.inl (Nat.add_lt_add_left j.isLt base))
    exact (congrArg Fin.val body).trans ((selectorImage_stored z.mem base (D.select p) (one_lt_pow₀ (by decide) hw.ne')) j)
  · intro e atV j
    rw [← bodyOrder_end (s := s) e j,← Nat.add_assoc]
    apply D.visit_keeps_body p z hw (.inl (e,j))
    · simp only [ownedPosition]; split_ifs <;> simp [Position.value]
    · rw [Nat.add_assoc,bodyOrder_end]
      exact old.demand e atV j
  · intro e atV j
    let k : Fin (h*s) := ⟨j.val,j.isLt.trans_le (supplyWidth_le (D.select p) e s)⟩
    rw [show j.val = k.val from rfl,← bodyOrder_supply (b := b) e k,← Nat.add_assoc]
    apply D.visit_keeps_body p z hw (.inr (e,k))
    · simp only [ownedPosition,dite_eq_left (show k.val < payload (onEdge s) (D.select p).2 e from j.isLt)]
      split_ifs <;> simp [Position.value,k]
    · rw [Nat.add_assoc,bodyOrder_supply]
      exact old.supply e atV j

/-- Every prefix of a subsequent oriented row preserves a previously correct vertex. -/
theorem before_preserves_vertexAt (p : Packet n d blocks) (v : Vertex (n+1)) (m : Memory w) (hw : 0 < w)
    (stride : bankWidth n b h K s ≤ D.stride)
    (old : VertexAt m (bankAt D.base D.stride p) (D.select p) v (D.demand p) (D.supply p))
    (k : ℕ) (hk : k ≤ packetTrials n d blocks) :
    VertexAt (D.before m k).mem (bankAt D.base D.stride p) (D.select p) v (D.demand p) (D.supply p) := by
  apply D.before_invariant m (fun m => VertexAt m (bankAt D.base D.stride p) (D.select p) v (D.demand p) (D.supply p)) old _ k hk
  intro q _ z previous
  by_cases eq : p = q
  · subst q; exact D.visit_preserves_vertexAt p v z hw previous
  constructor
  · intro j
    have bound : j.val < bankWidth n b h K s := by unfold bankWidth supplyBase; have := j.isLt; omega
    exact (congrArg Fin.val (D.visit_other_bank p q eq z stride ⟨_,bound⟩)).trans (previous.selector j)
  · intro e atV j
    have bound := (demandOffset_range (K := K) e j).2
    have below : demandOffset n b h K e j < bankWidth n b h K s := by unfold bankWidth; omega
    exact (congrArg Fin.val (D.visit_other_bank p q eq z stride ⟨_,below⟩)).trans (previous.demand e atV j)
  · intro e atV j
    exact (congrArg Fin.val (D.visit_other_bank p q eq z stride ⟨_,(supplyOffset_range (b := b) (D.select p) e j).2⟩)).trans
      (previous.supply e atV j)

end PacketRowData
end Cube.Scatter

end BorderVNP
end Computability
end OAI
