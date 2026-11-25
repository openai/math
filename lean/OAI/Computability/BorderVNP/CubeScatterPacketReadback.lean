import OAI.Computability.BorderVNP.CubeISAOwnedRowSelectors

/-! # Reading owned vertex words after the chronological packet-row scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA Physical Physical.Owned Physical.VertexIndex VPVNP.BurstRAM Tally
open RoutingISA.OwnedVertex (bankAt)
open private vertex_iff from OAI.Computability.BorderVNP.CubeISAOwnedVertexModel

namespace PacketRowData

variable {n d blocks b h K s w : ℕ} (D : PacketRowData n d blocks b h K s)

/-- A visited packet changes memory only inside its own complete bank. -/
theorem visit_outside (p : Packet n d blocks) (z : State w) (a : ℕ)
    (away : a < bankAt D.base D.stride p ∨ bankAt D.base D.stride p + bankWidth n b h K s ≤ a) :
    (D.visit p z).mem a = z.mem a := by
  let base := bankAt D.base D.stride p
  have pre : (selectorPositions (D.select p)).length = selectorWidth n K h := List.length_ofFn
  have len : (D.body p).length = bodyWidth n b h s := List.length_ofFn
  have span : selectorWidth n K h+bodyWidth n b h s = bankWidth n b h K s := by
    simp [bodyWidth,bankWidth,supplyBase,Nat.add_assoc]
  change a < base ∨ base+bankWidth n b h K s ≤ a at away
  change image _ (base+selectorWidth n K h) (image _ base z.mem) a = _
  rw [image_outside _ _ _ (by rw [len]; omega)]
  exact image_outside _ _ _ (by rw [pre]; omega)

/-- A lane in a different packet bank survives the entire update. -/
theorem visit_other_bank (p q : Packet n d blocks) (ne : p ≠ q) (z : State w)
    (stride : bankWidth n b h K s ≤ D.stride) (j : Fin (bankWidth n b h K s)) :
    (D.visit q z).mem (bankAt D.base D.stride p+j.val) = z.mem (bankAt D.base D.stride p+j.val) := by
  apply D.visit_outside
  have different : packetIndex p ≠ packetIndex q := fun eq => ne (packetIndex_injective eq)
  rcases lt_or_gt_of_ne different with less | more
  · have st := Nat.mul_le_mul_right D.stride (Nat.succ_le_of_lt less)
    rw [Nat.succ_mul] at st
    exact Or.inl (by unfold bankAt; have := j.isLt; omega)
  · have st := Nat.mul_le_mul_right D.stride (Nat.succ_le_of_lt more)
    rw [Nat.succ_mul] at st
    exact Or.inr (by unfold bankAt; omega)

/-- A predicate preserved by every selected update holds after every prefix of the row. -/
theorem before_invariant (m : Memory w) (P : Memory w → Prop) (initial : P m)
    (keep : ∀ p : Packet n d blocks, p.1.1 D.axis = D.pair → ∀ z : State w,
      P z.mem → P (D.visit p z).mem) (k : ℕ) (hk : k ≤ packetTrials n d blocks) :
    P (D.before m k).mem := by
  induction k with
  | zero => exact initial
  | succ k ih =>
    let t : Fin (packetTrials n d blocks) := ⟨k,hk⟩
    by_cases ok : packetTrialValid t
    · rw [D.before_visit m t ok]
      exact keep _ (packetRowEquiv D.axis D.pair ⟨t,ok⟩).property _ (ih (by omega))
    · rw [D.before_skip m t ok]
      exact ih (by omega)

/-- The bank of a selected packet at the end of its row equals its own chronological update. -/
theorem final_word (m : Memory w) (stride : bankWidth n b h K s ≤ D.stride)
    (p : Packet n d blocks) (row : p.1.1 D.axis = D.pair) (j : Fin (bankWidth n b h K s)) :
    let t := (packetRowEquiv D.axis D.pair).symm ⟨p,row⟩
    let a := bankAt D.base D.stride p+j.val
    (D.before m (packetTrials n d blocks)).mem a = (D.visit p (D.before m t.val.val)).mem a := by
  intro t a
  have he : D.packet t.val t.property = p := congrArg Subtype.val (Equiv.apply_symm_apply ..)
  have done (k : ℕ) (lo : t.val.val+1 ≤ k) (hi : k ≤ packetTrials n d blocks) :
      (D.before m k).mem a = (D.visit p (D.before m t.val.val)).mem a := by
    induction lo with
    | refl => rw [D.before_visit m t.val t.property,he]
    | @step l prev ih =>
      let u : Fin (packetTrials n d blocks) := ⟨l,hi⟩
      by_cases ok : packetTrialValid u
      · rw [D.before_visit m u ok]
        have ne : p ≠ D.packet u ok := by
          intro eq
          have er : packetRowEquiv D.axis D.pair t = packetRowEquiv D.axis D.pair ⟨u,ok⟩ := Subtype.ext (he.trans eq)
          have ev := congrArg (fun k : {t : Fin (packetTrials n d blocks) // packetTrialValid t} => k.val.val)
            ((packetRowEquiv D.axis D.pair).injective er)
          change t.val.val = l at ev
          exact Nat.not_succ_le_self l (ev ▸ prev)
        exact (D.visit_other_bank p _ ne _ stride j).trans (ih (by omega))
      · rw [D.before_skip m u ok]
        exact ih (by omega)
  exact done _ t.val.isLt le_rfl

/-- The full selector, demand, and supply inputs of an owned vertex after the actual row scan. -/
theorem final_vertexAt (m : Memory w) (hw : 0 < w) (stride : bankWidth n b h K s ≤ D.stride)
    (p : Packet n d blocks) (row : p.1.1 D.axis = D.pair) (v : Vertex (n+1))
    (owned : vertexLabel p v D.axis = groupSymbol p D.axis D.high) :
    VertexAt (D.before m (packetTrials n d blocks)).mem (bankAt D.base D.stride p)
      (D.select p) v (D.demand p) (D.supply p) := by
  let t := (packetRowEquiv D.axis D.pair).symm ⟨p,row⟩
  have atVisit := image_vertexAt hw (bankAt D.base D.stride p) (D.before m t.val.val).mem (D.select p)
    D.axis (ownerBit D.axis p.1.2 D.high) v ((vertex_iff ..).mp owned) (D.demand p) (D.supply p)
  change VertexAt (D.visit p (D.before m t.val.val)).mem _ _ _ _ _ at atVisit
  constructor
  · intro j
    have bound : j.val < bankWidth n b h K s := by unfold bankWidth supplyBase; have := j.isLt; omega
    exact (congrArg Fin.val (D.final_word m stride p row ⟨_,bound⟩)).trans (atVisit.selector j)
  · intro e atV j
    have bound := (demandOffset_range (K := K) e j).2
    have below : demandOffset n b h K e j < bankWidth n b h K s := by unfold bankWidth; omega
    exact (congrArg Fin.val (D.final_word m stride p row ⟨_,below⟩)).trans (atVisit.demand e atV j)
  · intro e atV j
    exact (congrArg Fin.val (D.final_word m stride p row ⟨_,(supplyOffset_range (b := b) (D.select p) e j).2⟩)).trans
      (atVisit.supply e atV j)

end PacketRowData
end Cube.Scatter

end BorderVNP
end Computability
end OAI
