import OAI.Computability.BorderVNP.CubeScatterSingletonRun
import OAI.Computability.BorderVNP.CubeISAOwnedScatterRealization

/-! # The actual per-packet words shared by both incident groups

Private demand ends and within-group edges never enter the crossing suffix.
Changing the owned side, or its private bits, leaves the crossing stream
identical in every position. Prefix slices therefore feed each physical cursor
from one common ordered label-pair list.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA VPVNP.BurstRAM VPVNP.MotifBase DiagonalResidueRAM Tally

variable {n b h K s w : ℕ}

/-- Little-endian selector digits physically copied from a label-pair prefix. -/
def selectorStream (u : Selector n K h) : List Bool :=
  List.ofFn fun j : Fin (selectorWidth n K h) =>
    VPVNP.RAMSerialization.wordBits _ ⟨(selectorOrder n K h u).val,
      (selectorOrder n K h u).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩ j

/-- The two routed streams consumed by the actual selector-prefix copy. -/
theorem selector_streams (u : Selector n K h) :
    (selectorPositions u).filterMap Position.selectorBit = selectorStream u ∧
      (selectorPositions u).filterMap Position.crossBit = [] := by
  have eq : selectorPositions u = (selectorStream u).map Position.selector := by
    simp [selectorStream,selectorPositions,Function.comp_def]
  rw [eq]
  generalize selectorStream u = xs
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons b xs ih => simp [List.filterMap_cons,Position.selectorBit,Position.crossBit,ih]

/-- The prefix has the fixed native selector width. -/
theorem selectorStream_length (u : Selector n K h) : (selectorStream u).length = selectorWidth n K h :=
  List.length_ofFn

/-- Actual packet crossing bits in the common bank order of its two owned views. -/
def crossingStream (b : ℕ) (u : Selector n K h) (i : Fin (n+1))
    (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) : List Bool :=
  (bodyPositions (b := b) u i false (fun _ _ => false) z).filterMap Position.crossBit

/-- The copied crossing positions have the same bits in the same order for either owner. -/
theorem body_cross_stream (u : Selector n K h) (i : Fin (n+1)) (bit : Bool)
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) :
    (bodyPositions u i bit x z).filterMap Position.crossBit = crossingStream b u i z := by
  let slots := List.ofFn fun k => (bodyOrder n b h s).symm k
  have fmt (bit : Bool) (x : Ends n → Fin (h*b) → Bool) :
      bodyPositions u i bit x z = slots.map (ownedPosition u i bit x z) := by
    simp [slots,bodyPositions,Function.comp_def]
  rw [crossingStream,fmt,fmt,List.filterMap_map,List.filterMap_map]
  apply List.filterMap_congr
  intro p _
  cases p with
  | inl q => rcases q with ⟨e,j⟩; simp only [Function.comp_def,ownedPosition]; split_ifs <;> rfl
  | inr q => rcases q with ⟨e,j⟩; simp only [Function.comp_def,ownedPosition]; split_ifs <;> rfl

/-- The crossing words in the physical pair bank have exactly the packet's declared directional length. -/
theorem crossingStream_length (b : ℕ) (u : Selector n K h) (i : Fin (n+1))
    (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) :
    (crossingStream b u i z).length = ∑ v : Vertex (n+1), payload (onEdge s) u.2 (v,i) :=
  body_cross_length ..

/-- A contiguous sublist of a delivered stream is available at its actual pointer plus the prefix length. -/
theorem BitsAt.slice {m : Memory w} {base : ℕ} (pre own post : List Bool)
    (h : BitsAt m base (pre++own++post)) : BitsAt m (base+pre.length) own := by
  intro k
  let j : Fin (pre++own++post).length := ⟨pre.length+k.val,by simp; omega⟩
  have eq := h j
  simp only [Fin.getElem_fin] at eq ⊢
  dsimp only [j] at eq
  have left : pre.length+k.val < (pre++own).length := by simp
  simpa only [Nat.add_assoc,List.getElem_append_left left,List.getElem_append_right (Nat.le_add_right ..),
    Nat.add_sub_cancel_left] using eq

/-- A complete routed stream simultaneously supplies each bit in every constituent interval. -/
theorem BitsAt.append {m : Memory w} {base : ℕ} {xs ys : List Bool}
    (hx : BitsAt m base xs) (hy : BitsAt m (base+xs.length) ys) : BitsAt m base (xs++ys) := by
  intro k
  simp only [Fin.getElem_fin]
  by_cases hk : k.val < xs.length
  · rw [List.getElem_append_left hk]
    exact hx ⟨k.val,hk⟩
  · have hi : k.val-xs.length < ys.length := by have := k.isLt; simp at this; omega
    rw [List.getElem_append_right (Nat.le_of_not_gt hk)]
    have eq := hy ⟨k.val-xs.length,hi⟩
    simpa only [Fin.getElem_fin,Nat.add_assoc,Nat.add_sub_of_le (Nat.le_of_not_gt hk)] using eq

end Cube.Scatter

end BorderVNP
end Computability
end OAI
