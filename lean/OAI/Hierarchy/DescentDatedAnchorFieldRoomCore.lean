import OAI.Hierarchy.DescentDatedMatcherPageIndex

namespace OAI
/-! # Bounds on the outgoing ordinal and role published by a genuine matcher page -/
namespace Hierarchy.DescentDatedOperandPages
open DescentSIMDLookup DescentRawCablePanel.DepotRAM DescentOperandPriorIncidence
open DescentPacking.PackedMatch.Local
open scoped Classical Fin.CommRing
noncomputable section

private theorem cast_le (n b : ℕ) : (n:Cell b).val≤n := Nat.mod_le _ _

private theorem old_column (cap : ℕ) (live : 0<cap) (v : ℕ×ℕ) :
    Stage.anchorColumns cap v 1≤2*cap := by
  change 1+v.1%(2*cap)≤2*cap
  have h:=Nat.mod_lt v.1 (show 0<2*cap by omega)
  omega

theorem retarget_role {n : ℕ} (r : Fin n→Fin 12→ℕ) (side : Bool) (key : ℕ) :
    (Stage.retarget r side key).2≤2 := by
  cases side with
  | false => change 0≤2; decide
  | true =>
    cases h : Stage.matchingRow r true key <;> cases h' : Stage.matchingRow r false key <;>
      simp [Stage.retarget,Stage.selectedAnchor,h,h',Option.orElse]

private theorem field_room (f : Shape) (profile b : ℕ) (x : Fin f.blocks) (old : Fin f.cap)
    (data : Cell (totalBits f)) (key : Cell (originBits f)) :
    (TerrainAnchor.field f profile b x 1 data key).val≤2*f.cap ∧
      (TerrainAnchor.field f profile b x 2 data key).val≤2 := by
  by_cases zero : key.val=0
  · simp [TerrainAnchor.field,zero]
  · simp only [TerrainAnchor.field,ite_eq_right zero]
    exact ⟨(cast_le _ _).trans (old_column f.cap (by have h:=old.isLt;omega) _),
      (cast_le _ _).trans (retarget_role _ _ _)⟩

private theorem sibling_room (f : Shape) (profile b : ℕ) (x : Fin f.blocks) (old : Fin f.cap)
    (data : Cell (totalBits f)) :
    (TerrainAnchor.siblingField f profile b x old 1 data).val≤2*f.cap ∧
      (TerrainAnchor.siblingField f profile b x old 2 data).val≤2 := by
  cases found : TerrainAnchor.sibling (TerrainAnchor.records f profile x (separate f data))
      (x.val*(2*f.cap)+old.val) with
  | none => simp [TerrainAnchor.siblingField,found]
  | some second =>
    simp only [TerrainAnchor.siblingField,found,Option.elim_some]
    exact ⟨(cast_le _ _).trans (old_column f.cap (by have h:=old.isLt;omega) (second,0)),
      (cast_le (Stage.anchorColumns f.cap (second,0) 2) b).trans (by change 0≤2; decide)⟩

theorem anchor_room (f : Shape) (profile b : ℕ) (x : Fin f.blocks) (old : Fin f.cap)
    (side : Fin 2) (data : Cell (totalBits f)) :
    (law f profile b (anchor f x old side 1).val data).val≤2*f.cap ∧
      (law f profile b (anchor f x old side 2).val data).val<11 := by
  simp only [anchor_value_data]
  obtain ⟨hx,hy⟩:=field_room f profile b x old data (TerrainAnchor.ticket f old (decide (side.val=1)))
  exact ⟨hx,hy.trans_lt (by decide)⟩

theorem sibling_law_room (f : Shape) (profile b : ℕ) (x : Fin f.blocks) (old : Fin f.cap)
    (data : Cell (totalBits f)) :
    (law f profile b (sibling f x old 1).val data).val≤2*f.cap ∧
      (law f profile b (sibling f x old 2).val data).val<11 := by
  simp only [sibling_value_data]
  obtain ⟨hx,hy⟩:=sibling_room f profile b x old data
  exact ⟨hx,hy.trans_lt (by decide)⟩


/-- The physical decoder's old ordinal and role are bounded on every public
path and seat, including both retarget choices and the sibling page. -/
theorem matcher_index_room (fmt : Shape) (paths profile b : ℕ)
    (i : Fin (paths*(fmt.blocks*(fmt.cap*3)))) (source : Cell (totalBits fmt)) :
    (law fmt profile b (matcherIndex fmt paths i 1).2.val source).val≤2*fmt.cap ∧
      (law fmt profile b (matcherIndex fmt paths i 2).2.val source).val<11 := by
  obtain ⟨⟨path,rest⟩,rfl⟩:=finProdFinEquiv.surjective i
  obtain ⟨⟨x,slot⟩,rfl⟩:=finProdFinEquiv.surjective rest
  obtain ⟨⟨old,mode⟩,rfl⟩:=finProdFinEquiv.surjective slot
  by_cases live : mode.val<2
  · simpa only [matcherIndex,Equiv.symm_apply_apply,dite_eq_left live] using
      anchor_room fmt profile b x old ⟨mode.val,live⟩ source
  · simpa only [matcherIndex,Equiv.symm_apply_apply,dite_eq_right live] using
      sibling_law_room fmt profile b x old source


end
end Hierarchy.DescentDatedOperandPages

end OAI
