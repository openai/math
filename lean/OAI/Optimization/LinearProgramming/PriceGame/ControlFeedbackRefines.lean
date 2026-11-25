import OAI.Optimization.LinearProgramming.PriceGame.ControlBoundedFeedback
import OAI.Optimization.LinearProgramming.PriceGame.ControlCollapseRefines
import OAI.Optimization.LinearProgramming.PriceGame.ControlFeedbackOrder

/-! Correctness of the physical feedback scan for all chronological replies. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open States States.Mass

private theorem get_pack {N l : ℕ} (x : Vertex N l → ℚ) (j : Vertex N l) :
    ((packTable N l x).drop (vertexEquivFin N l j).val).headD 0 = x j := by
  rw [drop_head_eq]
  exact lookupTable_pack N l x j

theorem medianRow_pack {N l : ℕ} (y : Vertex N l → ℚ) (x : Vertex N (l+1) → ℚ) :
    medianRow (packTable N l y) (packTable N (l+1) x) = packTable N l (parentPrices y x) := by
  apply List.ext_getElem
  · simp [medianRow,liftRow]
  · intro i hi hj
    have hlt : i < N*2^l := by simpa only [length_packTable] using hj
    let v : Vertex N l := (vertexEquivFin N l).symm ⟨i,hlt⟩
    have hv : (vertexEquivFin N l v).val = i := congrArg Fin.val ((vertexEquivFin N l).apply_symm_apply _)
    have hL : (vertexEquivFin N (l+1) (v,false)).val = 2*i := by rw [childAddress,hv]; simp
    have hR : (vertexEquivFin N (l+1) (v,true)).val = 2*i+1 := by rw [childAddress,hv]; simp [Nat.add_comm]
    have leftEq := get_pack x (v,false)
    have rightEq := get_pack x (v,true)
    have baseEq := get_pack y v
    rw [hL] at leftEq
    rw [hR] at rightEq
    rw [hv] at baseEq
    simp only [medianRow,liftRow,List.getElem_map,List.getElem_range,liftCell,length_packTable]
    have ne : i ≠ 2*(N*2^l)/2 := by omega
    simp only [ne,ite_false]
    rw [baseEq,leftEq,rightEq]
    simpa only [packTable,List.getElem_ofFn] using (show median₃ (y v) (x (v,false)) (x (v,true)) =
      parentPrices y x v from rfl)

private theorem numericItem_refines {N l : ℕ} (h : History N)
    (y : Vertex N l → ℚ) (x : Vertex N (l+1) → ℚ) (i : Vertex N l) :
    numericItem (packHistory l h,packTable N l y,packTable N l (parentPrices y x))
      (vertexEquivFin N l i).val =
      feedbackItem N l (packHistory l h) (packTable N l y) (packTable N (l+1) x) i := by
  have hy : lookupTable N l (packTable N l y) = y := funext fun _ => lookupTable_pack ..
  have hx : lookupTable N (l+1) (packTable N (l+1) x) = x := funext fun _ => lookupTable_pack ..
  have prodEq := (collapse_refines N l h (parentPrices y x) i).trans
    (rootQueryRows_refines N l (packHistory l h) (parentPrices y x) i).symm
  simp only [numericItem,feedbackItem,hy,hx,get_pack]
  split_ifs
  · rfl
  · rfl
  · exact congrArg FeedbackItem.request prodEq

private theorem numericItems_refines {N l : ℕ} (h : History N)
    (y : Vertex N l → ℚ) (x : Vertex N (l+1) → ℚ) (bs : List Bool) :
    numericItems (packHistory l h,packTable N l y,packTable N (l+1) x,bs) =
      (allVertices N l).map (feedbackItem N l (packHistory l h) (packTable N l y)
        (packTable N (l+1) x)) := by
  simp only [numericItems,medianRow_pack,length_packTable]
  rw [← addresses_allVertices, List.map_map]
  apply List.map_congr_left
  intro i _
  exact numericItem_refines h y x i

private theorem consume_count (xs : List FeedbackItem) (bs ys rest : List Bool)
    (h : consumeItems xs bs = .inl (ys,rest)) : ys.length = xs.length := by
  induction xs generalizing bs ys rest with
  | nil => cases h; rfl
  | cons i xs ih =>
    simp only [consumeItems] at h
    cases ht : takeFeedback i bs with
    | inr => simp [ht] at h
    | inl v =>
      rcases v with ⟨b,tail⟩
      cases hr : consumeItems xs tail with
      | inr => simp [ht,hr] at h
      | inl out =>
        rcases out with ⟨ys',rs⟩
        simp [ht,hr] at h
        obtain ⟨rfl,rfl⟩ := h
        exact congrArg Nat.succ (ih _ _ _ hr)

/-- Every complete feedback row and every interrupted prefix agrees with the source. -/
theorem boundedFeedback_refines {N l : ℕ} (h : History N)
    (y : Vertex N l → ℚ) (x : Vertex N (l+1) → ℚ) (bs : List Bool) :
    boundedFeedback (packHistory l h,packTable N l y,packTable N (l+1) x,bs) =
      feedbackPrefix N l (packHistory l h) (packTable N l y) (packTable N (l+1) x) bs := by
  simp only [boundedFeedback,numericItems_refines,feedbackPrefix]
  generalize hi : (allVertices N l).map (feedbackItem N l (packHistory l h) (packTable N l y)
    (packTable N (l+1) x)) = items
  cases hc : consumeItems items bs with
  | inr q => rfl
  | inl out =>
    rcases out with ⟨v,remaining⟩
    have hv : v.length = (allVertices N l).length := by
      rw [consume_count items bs v remaining hc,← hi,List.length_map]
    simp only [Sum.map_inl,packFeedback_order N l v hv]

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
