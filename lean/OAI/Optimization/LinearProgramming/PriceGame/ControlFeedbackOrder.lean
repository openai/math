import OAI.Optimization.LinearProgramming.PriceGame.ControlData
import OAI.Optimization.LinearProgramming.PriceGame.StatesFeedback

/-! The price controller visits every duplicated coordinate in increasing binary
address order, including the two copies of each active parent. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control

open States States.Mass

private theorem range_pairs (k : ℕ) :
    (List.range k).flatMap (fun j => [2*j, 2*j+1]) = List.range (2*k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    rw [Nat.mul_succ]
    simp [List.range_succ, List.append_assoc]

private theorem addresses_pairs {I : Type} (code : I → ℕ) (pairCode : I × Bool → ℕ)
    (h₀ : ∀ i, pairCode (i,false) = 2 * code i) (h₁ : ∀ i, pairCode (i,true) = 2 * code i + 1)
    (xs : List I) :
    (xs.flatMap (fun i => [(i,false),(i,true)])).map pairCode =
    (xs.map code).flatMap (fun j => [2*j, 2*j+1]) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.map_cons, h₀, h₁, ih]

theorem addresses_allVertices (N l : ℕ) :
    (allVertices N l).map (fun i => (vertexEquivFin N l i).val) = List.range (N*2^l) := by
  induction l with
  | zero =>
    change (List.finRange N).map (fun i => i.val) = _
    simp
  | succ l ih =>
    change (((allVertices N l).flatMap fun i => [(i,false),(i,true)]).map
      (fun i : Vertex N l × Bool => (vertexEquivFin N (l+1) i).val)) = _
    let addr := fun j : Vertex N l => (vertexEquivFin N l j).val
    let pairAddr := fun j : Vertex N l × Bool => (vertexEquivFin N (l+1) j).val
    have h₀ (i : Vertex N l) : pairAddr (i,false) = 2 * addr i := by
      change 0 + 2*addr i = _; omega
    have h₁ (i : Vertex N l) : pairAddr (i,true) = 2 * addr i + 1 := by
      change 1 + 2*addr i = _; omega
    apply (addresses_pairs addr pairAddr h₀ h₁ (allVertices N l)).trans
    change ((allVertices N l).map (fun i => (vertexEquivFin N l i).val)).flatMap _ = _
    rw [ih, range_pairs, pow_succ]
    congr 1
    ac_rfl

theorem allVertices_eq_order (N l : ℕ) :
    allVertices N l = List.ofFn (vertexEquivFin N l).symm := by
  apply (List.map_injective_iff (f:=fun i : Vertex N l => (vertexEquivFin N l i).val)).mpr
    (fun i j he => (vertexEquivFin N l).injective (Fin.ext he))
  rw [addresses_allVertices]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [List.getElem_range]

private theorem lookup_at {I : Type} [DecidableEq I] (xs : List I) (ys : List Bool)
    (hx : xs.Nodup) (hy : ys.length = xs.length) (j : ℕ) (hj : j < xs.length) :
    lookupFeedback xs ys xs[j] = ys[j]'(hy ▸ hj) := by
  induction xs generalizing ys j with
  | nil => simp at hj
  | cons x xs ih =>
    cases ys with
    | nil => simp at hy
    | cons y ys =>
      have he := List.nodup_cons.mp hx
      cases j with
      | zero => simp [lookupFeedback]
      | succ j =>
        have hj' : j < xs.length := by simpa using hj
        have hdiff : xs[j] ≠ x := fun e => he.1 (e ▸ List.getElem_mem hj')
        simpa [lookupFeedback, hdiff] using ih ys he.2 (by simpa using hy) j hj'

theorem packFeedback_order (N l : ℕ) (ys : List Bool)
    (hy : ys.length = (allVertices N l).length) :
    packTable N l (lookupFeedback (allVertices N l) ys) = ys := by
  have hn : (allVertices N l).Nodup := by
    rw [allVertices_eq_order]
    exact List.nodup_ofFn_ofInjective (vertexEquivFin N l).symm.injective
  apply List.ext_getElem
  · rw [length_packTable, hy, length_allVertices, card_vertices]
    ac_rfl
  · intro j hj hys
    have hj' : j < (allVertices N l).length := hy ▸ hys
    have hl := lookup_at (allVertices N l) ys hn hy j hj'
    have hv : (allVertices N l)[j] = (vertexEquivFin N l).symm
        ⟨j, by simpa only [length_packTable] using hj⟩ := by
      simp [allVertices_eq_order]
    simpa only [packTable, List.getElem_ofFn, hv] using hl

end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
