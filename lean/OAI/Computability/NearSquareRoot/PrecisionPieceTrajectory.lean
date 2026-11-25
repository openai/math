import OAI.Computability.NearSquareRoot.PrecisionLayers
import OAI.Computability.NearSquareRoot.PhysicalWalshPieceExecution
import OAI.Computability.NearSquareRoot.PhysicalWalshPieceIdeal
import OAI.Computability.NearSquareRoot.PrecisionNodeChild

/-! # Rounding along the generated list of even Walsh pieces

The numerical trajectory here is the same trajectory used by the physical
sweep. The prefix bound supplies each invocation's range hypothesis at its
actual rounded input and hence proves every reached representation guard.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication KernelPass PhysicalWalshNode FlatWalshNode

noncomputable section

def decoded {w : ℕ} (p : ℕ) (x : ℕ → Dusk.Grain w) : IdealRow := fun n => Grid.meaning p w (x n)

private def resizeIso (A N : ℕ) (s : Shape) (hc : count A s = N) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N) := hc ▸ nodeIsometry A s

private theorem resize_at (A N : ℕ) (s : Shape) (hc : count A s = N) (x : IdealRow) :
    resizeIso A N s hc (atWidth N x) = atWidth N (idealRow A s x) := by
  subst N
  exact (idealRow_isometry A s x).symm

private theorem gap_transport {A p N w : ℕ} (s : Shape) (hw : s.w = w) (hn : count A s = N)
    (x : ℕ → Dusk.Grain w) (z : Data s) :
    ‖atWidth N (decoded p (castRow hw z)) -
        atWidth N (idealRow A s (decoded p x))‖ =
      ‖nodeValues A p s z - nodeTarget A p s (castRow hw.symm x)‖ := by
  subst w N
  rfl

private theorem initial_transport {A p N w : ℕ} (s : Shape) (hw : s.w = w) (hn : count A s = N)
    (x : ℕ → Dusk.Grain w) :
    ‖atWidth N (decoded p x)‖ = ‖nodeValues A p s (castRow hw.symm x)‖ := by
  subst w N
  rfl

/-- Total rounded error and reachability of every scheduled piece, starting
with the represented padded stream in its original ordinal order. -/
theorem trajectory_bound {a W : ℕ} (ha : 1 < a+1) (hw : 0 < W) (plan : Plan (a+1) W W)
    (b : Root) (p : ℕ) {δ R : ℝ} (hd : 0 ≤ δ)
    (hR : ‖atWidth (b.size (a:=a) (W:=W)) (decoded p b.row)‖ +
      (b.pieces (a:=a) hw).length*δ ≤ R)
    (localStep : ∀ j : Fin (b.pieces (a:=a) hw).length,
      let u := (b.pieces hw).get j
      let x := b.reached hw plan ha j
      ‖nodeValues (a+1) p u x‖ ≤ R →
        Good hw plan u x ∧ ‖nodeValues (a+1) p u (run hw plan u x) - nodeTarget (a+1) p u x‖ ≤ δ) :
    b.Feasible hw plan ha ∧
      ‖atWidth (b.size (a:=a) (W:=W)) (activeRow (2*(b.s/2)) (2^(b.s%2)) (decoded p b.row))‖ =
        ‖atWidth (b.size (a:=a) (W:=W)) (decoded p b.row)‖ ∧
      ‖atWidth (b.size (a:=a) (W:=W)) (decoded p (b.stage hw plan (b.pieces (a:=a) hw).length)) -
        atWidth (b.size (a:=a) (W:=W)) (activeRow (2*(b.s/2)) (2^(b.s%2)) (decoded p b.row))‖ ≤
        (b.pieces (a:=a) hw).length*δ := by
  let A := a+1
  let N := b.size (a:=a) (W:=W)
  let l := b.pieces (a:=a) hw
  let v (j : ℕ) := atWidth N (decoded p (b.stage hw plan j))
  have geo (j : Fin l.length) := get_geometry hw ha b.k b.s b.w j
  let U (j : ℕ) : EuclideanSpace ℂ (Fin N) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N) :=
    if h : j < l.length then (resizeIso A N (l.get ⟨j,h⟩) (geo ⟨j,h⟩).2.1).toLinearIsometry
    else LinearIsometry.id
  have step (j : ℕ) (hj : j < l.length) (h : ‖v j‖ ≤ R) :
      Good hw plan (l.get ⟨j,hj⟩) (b.reached hw plan ha ⟨j,hj⟩) ∧
      ‖v (j+1) - U j (v j)‖ ≤ δ := by
    let ix : Fin l.length := ⟨j,hj⟩
    let u := l.get ix
    have w : u.w=b.w := (geo ix).1
    have n : count A u=N := (geo ix).2.1
    have ent := initial_transport (p:=p) u w n (b.stage hw plan j)
    obtain ⟨hg,he⟩ := localStep ix (ent ▸ h)
    refine ⟨hg,?_⟩
    change ‖atWidth N (decoded p (trajectory hw plan l b.row (j+1))) - U j (v j)‖ ≤ δ
    rw [trajectory_succ hw plan l ix w]
    simp only [U, hj, ↓reduceDIte, LinearIsometryEquiv.coe_toLinearIsometry]
    rw [show v j = atWidth N (decoded p (b.stage hw plan j)) from rfl, resize_at]
    exact (gap_transport (p:=p) u w n _ _).trans_le he
  have bounds := fun j (hj : j ≤ l.length) =>
    roundedLayerPrefix_bound U v l.length hd hR (fun n hn h => (step n hn h).2) (j:=j) hj
  have target (j : ℕ) (hj : j ≤ l.length) :
      exactLayerPrefix U (v 0) j = atWidth N
        ((l.take j).foldl (fun y s => idealRow A s y) (decoded p b.row)) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hl : j < l.length := by omega
      rw [exactLayerPrefix, ih (by omega), List.take_succ_eq_append_getElem hl,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [U, hl, ↓reduceDIte, LinearIsometryEquiv.coe_toLinearIsometry]
      exact resize_at ..
  refine ⟨fun j => (step j.val j.isLt (bounds j.val j.isLt.le).2).1, ?_, ?_⟩
  · have h := norm_exactLayerPrefix U (v 0) l.length
    rw [target _ le_rfl, List.take_length] at h
    simpa only [l,Root.pieces,A,ideal_even _ _ ha hw,v,Root.stage,trajectory] using h
  have h := (bounds l.length le_rfl).1
  rw [target _ le_rfl, List.take_length] at h
  simpa only [l, Root.pieces, A, ideal_even _ _ ha hw] using h

end
end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
