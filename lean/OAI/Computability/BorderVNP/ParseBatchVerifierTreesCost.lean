import OAI.Computability.BorderVNP.ParseBatchVerifierTreesStructure

/-! # Absolute gate bounds for the assembled batch verifier -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchTrees

open VPVNP VPVNP.VerifierNetwork

variable {m g n r : ℕ}

/-- A structure test of cost A m L^E, where L is the batch word width,
gives a complete circuit of cost (A+607) m r L^max(E,3).
The constant covers the two leaf sorts and the final conjunction. -/
theorem exists_acceptFrame_of_shape (d : Fin n) (h : Fin g) (hm : m = d.val+1)
    (hr : 0 < r) (hw : max m (max g n) + 1 ≤ 2*m*r)
    (shape : Frame (RowPins m g n d) Unit)
    (hs : ∀ bs, shape.eval (fun ij => bs ij.1 ij.2) () = true ↔ Structure d h bs)
    (A E : ℕ) (hc : shape.size ≤ A*m*(Nat.clog 2 (2*m*r)+3)^E) :
    ∃ f : Frame (BatchPins m g n r d) Unit,
      f.size ≤ (A+607)*(m*r)*(Nat.clog 2 (2*m*r)+3)^(max E 3) ∧
      ∀ x bs, f.eval (batchInput d x bs) () = true ↔ ParseBatch.Accepted d h x bs := by
  let L := Nat.clog 2 (2*m*r)+3
  let M := max E 3
  let P := m * L^M
  have hp : 1 ≤ P := Nat.mul_pos (by omega : 0 < m) (Nat.pow_pos (by dsimp [L]; omega : 0 < L))
  have hl : 0 < L := by dsimp [L]; omega
  have hshape : shape.size ≤ A*P := hc.trans <| by
    dsimp only [P, M]
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hl (le_max_left ..))
  have hleaf : (ParseBatchLeaves.frame m g n (2*d.val+1) (Nat.clog 2 (2*d.val+1))).size ≤
      600*P := (ParseBatchLeaves.frame_size_per_query d hm hr hw).trans <| by
    dsimp only [P, M]
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hl (le_max_right ..))
  have ht : (checkTree d shape).size+2 ≤ (A+605)*P := by
    have h₁ := checkTree_size d shape
    rw [Nat.add_mul]
    omega
  obtain ⟨f, hf, he⟩ := exists_batch_of_tree (r := r) d h (checkTree d shape) (checkTree_eval d h hm shape hs)
  refine ⟨f, hf.trans ?_, he⟩
  calc
    2 + r*((checkTree d shape).size+2) ≤ 2 + r*((A+605)*P) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left r ht) 2
    _ ≤ (A+607)*(r*P) := by
      have hpos : 1 ≤ r*P := Nat.mul_pos hr hp
      calc
        _ ≤ 2*(r*P) + (A+605)*(r*P) :=
          Nat.add_le_add (by omega) (le_of_eq (by ring))
        _ = _ := by ring
    _ = _ := by dsimp [P,M,L]; ring

end ParseBatchTrees

end BorderVNP
end Computability
end OAI
