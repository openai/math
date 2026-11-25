import OAI.Hierarchy.DescentGLPhysicalTrajectory

namespace OAI
/-! The central solver preserves every word outside its rectangular arena,
including for arbitrary input tables and arbitrary initial memory. -/
namespace Hierarchy.DescentGL.PhysicalTrajectory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM RowStageRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
variable {w : ℕ}

private theorem shelf_frame {h r : ℕ} (s : Shelf) (ptr : Fin (h+1+r) → ℕ) (tabs : Fin (r+1) → ℕ)
    (m : Memory w) (a : ℕ) (di : a < s.data ∨ s.data + 2^(h+1+r) ≤ a)
    (sc : a < s.scores ∨ s.scores + 2^(h+1+r) ≤ a)
    (pick : a < s.row ∨ s.row+1 ≤ a) (mask : a < s.nextMask ∨ s.nextMask+2^(h+1+r) ≤ a) :
    RowStageRAM.after s ptr tabs m a = m a := by
  unfold RowStageRAM.after writeMask writeChoice writeScore writeInput
  rw [SpanRAM.frame _ _ _ _ a mask,SpanRAM.frame _ _ _ _ a pick,
    SpanRAM.frame _ _ _ _ a sc,SpanRAM.frame _ _ _ _ a di]

private theorem shelf_ranges (base offset stop width a : ℕ)
    (edge : offset+(3*width+1) ≤ stop) (outside : a < base ∨ base+stop+width ≤ a) :
    (a < base+offset+width ∨ base+offset+width+width ≤ a) ∧
    (a < base+offset+2*width ∨ base+offset+2*width+width ≤ a) ∧
    (a < base+offset+3*width ∨ base+offset+3*width+1 ≤ a) ∧
    (a < base+offset+(3*width+1) ∨ base+offset+(3*width+1)+width ≤ a) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

private theorem row_frame (k base : ℕ) (bank : ℕ → ℕ) (m : Memory w) (t : ℕ) (ht : t ≤ k)
    (a : ℕ) (outside : a < base ∨ outputBase k base ≤ a) : result k base bank m t a = m a := by
  induction t with
  | zero =>
    apply SpanRAM.frame
    dsimp [outputBase, placed] at outside
    omega
  | succ t ih =>
    have eqk : t + 1 + (k - (t + 1)) = k := by omega
    have edge : (t+1)*(3*2^k+1) ≤ k*(3*2^k+1) := Nat.mul_le_mul_right _ ht
    rw [Nat.succ_mul] at edge
    obtain ⟨data, scores, pick, mask⟩ :=
      shelf_ranges base (t*(3*2^k+1)) (k*(3*2^k+1)) (2^k) a edge outside
    change RowStageRAM.after _ _ _ _ a = _
    rw [shelf_frame]
    · exact ih (Nat.le_of_succ_le ht)
    · simpa only [eqk, placed] using data
    · simpa only [eqk, placed] using scores
    · exact pick
    · simpa only [eqk, placed] using mask

theorem final_frame (k base : ℕ) (bank : ℕ → ℕ) (m : Memory w) (a : ℕ)
    (outside : a < base ∨ outputBase k base + 2^k ≤ a) : finalMemory k base bank m a = m a := by
  have start : base ≤ outputBase k base :=
    (Nat.le_add_right base (k*(3*2^k+1))).trans (Nat.le_add_right _ (2^k))
  have permutation : a < outputBase k base ∨ outputBase k base + 2^k ≤ a :=
    outside.imp (fun low => low.trans_le start) id
  unfold finalMemory
  rw [DescentGLPermutationRAM.frame _ _ _ a permutation]
  exact row_frame k base bank m k le_rfl a
    (outside.imp id (fun high => (Nat.le_add_right (outputBase k base) (2^k)).trans high))

end
end Hierarchy.DescentGL.PhysicalTrajectory

end OAI
