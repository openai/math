import OAI.Hierarchy.ProbeStageRegularization

namespace OAI
/-! # The original permutation remains readable after subdivision -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM ProtocolRAM
open scoped Fin.CommRing
noncomputable section

/-- The native root writer and every subsequent phase preserve the original
permutation values in the low segment, including the zero-round case. -/
theorem images_raw {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h)))
    (raw : Memory (wordBits h d copies)) (read : ∀ r : Fin (2^h),raw r.val=((π r).val : Word _))
    (r : Fin (2^h)) : images h d (inputTape h d _ raw) (rounds d) r.val=raw r.val := by
  let input := inputTape h d _ raw
  have atStep : ∀ k≤rounds d,images h d input k r.val=raw r.val := by
    intro k
    induction k with
    | zero =>
      intro _
      exact (columns_frame [.lit 0,.row] input (Or.inl r.isLt)).trans (inputTape_root raw r.isLt)
    | succ k ih =>
      intro bound
      let j : Fin (rounds d) := ⟨k,by omega⟩
      have previous := after_levels hd π raw read (physical_ordinal hd π) k (by omega)
      obtain ⟨fixed,fresh⟩ := previous.future j le_rfl
      have next := phase_result hd π j (images h d input k) fixed previous.parent fresh (physical_ordinal hd π j)
      have low : r.val<phase h d copies k := by
        have le : extent h d≤(3+k*stride d copies)*extent h d :=
          Nat.le_mul_of_pos_left _ (by omega)
        exact (r.isLt.trans_le (height_extent h d)).trans_le le
      exact (next.frame r.val (Or.inl low)).trans (ih (by omega))
  exact atStep _ le_rfl

end
end Hierarchy.ProbeStage.Native

end OAI
