import OAI.Computability.NearSquareRoot.PhysicalWalshCompileFrameHeader
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeBase

/-! # Values and storage expenses of the compiled recursive Walsh frames -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.FrameValues

open IntegerMultiplication Code PhysicalWalsh PhysicalWalshNode ChildLanes

open private cell flat_cells bank_cells from OAI.Computability.NearSquareRoot.PhysicalWalshNodeIO

/-- Serialized row values, omitting the grid and compact recursion headers. -/
def bank (a W : ℕ) (s : Shape) (y : Fin W → Data s) : List (List Dusk.Pair) :=
  (packet (PhysicalWalshGrid.layout (coords a W) Shape.w) s y).2

theorem split_eq (a W : ℕ) (s : Shape) (hs : 0 < s.level) (hd : W^s.level ∣ s.pref) (x : Data s) :
    ChildLanes.split W (FrameHeader.rulers a W s, flat (a+1) s x) = bank a W s (lane (a+1) W s x) := by
  have p := split_stream (List.finRange (groups W s)) (fun g j => List.ofFn (cell (a+1) W s x g j))
    (inner (a+1) s) (fun _ _ _ => List.length_ofFn)
  simpa only [List.length_finRange,flat_cells s hs hd,bank_cells s hs,bank,FrameHeader.rulers] using p

theorem merge_eq (a W : ℕ) (hW : 0 < W) (s : Shape) (hs : 0 < s.level) (hd : W^s.level ∣ s.pref)
    (y : Fin W → Data s) :
    ChildLanes.merge W (FrameHeader.rulers a W s,bank a W s y) = flat (a+1) s (unlane (a+1) hW s y) := by
  let x := unlane (a+1) hW s y
  have p := merge_rows (List.finRange (groups W s)) (fun g j => List.ofFn (cell (a+1) W s x g j))
    (inner (a+1) s) (fun _ _ _ => List.length_ofFn)
  simpa only [List.length_finRange,flat_cells s hs hd,bank_cells s hs,x,lane_unlane,bank,FrameHeader.rulers] using p

private theorem cells_le (A : ℕ) (s : Shape) :
    count A s * (4*(s.w+1)+4) ≤ 8*nodeVolume A s := by
  unfold nodeVolume
  rw [Nat.mul_left_comm 8]
  gcongr <;> omega

theorem flat_size (A d : ℕ) (s : Shape) (x : Data s) :
    size (flat A s x) ≤ 8*(allowance A d s+1) := by
  rw [PhysicalWalshNode.flat_size]
  have h := (cells_le A s).trans (Nat.mul_le_mul_left 8 (nodeVolume_le A d s))
  omega

theorem bank_size (a W d : ℕ) (s : Shape) (hs : 0 < s.level) (hd : W^s.level ∣ s.pref)
    (y : Fin W → Data s) : size (bank a W s y) ≤ 10*(allowance (a+1) d s+1) := by
  let A := a+1
  have step : ∀ j : Fin W, size ((PhysicalWalshGrid.layout (coords a W) Shape.w).store s (y j)) ≤
      (groups W s*inner A s)*(4*(s.w+1)+4)+1 := by
    intro j
    change size (((coords a W).rows s).map (Dusk.mark ∘ y j)) ≤ _
    rw [coords_range a W s hs,← List.map_map,PhysicalWalsh.Padding.marks_size,List.length_map,List.length_range]
  have h := PhysicalWalshBank.size_rows_le _ _ step
  change size (bank a W s y) ≤ W*((groups W s * inner A s)*(4*(s.w+1)+4)+1+1)+1 at h
  have hg := groups_mul hs hd
  have hg' : W ≤ s.pref := by
    rw [← hg]
    exact Nat.le_mul_of_pos_left W (Nat.le_max_left ..)
  have hw : W ≤ count A s := hg'.trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos (pow_pos (by decide) _) s.suff_pos))
  have h' : W*((groups W s * inner A s)*(4*(s.w+1)+4)+1+1)+1 =
      count A s*(4*(s.w+1)+4)+2*W+1 := by
    dsimp only [count]
    rw [← hg]
    ring
  rw [h'] at h
  have vol := nodeVolume_le A d s
  have wle : count A s ≤ nodeVolume A s := (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have full := cells_le A s
  change _ ≤ 10*(allowance A d s+1)
  omega

end PhysicalWalshCompile.FrameValues

end NearSquareRoot
end Computability
end OAI
