import OAI.Computability.VPVNP.RAMTapeSortOneStagePorts
import OAI.Computability.VPVNP.RAMTapeSortLayerRowsModel

/-! # The incident stream and cost of one physical sorting layer -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortOneStage

open BurstRAM RAMSort RAMBoundary Boundary

variable {h d w : ℕ}

/-- The next two physical blocks precede the remaining stream at a cross-site layer. -/
def stream (s : Stage (h+d)) (send recv : Wires h (RawSlot w)) (tail : List Bool) : List Bool :=
  if s.stride < h then tail else blockBytes (List.ofFn send) ++ (blockBytes (List.ofFn recv) ++ tail)

theorem prepare_runs (s : Stage (h+d)) (v : Word d) (current send recv : Wires h (RawSlot w))
    (tail flags : List Bool) :
    ∃ t ≤ 6*h+8+SortBoundary.splitCost (2^h) w,
      prepare.Runs t (bank v s.phase s.stride w h (blockBytes (List.ofFn current)) [] []
        (stream s send recv tail) flags)
        (bank v s.phase s.stride w h (blockBytes (List.ofFn current)) []
          (SortLayerRows.fieldsBefore s send []) (SortLayerRows.fieldsBefore s recv tail) flags) := by
  by_cases hl : s.stride < h
  · simp only [stream, SortLayerRows.fieldsBefore, hl, ↓reduceIte]
    exact ⟨_, by omega, prepare_local v s.phase s.stride w h _ _ _ hl⟩
  · simp only [stream, SortLayerRows.fieldsBefore, hl, ↓reduceIte, List.append_nil]
    exact ⟨_, by omega, prepare_cross v s.phase s.stride w h _ _ _ _ (by omega) (by simp)⟩

/-- A common bound for all stages, covering split, row visits, and block reversal. -/
def budget (h d w : ℕ) :=
  6*h+8 + SortBoundary.splitCost (2^h) w + 8192*(2^h+1)^2*(h+d+w+1) + 3*(2^h*(5*w)) + 2

theorem budget_le (h d w : ℕ) : budget h d w ≤ 16384*(2^h+1)^2*(h+d+w+1) := by
  let n := 2^h
  let m := h+d+w+1
  have hnm : n*(w+1) ≤ (n+1)^2*m := by
    gcongr
    · calc
        n ≤ (n+1)*1 := by simp
        _ ≤ (n+1)*(n+1) := Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le _))
        _ = _ := (pow_two _).symm
    · dsimp [m]; omega
  have hbase : m ≤ (n+1)^2*m := Nat.le_mul_of_pos_left _ (by positivity)
  have hn : n ≤ n*(w+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hw : n*w ≤ n*(w+1) := Nat.mul_le_mul_left _ (by omega)
  change 6*h+8 + (n*(40*w+17)+4) + 8192*(n+1)^2*m + 3*(n*(5*w)) + 2 ≤ 16384*(n+1)^2*m
  rw [Nat.mul_add, show n*(40*w) = 40*(n*w) by ring, show n*(5*w) = 5*(n*w) by ring,
    Nat.mul_assoc 8192, Nat.mul_assoc 16384, Nat.mul_comm n 17]
  dsimp only [m] at hbase ⊢
  dsimp only [m] at hnm
  omega

end RAMTape.SortOneStage

end VPVNP
end Computability
end OAI
