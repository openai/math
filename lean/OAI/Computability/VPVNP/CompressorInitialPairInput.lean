import OAI.Computability.VPVNP.CompressorInitialLiveBoundary
import OAI.Computability.VPVNP.PaperPairParameters

/-! # Identifying the physical initial graph with the compression theorem's input

Both the native cursor scan and the abstract pair input reverse the bits
within their designated base and lane blocks. Transporting the equality
of the total widths through the labels identifies the two states literally.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledTrace

open BurstRAM Compression LiveProgram CursorNetwork CursorBounds CursorRouting
open scoped Fin.CommRing

private theorem coordinate_state {d j l a pad : ℕ} {s : Type} [Fintype s] (eqn : d = j+l)
    (hD : 1 < d) (sum : 1 < j+l) (degree : 2+pad = 2^a) (bits : s → ℕ) :
    cursorState ((finCongr eqn).trans (cursorCoordinateLabels j l)) hD degree bits =
      cursorState (cursorCoordinateLabels j l) sum degree bits := by
  subst d
  rfl

/-- At the physical split the six-column cursor graph is the very state
used for the pair's compression choices, widths and path contraction. -/
theorem initial_pairInput {k : Type*} [_root_.Field k] (S : BlockSchedule k) (addr n l : ℕ)
    (split : l ≤ virtualBits addr n) (hD : 1 < virtualBits addr n)
    (sum : 1 < (virtualBits addr n-l)+l) (hd : 2+(2^(S.degreeExponent 0)-2) = 2^(S.degreeExponent 0)) :
    pairInput S (laneLabels (virtualBits addr n) l split) hD =
      cursorState (cursorCoordinateLabels (virtualBits addr n-l) l) sum hd
        (ramFieldBits (virtualBucket n) (wordBits addr n) : RAMSystem (virtualBits addr n) → ℕ) :=
  coordinate_state (Nat.sub_add_cancel split).symm hD sum hd _

/-- The rational program exponent gives the same number of reserved lanes
as the mathematical schedule, and the reserved lanes fit at every large length. -/
theorem actual_laneSplit {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
    (u : PairExponents B.growthConstant) (addr n : ℕ) (lanes : S.laneBits ≤ addr) (hn : 3 ≤ n) :
    let T := roundedDown (blockRatio u).num (blockRatio u).den n
    T = blockCount (u.θ : ℝ) n ∧ T*S.laneBits ≤ virtualBits addr n := by
  intro T
  have h := blockRatio_floor u n
  refine ⟨h,?_⟩
  rw [show T = blockCount (u.θ : ℝ) n from h,Nat.mul_comm]
  exact laneBudget addr S.laneBits n lanes (by exact_mod_cast (show u.θ ≤ 1 by linarith [u.theta_lt])) hn

end CompressorRecords.ScheduledTrace

end VPVNP
end Computability
end OAI
