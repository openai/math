import OAI.Optimization.LinearProgramming.Recovery.PairBuilderNumeric
import OAI.Optimization.LinearProgramming.Recovery.PairBuilderCall
import OAI.Optimization.LinearProgramming.RAM.FrameFirstHeader
import OAI.Optimization.LinearProgramming.Geometry.UniformGramTimeBound

/-! A single finite even-bank window bounds all three freshly staged numerical calls. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder

open RAM RAM.Callable RAM.Call RAM.Tape RAM.Block Elimination Compression Matrix
open _root_.OAI.Optimization.LinearProgramming.Geometry

def scale (h n : ℕ) := h+2*n+2

def workerTime (h n : ℕ) := 6000000*(scale h n)^9

def codeReserve := addressBudget rowROM + addressBudget ResidualROM.program

def capacity (h n previous : ℕ) :=
  previous+codeReserve+workerTime h n+(scale h n)^2+2*(scale h n)+4

def capacityExpr (h n old : AddressTerm 220) : AddressTerm 220 :=
  let z := h+2*n+2
  old+.val codeReserve+6000000*addressPower z 9+z*z+2*z+4

theorem capacityExpr_eq (h n old : AddressTerm 220) (env : Fin 220→ℕ) :
    (capacityExpr h n old).value env = capacity (h.value env) (n.value env) (old.value env) := by
  simp [capacityExpr,capacity,scale,workerTime,AddressTerm.value,AddressOp.value,pow_two]

theorem row_time_bound {a h n : ℕ} (ha : a ≤ h+n) : rowTime a n ≤ workerTime h n := by
  let z := scale h n
  have hz : 1 ≤ z := by dsimp [z,scale]; omega
  have ha' : a ≤ z := by dsimp [z,scale]; omega
  have hn : n ≤ z := by dsimp [z,scale]; omega
  have hp (k : ℕ) (hk : k ≤ 9) : z^k ≤ z^9 := Nat.pow_le_pow_right hz hk
  have hmono : rowTime a n ≤ rowTime z z := by
    dsimp only [rowTime,rowBasisTime,RowPack.packTime,RowGather.cellTime,uniformTableTime,uniformEntryTime,
      uniformRowDotCost,clearFlagsCost,basisScanCost,basisProbeCost,decisionCost,maskTableCost]; gcongr
  apply hmono.trans
  change rowTime z z ≤ 6000000*z^9
  dsimp only [rowTime,rowBasisTime,RowPack.packTime,RowGather.cellTime,uniformTableTime,uniformEntryTime,
    uniformRowDotCost,clearFlagsCost,basisScanCost,basisProbeCost,decisionCost,maskTableCost]
  nlinarith only [hp 0 (by decide),hp 1 (by decide),hp 2 (by decide),hp 3 (by decide),hp 4 (by decide),
    hp 5 (by decide),hp 6 (by decide),hp 7 (by decide),hp 8 (by decide)]

theorem residual_time_bound {a h n : ℕ} (ha : a ≤ h+n) : ResidualROM.time a n ≤ workerTime h n := by
  let z := scale h n
  have hz : 1 ≤ z := by dsimp [z,scale]; omega
  have hs : a+n+1 ≤ z := by dsimp [z,scale]; omega
  have hn : n ≤ z := by dsimp [z,scale]; omega
  have hg : uniformGramTime a n ≤ 5000000*z^9 := (uniformGramTime_bound a n).trans (by gcongr)
  have hp (k : ℕ) (hk : k ≤ 9) : z^k ≤ z^9 := Nat.pow_le_pow_right hz hk
  have hp' : residualPassTime n ≤ residualPassTime z := by dsimp only [residualPassTime,uniformTableTime,uniformEntryTime]; gcongr
  have hm : 200*(a+n+1)^2 ≤ 200*z^2 := by gcongr
  change 200*(a+n+1)^2+uniformGramTime a n+5+residualPassTime n+1 ≤ 6000000*z^9
  apply (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add hm hg) 5) hp') 1).trans
  dsimp only [residualPassTime,uniformTableTime,uniformEntryTime]
  nlinarith only [hp 0 (by decide),hp 1 (by decide),hp 2 (by decide),hp 3 (by decide),hp 4 (by decide)]

/-- Both the old native tape and every fresh numerical result fit strictly inside the reset window. -/
theorem old_fits (h n previous : ℕ) : previous < capacity h n previous := by unfold capacity; omega

theorem input_fits {h n a : ℕ} (previous : ℕ) (ha : a ≤ h+n) : a*n ≤ capacity h n previous := by
  have a1 : a ≤ scale h n := by dsimp [scale]; omega
  have n1 : n ≤ scale h n := by dsimp [scale]; omega
  have a2 := Nat.mul_le_mul a1 n1
  unfold capacity; rw [pow_two]; omega

theorem pair_fits (h n previous : ℕ) : 2 ≤ capacity h n previous := by unfold capacity; omega

theorem output_fits {K : Type} {h n a t : ℕ} (previous : ℕ) (ha : a ≤ h+n) (p : Program)
    (hp : addressBudget p ≤ codeReserve) (ht : t ≤ workerTime h n) (D : Matrix (Fin a) (Fin n) K) :
    nativeWindow p [a,n] (encodedGramInput D)+t < capacity h n previous := by
  let z := scale h n
  have a1 : a ≤ z := by dsimp [z,scale]; omega
  have n1 : n ≤ z := by dsimp [z,scale]; omega
  have a2 := Nat.mul_le_mul a1 n1
  simp only [nativeWindow,length_encodedGramInput,List.length_cons,List.length_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  change max (addressBudget p) (max (a*n) (max 2 (a+n)))+t < previous+codeReserve+workerTime h n+z^2+2*z+4
  rw [pow_two]; omega

theorem residualWidth_mono {k k' n e : ℕ} (hk : k ≤ k') : residualWidth k n e ≤ residualWidth k' n e := by
  dsimp only [residualWidth,ResidualBitsCommon.residualEntryBits,gramProjectorBits,gramWorkspaceBits,gramDetBits,detRegisterBits,dotBitBound]; gcongr

/-- Only actual LP entries and dimensions enter the numerical increments. Unrelated caller
registers enter the total bit bound only through one initial maximum. -/
def pairWidth (h n e : ℕ) :=
  let first := rowWidth h n e
  let residual := residualWidth n n first
  max (max 3 first) (max residual (rowWidth n n residual))

theorem firstWidth_le (h n e : ℕ) : rowWidth h n e ≤ pairWidth h n e :=
  (le_max_right ..).trans (le_max_left ..)

theorem residualWidth_le (h n e : ℕ) : residualWidth n n (rowWidth h n e) ≤ pairWidth h n e :=
  (le_max_left ..).trans (le_max_right ..)

theorem lastWidth_le (h n e : ℕ) : rowWidth n n (residualWidth n n (rowWidth h n e)) ≤ pairWidth h n e :=
  (le_max_right ..).trans (le_max_right ..)

end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
