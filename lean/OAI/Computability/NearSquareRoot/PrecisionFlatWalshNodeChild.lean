import OAI.Computability.NearSquareRoot.PrecisionFlatWalshNodeIndex
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshWindowRows
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshWindowMatrix
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshChildKernel

/-! # The selected-lane matrix executed by a contiguous recursive child -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatWalshNode

open PhysicalWalshNode FlatWalshKernel FlatWalshWindow KernelScaleLayout

/-- Descending to one slot leaves its prefix and suffix spectators fixed.
The child in the physical ordinal layout therefore applies precisely the
selected-lane Walsh matrix in the full paired-column address space. -/
theorem idealRow_descend (a W : ℕ) (s : Shape) (j : Fin (a+1)) (g : ℕ) (t : Fin s.suff)
    (z : NodeAddress a s) (v : ℕ → ℂ) :
    idealRow (a+1) (descend (a+1) W j s) v (rowPos a s g z t) =
      ∑ u : NodeAddress a s, BoxFin.flatWalsh (laneBits a ((a+1)^(s.level-1)) j) (rank z) (rank u) *
        v (rowPos a s g u t) := by
  classical
  let h := (a+1)^(s.level-1)
  let L := 2*h
  let n := (a+1)*L
  let P := j.val*L
  let d := (a-j.val)*L
  have width : P+L+d=n := by
    change j.val*L+L+(a-j.val)*L=(a+1)*L
    rw [← Nat.succ_mul, ← Nat.add_mul]
    congr 1; omega
  have fit : d+L ≤ n := by omega
  have eqBits : laneBits a h j = bits n L d fit := by
    ext p
    rw [mem_laneBits_iff, mem_bits]
  let K := BoxFin.flatWalsh (laneBits a h j)
  have ent p b y q c x : K (pack P L d n width ((p,b),y)) (pack P L d n width ((q,c),x)) =
      if p=q ∧ b=c then BoxFin.flatWalsh Finset.univ y x else 0 := by
    dsimp only [K]
    rw [eqBits, flatWalsh_window]
    have hy := pack_split P L d n width p b y
    have hx := pack_split P L d n width q c x
    have ey : middle L d (pack P L d n width ((p,b),y)) = y := Fin.ext hy.2.1
    have ex : middle L d (pack P L d n width ((q,c),x)) = x := Fin.ext hx.2.1
    simp only [hy.2.2, hx.2.2, hy.1, hx.1, ey, ex, Fin.val_inj]
  have run := activeRow_window P L d n width s.suff s.suff_pos g t v (rank z) K ent
  change activeRow L (2^(((a+1)-1-j.val)*L)*s.suff) v ((g*2^n+(rank z).val)*s.suff+t.val) = _
  rw [Nat.add_sub_cancel, run]
  exact ((addressEquiv a h).symm.sum_comp (fun u : Fin (2^n) =>
    K (rank z) u * v ((g*2^n+u.val)*s.suff+t.val))).symm

end FlatWalshNode

end NearSquareRoot
end Computability
end OAI
