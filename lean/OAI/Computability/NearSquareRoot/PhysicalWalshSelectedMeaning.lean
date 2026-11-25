import OAI.Computability.NearSquareRoot.PhysicalWalshPieceIdeal
import OAI.Computability.NearSquareRoot.PhysicalWalshPadProjection
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshWindowMatrix
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshWindowRows
import OAI.Computability.NearSquareRoot.PrecisionButterflyMatrix

/-! # The selected Walsh matrix realized by the complete contiguous schedule -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open Matrix FlatWalshNode FlatWalshWindow PhysicalWalshNode
noncomputable section

/-- The ideal terminal one-bit pass is the same normalized pair operation
used by the rounded physical butterfly. -/
theorem odd_butterfly (x : ℕ → ℂ) (g : ℕ) (b : Bool) :
    activeRow 1 1 x (2*g + (if b then 1 else 0)) =
      (SynchronizedPair.w : ℂ)*FixedPoint.butterflySum b (x (2*g)) (x (2*g+1)) := by
  let j : Fin (2^1) := if b then 1 else 0
  have eq := activeRow_at 1 1 Nat.one_pos x g (0 : Fin 1) j
  simp_rw [FlatWalshKernel.fullFlat, Fin.prod_univ_one] at eq
  simp only [pow_one] at eq
  cases b <;>
    simp [j, FlatWalshKernel.bitFactor, FixedPoint.butterflySum, Nat.mul_comm g] at eq ⊢ <;>
    rw [eq] <;> ring

/-- Full Walsh acts independently on every spectator row of the padded
stream, in precisely the indexing used by padding and truncation. -/
theorem activeRow_onRows (q s : ℕ) (x : ℕ → ℂ) :
    (fun i : Fin (q*2^s) => activeRow s 1 x i.val) =
      Padding.onRows q (fun v => BoxFin.flatWalsh Finset.univ *ᵥ v) (fun i => x i.val) := by
  funext i
  obtain ⟨⟨g,j⟩,rfl⟩ := (finProdFinEquiv (m := q) (n := 2^s)).surjective i
  rw [Padding.onRows_apply]
  have he (r : Fin (2^s)) : (finProdFinEquiv (g,r)).val = g.val*2^s+r.val := by
    change r.val+2^s*g.val = _
    ring
  rw [he]
  have H := activeRow_at s 1 Nat.one_pos x g.val 0 j
  simpa only [Fin.val_zero, mul_one, add_zero, mulVec, dotProduct, he] using H

/-- On original packed addresses the completed action is the normalized
selected-bit matrix for the low contiguous field, including empty fields. -/
theorem activeRow_low (k s : ℕ) (hs : s ≤ k) (x : ℕ → ℂ) :
    (fun i : Fin (2^k) => activeRow s 1 x i.val) =
      BoxFin.flatWalsh (bits k s 0 (by omega)) *ᵥ (fun i => x i.val) := by
  funext z
  let P := k-s
  have width : P+s+0=k := by dsimp [P]; omega
  let K := BoxFin.flatWalsh (bits k s 0 (by omega))
  have ent p b y q c u : K (pack P s 0 k width ((p,b),y)) (pack P s 0 k width ((q,c),u)) =
      if p=q ∧ b=c then BoxFin.flatWalsh Finset.univ y u else 0 := by
    dsimp only [K]
    rw [flatWalsh_window]
    have hy := pack_split P s 0 k width p b y
    have hu := pack_split P s 0 k width q c u
    have ey : middle s 0 (pack P s 0 k width ((p,b),y)) = y := Fin.ext hy.2.1
    have eu : middle s 0 (pack P s 0 k width ((q,c),u)) = u := Fin.ext hu.2.1
    simp only [hy.2.2, hu.2.2, hy.1, hu.1, ey, eu, Fin.val_inj]
  have H := activeRow_window P s 0 k width 1 Nat.one_pos 0 0 x z K ent
  simpa only [pow_zero, one_mul, Fin.val_zero, zero_mul, zero_add, mul_one, add_zero,
    Matrix.mulVec, dotProduct] using H

/-- Matrix specification of the complete ordered traversal, on the
original array after discarding any extra spectator rows. -/
theorem ideal_selected (A W : ℕ) (hA : 1 < A) (hW : 0 < W) (k s w : ℕ) (hs : s ≤ k)
    (x : ℕ → ℂ) :
    (fun z : Fin (2^k) => activeRow (s%2) 1
      ((schedule A W hW k s w).foldl (fun y p => idealRow A p y) x) z.val) =
      BoxFin.flatWalsh (bits k s 0 (by omega)) *ᵥ (fun i => x i.val) := by
  rw [ideal_complete A W hA hW]
  exact activeRow_low k s hs x

end
end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
