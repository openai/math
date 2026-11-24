import OAI.Computability.VPVNP.JointScalarCore
import OAI.Computability.VPVNP.JointScalarRowPrefix

/-! # Packing the exponent coordinates of a signed original-row query -/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointScalar.Leaf

open UniversalCountStack

/-- Concatenate the low `W` bits of each exponent in coordinate order, least significant bit
first within each coordinate. -/
def packed {t : ℕ} (W : ℕ) (a : Fin t → ℕ) : List Bool :=
  (List.ofFn a).flatMap (digits W)

@[simp] theorem packed_length {t : ℕ} (W : ℕ) (a : Fin t → ℕ) : (packed W a).length = t*W := by
  simp [packed, List.length_flatMap, Function.comp_def, List.ofFn_const]

/-- The little-endian binary words sent to the interpreter are the inputs
of the gate checker in the order of its formal wires. -/
theorem query_bits {t : ℕ} (n high W : ℕ) (negative : Bool) (row : ℕ) (a : Fin t → ℕ) :
    List.ofFn (query (n := n) (high := high) (W := W) negative row a) =
      negative :: (digits (n+high) row ++ packed W a) := by
  simp only [query, List.ofFn_fin_append, List.ofFn_const, List.replicate_one, List.singleton_append,
    RowPrefix.digits_ofFn]
  congr 2
  rw [List.ofFn_mul]
  change _ = ((List.ofFn a).map (digits W)).flatten
  rw [List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [Function.comp_apply, RowPrefix.digits_ofFn]
  apply congrArg List.ofFn
  funext j
  have idx (h : i.val * W + j.val < t * W) :
      (⟨i.val * W + j.val, h⟩ : Fin (t*W)) = finProdFinEquiv (i,j) :=
    Fin.ext (by change _ = j.val + W * i.val; ring)
  simp only [idx, Equiv.symm_apply_apply]

end JointScalar.Leaf

end VPVNP
end Computability
end OAI
