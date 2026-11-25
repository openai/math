import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Exact whole words at the output of a masked local lookup -/
namespace Hierarchy.DescentSIMDLookup
noncomputable section
variable {a b M H G : ℕ}

theorem masked_fits (f : Cell a → Cell b) (x : Fin H → Fin G → Cell a) (p : Row H G M) :
    masked f x p < 2^(b*M) :=
  (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le
    (Nat.pow_le_pow_right (by decide : 0<2) (Nat.mul_le_mul_left b (min_le_left _ _)))

theorem masked_eq_data (f : Cell a → Cell b) (x : Fin H → Fin G → Cell a) (p : Row H G M) :
    masked f x p = (data (fun h j=>f (x h j)) p).val := by
  let z : Cell (b*M):=⟨masked f x p,masked_fits f x p⟩
  change z.val = _
  apply congrArg Fin.val
  apply (encode b M).symm.injective
  funext i
  apply Fin.ext
  have get := (digit_encode ((encode b M).symm z) i).symm
  rw [Equiv.apply_symm_apply] at get
  rw [get]
  change digit b i.val (masked f x p) = _
  simp only [data,Equiv.symm_apply_apply]
  by_cases live : p.2.val*M+i.val<G
  · rw [dite_eq_left live]
    exact active_read f x p i live
  · rw [dite_eq_right live]
    exact padding_zero f x p i (by unfold used;omega)

end
end Hierarchy.DescentSIMDLookup

end OAI
