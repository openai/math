import OAI.Hierarchy.DescentFallbackOperandBranch
import OAI.Hierarchy.DescentTreePrefixIntervals

namespace OAI
/-! # The bit extracted from a measured padded address names its actual child -/
namespace Hierarchy.DescentTreePrefixIntervals

theorem padded_prefix {d h H : ℕ} (depth : d≤h) (wide : h≤H) (leaf : Bits h) :
    start H leaf/2^(H-d)=lex d (cut depth leaf) := by
  have bounds := (member depth wide leaf (cut depth leaf)).2 rfl
  let width := 2^(H-d)
  have positive : 0<width := Nat.two_pow_pos _
  have lo : lex d (cut depth leaf)*width≤ start H leaf := bounds.1
  have hi : start H leaf<(lex d (cut depth leaf)+1)*width := bounds.2
  exact Nat.le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul positive).2 hi))
    ((Nat.le_div_iff_mul_le positive).2 lo)

theorem child_path {d h H : ℕ} (depth : d<h) (wide : h≤H) (leaf : Bits h) :
    DescentFallbackOperandBranch.Config.childPath H (List.ofFn (cut depth.le leaf)) (start H leaf)=
      List.ofFn (cut (Nat.succ_le_of_lt depth) leaf) := by
  let next := cut (Nat.succ_le_of_lt depth) leaf
  have digit : decide ((start H leaf/2^(H-(d+1)))%2=1) = next (Fin.last d) := by
    rw [padded_prefix (Nat.succ_le_of_lt depth) wide]
    change decide ((2*lex d (fun i=>next i.castSucc)+(next (Fin.last d)).toNat)%2=1)=next (Fin.last d)
    cases hx : next (Fin.last d) <;> simp [Nat.add_mod]
  change DescentFallbackOperandBranch.Config.childPath H _ _=List.ofFn next
  rw [List.ofFn_succ_last]
  simp only [DescentFallbackOperandBranch.Config.childPath,List.length_ofFn,digit]; rfl

end Hierarchy.DescentTreePrefixIntervals

end OAI
