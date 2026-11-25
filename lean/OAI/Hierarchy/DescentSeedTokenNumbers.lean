import OAI.Hierarchy.DescentPrimitivePaletteCounts
import OAI.Hierarchy.DescentSIMDLookup
import Mathlib.Tactic

namespace OAI
/-! # Widths of the original census role and its physically packed input tile -/
namespace Hierarchy.DescentSeedRoot
def digitsNeeded (s : ℕ) := s.log2+1
end Hierarchy.DescentSeedRoot

namespace Hierarchy.DescentPackedSeed.Primitive
open DescentSIMDLookup DescentSeedRoot DescentPrimitivePalette
open scoped BigOperators
def roleBits (s : ℕ) := digitsNeeded (censusCount s)
def pieces (w s : ℕ) := lanes w (8*digitsNeeded s)
theorem role_bound_short (s : ℕ) : roleBits s≤8*digitsNeeded s+3 := by
  let d:=digitsNeeded s
  have pos:0<d:=Nat.zero_lt_succ _
  have source:s+1≤2^d:=Nat.lt_log2_self ..
  have upper (m:Fin 4) : (s+1)^(2^m.val)≤2^(8*d) := by
    calc (s+1)^(2^m.val)≤(2^d)^(2^m.val):=Nat.pow_le_pow_left source _
      _≤(2^d)^8:=Nat.pow_le_pow_right (Nat.two_pow_pos _) (Nat.pow_le_pow_right (by decide : 0<2) (show m.val≤3 by omega))
      _=2^(8*d):=by rw [←pow_mul,Nat.mul_comm]
  have sum : (∑ m:Fin 4,(s+1)^(2^m.val))≤4*2^(8*d):=by
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun m _=>upper m)
  have positive:0<2^(8*d):=Nat.two_pow_pos _
  have small:censusCount s<2^(8*d+3):=by unfold censusCount;rw [pow_add];norm_num;omega
  have bits:= (Nat.log2_lt (show censusCount s≠0 by unfold censusCount;omega)).mpr small
  change (censusCount s).log2+1≤8*d+3
  omega

end Hierarchy.DescentPackedSeed.Primitive

end OAI
