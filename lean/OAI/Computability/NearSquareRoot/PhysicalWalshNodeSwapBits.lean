import OAI.Computability.NearSquareRoot.PhysicalWalshNodeConjugate
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeSwapWord

/-! # Whole-slot interchanges on the physical record ordinal -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode
open KernelPass KernelScaleLayout

namespace SwapWord
open XorBits

/-- Three aligned CNOTs interchange the entire field, including an arbitrary
short lower slice of the full Walsh slot. -/
theorem three_xor (lo hi w n : ℕ) (apart : lo+w ≤ hi) :
    window lo hi w (window hi lo w (window lo hi w n)) = run lo hi w n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [run_bit _ _ _ _ apart]
  by_cases low : lo ≤ i ∧ i < lo+w
  · have outside : ¬(hi ≤ i ∧ i < hi+w) := by omega
    have pair : hi ≤ i-lo+hi ∧ i-lo+hi < hi+w := by omega
    simp only [window_bit,pos,ite_eq_right outside,ite_eq_left low,ite_eq_left pair,show i-lo+hi-hi+lo = i by omega]
    cases n.testBit i <;> cases n.testBit (i-lo+hi) <;> rfl
  by_cases high : hi ≤ i ∧ i < hi+w
  · have pair : lo ≤ i-hi+lo ∧ i-hi+lo < lo+w := by omega
    have outside : ¬(hi ≤ i-hi+lo ∧ i-hi+lo < hi+w) := by omega
    simp only [window_bit,pos,ite_eq_right low,ite_eq_left high,ite_eq_left pair,ite_eq_right outside,show i-hi+lo-lo+hi = i by omega]
    cases n.testBit i <;> cases n.testBit (i-hi+lo) <;> rfl
  simp only [window_bit,pos,ite_eq_right low,ite_eq_right high]

/-- Apply a packed operation to the word above the entire low spectator
range, preserving its residue for every positive (possibly odd) stride. -/
def stride (s : Shape) (f : ℕ → ℕ) (n : ℕ) := f (n/s.suff)*s.suff+n%s.suff

theorem stride_comp (s : Shape) (f g : ℕ → ℕ) (n : ℕ) :
    stride s f (stride s g n) = stride s (f ∘ g) n := by
  simp only [stride,Function.comp_apply,Nat.mul_comm (g _),Nat.mul_add_div s.suff_pos,
    Nat.div_eq_of_lt (Nat.mod_lt n s.suff_pos),Nat.add_zero,Nat.mul_add_mod,Nat.mod_mod]

end SwapWord

namespace Route
open XorBits SwapWord

private theorem axis_as_xors {a h : ℕ} (i j : Fin (a+1)) (ne : i ≠ j) (x : Addr (a+1) h) :
    axes (Equiv.swap i j) x = xorColumn (j,i) ∘ xorColumn (i,j) ∘ xorColumn (j,i) ∘ x := by
  funext t k b
  by_cases hi : k=i
  · subst k
    simp [axes,Function.comp_apply,xorColumn,ne,ne.symm]
    generalize x t i b = u,x t j b = v
    fin_cases u <;> fin_cases v <;> rfl
  by_cases hj : k=j
  · subst k
    simp [axes,Function.comp_apply,xorColumn,ne,ne.symm]
    generalize x t i b = u,x t j b = v
    fin_cases u <;> fin_cases v <;> rfl
  simp [axes,Equiv.swap_apply_of_ne_of_ne hi hj,Function.comp_apply,xorColumn,hi,hj]

/-- The physical descriptor leaves the prefix and low spectator fixed. For
ordered slot offsets its action is exactly the five-field floor/mod formula. -/
theorem key_swap {a : ℕ} (i j : Fin (a+1)) (ne : i ≠ j) (s : Shape) (n : ℕ)
    (apart : offset (grow (a+1) (s.level-1)) i + grow (a+1) (s.level-1) ≤ offset (grow (a+1) (s.level-1)) j) :
    let L := grow (a+1) (s.level-1)
    key s (axes (Equiv.swap i j)) n = stride s (SwapWord.run (offset L i) (offset L j) L) n := by
  intro L
  let xorKey := fun g : Fin (a+1) × Fin (a+1) => fun u : Active a s => xorColumn g ∘ u
  have split : key s (axes (Equiv.swap i j)) n = key s (xorKey (j,i))
      (key s (xorKey (i,j)) (key s (xorKey (j,i)) n)) := by
    simp only [key_comp]
    apply congrArg (fun f => key s f n)
    funext u
    exact axis_as_xors i j ne u
  rw [split]
  change xorIndex a (j,i) s (xorIndex a (i,j) s (xorIndex a (j,i) s n)) = _
  simp only [xorIndex_eq (j,i) ne.symm,xorIndex_eq (i,j) ne]
  change stride s (window (offset L i) (offset L j) L) (stride s (window (offset L j) (offset L i) L)
    (stride s (window (offset L i) (offset L j) L) n)) = _
  rw [stride_comp,stride_comp]
  exact congrArg (fun f => stride s f n) (funext fun q => three_xor _ _ _ q apart)

end Route
end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
