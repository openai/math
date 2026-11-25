import OAI.Optimization.LinearProgramming.Compression.ProxyPrepared
import OAI.Optimization.LinearProgramming.Compression.ComputedProxyOperands
import OAI.Optimization.LinearProgramming.Compression.ProxyRegisterBits

/-! The source-order selected scalar operands agree with the canonical finite-index
operand list. Every exponent is small enough for the counted signed-token writer. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM
open scoped BigOperators

/-- The numerical index order used by the compaction scan is the order of the
canonical finite-index minor query. -/
theorem canonicalProxyPowerOperands_range (n fuel prec : ℕ) (offset : ℤ) (D : ℕ)
    (a : ℕ → ℤ) (mag : ℕ → ℚ) :
    proxyPowerOperands ((List.range n).filter (fun i => (logProxyNumerator fuel prec (mag i)).isNone))
        offset D a mag =
      proxyPowerOperands (proxyLargeIndices fuel prec (fun i : Fin n => mag i))
        offset D (fun i : Fin n => a i) (fun i : Fin n => mag i) := by
  have hr : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem <;> simp
  unfold proxyPowerOperands proxyLargeIndices
  rw [← hr,List.filter_map]
  exact congrArg (List.cons ((2 : ℚ),offset)) List.map_map

@[simp] theorem proxyLargeIndices_toFinset {n : ℕ} (fuel prec : ℕ) (mag : Fin n → ℚ) :
    (proxyLargeIndices fuel prec mag).toFinset =
      Finset.univ.filter (fun i => logProxyNumerator fuel prec (mag i) = none) := by
  ext i
  simp [mem_proxyLargeIndices]

private theorem intCast_bits_of_natAbs_le_pow {u : ℤ} {e : ℕ} (h : u.natAbs ≤ 2^e) :
    ratBits (u : ℚ) ≤ e+3 := by
  have eq : ratBits (u : ℚ) = ratBits (u.natAbs : ℚ) := by
    simp only [ratBits,Rat.num_intCast,Rat.den_intCast,Rat.num_natCast,Rat.den_natCast,Int.natAbs_natCast]
  rw [eq]
  exact natCast_ratBits_le h

/-- Both the first constant and the full set of selected exponents can be handed
to the native signed-integer writer with width `2*fuel+3`. The other two bounds
cover the rational scalar registers written before that conversion. -/
theorem canonicalProxyPowerOperands_width {n : ℕ} (fuel prec : ℕ) {A : ℤ} (c : ℤ)
    (a : Fin n → ℤ) (mag : Fin n → ℚ) (hm : ∀ i, 0<mag i)
    (hform : |c| + ∑ i, |a i| ≤ A) (hcut : (2:ℤ)^prec*A ≤ 2^fuel) :
    let indices := proxyLargeIndices fuel prec mag
    let D := (2:ℕ)^(prec+2)
    let grid i := (logProxyNumerator fuel prec (mag i)).getD 0
    let offset := clearedProxyOffset indices.toFinset D c a grid
    let ps := proxyPowerOperands indices offset D a mag
    (∀ e ∈ ps.map Prod.snd, e.natAbs < 2^(2*fuel+3)) ∧
      (∀ i, ratBits (((D:ℤ)*a i:ℤ):ℚ) ≤ fuel+5) ∧
      ratBits (offset:ℚ) ≤ 2*fuel+5 := by
  let indices := proxyLargeIndices fuel prec mag
  let D := (2:ℕ)^(prec+2)
  let grid i := (logProxyNumerator fuel prec (mag i)).getD 0
  let offset := clearedProxyOffset indices.toFinset D c a grid
  obtain ⟨ho,he⟩ := logProxy_exponent_natAbs_le fuel prec c a mag hm hform hcut
  have hoff : offset.natAbs ≤ 2^(2*fuel+2) := by
    simpa only [offset,indices,proxyLargeIndices_toFinset,D,grid] using ho
  constructor
  · intro e h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h
    change p ∈ (2,offset) :: indices.map (fun i => (mag i,(D:ℤ)*a i)) at hp
    rcases List.mem_cons.mp hp with hp | hp
    · subst p
      exact hoff.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
      exact (he i).trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  · constructor
    · intro i
      exact intCast_bits_of_natAbs_le_pow (he i)
    · exact intCast_bits_of_natAbs_le_pow hoff

end Compression
end LinearProgramming
end Optimization
end OAI
