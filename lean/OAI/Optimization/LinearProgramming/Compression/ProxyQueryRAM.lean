import OAI.Optimization.LinearProgramming.Compression.ProxyPrepared
import OAI.Optimization.LinearProgramming.Compression.ProxyLiteralMachine
import OAI.Optimization.LinearProgramming.Compression.SmallProxyRAM
import OAI.Optimization.LinearProgramming.Compression.ComparisonDispatch

/-! A single fixed RAM for the sign of any prepared minor-log query. The term universe
is the supplied short list, so the dispatcher never enumerates the universe of minors. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM
open scoped BigOperators

/-- One fixed program, independent of dimensions, precision, magnitudes, and branch. -/
def proxySignProgram : Program := comparisonDispatchProgram smallAffineProgram literalPowerCompareProgram

def proxyQuerySteps (n fuel : ℕ) : ℕ :=
  max (9*(n+1)+6) (30*(2*(2*fuel+3)+3+n*(2*(fuel+3)+3))+9)

def proxyQueryBits (n fuel prec B : ℕ) : ℕ :=
  max (3+2*((n+2)+(2*(n+1)+3)*(prec+2+fuel+1))) (10+16*B^2+n*(3+(4*B+1)*B))

/-- A native caller may enter either physical comparison routine directly after preparing its raw tapes. -/
theorem proxySignBranch_correct {n : ℕ} (fuel prec B : ℕ) {A : ℤ}
    (c : ℤ) (a : Fin n → ℤ) (mag : Fin n → ℚ)
    (hm : ∀ i, 0 < mag i) (hbits : ∀ i, ratBits (mag i) ≤ B)
    (hform : |c| + ∑ i, |a i| ≤ A) (hcut : (2 : ℤ)^prec * A ≤ 2^fuel) :
    let p := preparedProxyQuery fuel prec c a mag
    let form := (c : ℝ) + ∑ i, (a i : ℝ) * logProxyValue prec (mag i)
      (logProxyNumerator fuel prec (mag i))
    ∃ k ≤ proxyQuerySteps n fuel, ∃ tr : Fin (k+1) → State ℚ,
      Trace (if p.symbolic then literalPowerCompareProgram else smallAffineProgram)
        (start p.address p.scalar) k tr ∧
      (tr (Fin.last k)).output = some (if form < 0 then 0 else if 0 < form then 2 else 1) ∧
      ∀ i, scalarBound (proxyQueryBits n fuel prec B) (tr i) := by
  classical
  let p := preparedProxyQuery fuel prec c a mag
  by_cases hnil : proxyLargeIndices fuel prec mag = []
  · have hsmall := (proxyLargeIndices_empty_iff fuel prec mag).mp hnil
    obtain ⟨k,hk,tr,ht,ho,_,hs⟩ := computedSmallProxyRAM_correct fuel prec c a mag hm hform hcut hsmall
    refine ⟨k,hk.trans (le_max_left _ _),tr,?_,ho,?_⟩
    · simpa [p,preparedProxyQuery,hnil] using ht
    · exact fun i j => (hs i j).trans (le_max_left _ _)
  · have hsym : ∃ i, logProxyNumerator fuel prec (mag i) = none := by
      by_contra! h
      exact hnil ((proxyLargeIndices_empty_iff fuel prec mag).mpr h)
    have heq : (proxyLargeIndices fuel prec mag).toFinset =
        Finset.univ.filter fun i => logProxyNumerator fuel prec (mag i) = none := by
      ext i
      simp [mem_proxyLargeIndices]
    obtain ⟨k,hk,tr,ht,_,ho,hs⟩ := computedProxyLiteralRAM_correct fuel prec B c a mag hm hbits
      hform hcut hsym (proxyLargeIndices fuel prec mag) (proxyLargeIndices_perm fuel prec mag)
    have hk' : k ≤ 30*(2*(2*fuel+3)+3+n*(2*(fuel+3)+3))+9 := by
      simpa only [Fintype.card_fin] using hk
    refine ⟨k,hk'.trans (le_max_right _ _),tr,?_,ho,?_⟩
    · simpa [p,preparedProxyQuery,hnil,heq] using ht
    · intro i j
      have h := hs i j
      rw [Fintype.card_fin] at h
      exact h.trans (le_max_right _ _)

/-- The exact sign of one common real proxy assignment is the program's actual halt
tag. The time is polynomial in the number of query terms and the logarithm of the
cutoff; the separate bit bound holds in every state of both paths. -/
theorem proxySignProgram_correct {n : ℕ} (fuel prec B : ℕ) {A : ℤ}
    (c : ℤ) (a : Fin n → ℤ) (mag : Fin n → ℚ)
    (hm : ∀ i, 0 < mag i) (hbits : ∀ i, ratBits (mag i) ≤ B)
    (hform : |c| + ∑ i, |a i| ≤ A) (hcut : (2 : ℤ)^prec * A ≤ 2^fuel) :
    let p := preparedProxyQuery fuel prec c a mag
    let form := (c : ℝ) + ∑ i, (a i : ℝ) * logProxyValue prec (mag i)
      (logProxyNumerator fuel prec (mag i))
    ∃ k ≤ 2 * proxyQuerySteps n fuel + 2, ∃ tr : Fin (k+1) → State ℚ,
      Trace proxySignProgram (start (dispatchDims p.symbolic p.address) (dispatchScalars p.scalar)) k tr ∧
      (tr (Fin.last k)).output = some (if form < 0 then 0 else if 0 < form then 2 else 1) ∧
      ∀ i, scalarBound (proxyQueryBits n fuel prec B) (tr i) := by
  classical
  let p := preparedProxyQuery fuel prec c a mag
  let form := (c : ℝ) + ∑ i, (a i : ℝ) * logProxyValue prec (mag i)
    (logProxyNumerator fuel prec (mag i))
  let tag := if form < 0 then 0 else if 0 < form then 2 else 1
  obtain ⟨k,hk,tr,ht,ho,hs⟩ := proxySignBranch_correct fuel prec B c a mag hm hbits hform hcut
  have htag : tag < 3 := by dsimp only [tag]; split_ifs <;> decide
  obtain ⟨l,hl,u,hu,hout,_,_,hsafe⟩ := comparisonDispatch_trace smallAffineProgram
    literalPowerCompareProgram p.symbolic p.address p.scalar tr htag ht ho hs
  exact ⟨l,hl.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hk) 2),u,hu,hout,hsafe⟩

end Compression
end LinearProgramming
end Optimization
end OAI
