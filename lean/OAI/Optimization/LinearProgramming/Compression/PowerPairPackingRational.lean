import OAI.Optimization.LinearProgramming.Compression.PowerPairPackingRun
import OAI.Optimization.LinearProgramming.Compression.ScalarPowerToken
import OAI.Optimization.LinearProgramming.Compression.ProxyRegisterBits

/-! Instantiation of the total pair preparation algorithm with the native
rational-scalar-to-binary compiler and an explicit register bit bound. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

theorem rationalPowerTokenEmitter {w : ℕ} {P : ℚ → Prop}
    (closed : ∀ v : ℕ, v ≤ 2^(2*w+2) → P (v : ℚ)) :
    PowerTokenEmitterSpec scalarExponentTokenBlock w P := by
  intro m x base out hm hx hb ho hbase hout hw
  exact scalarExponentTokenBlock_spec m x w base out hm hx hb ho hbase hout hw closed

theorem rationalPowerPairsBlock_spec (xs : List ℚ) (es : List ℤ) (m : Memory ℚ)
    (w B scratch src dst expSrc tokenStart : ℕ) (hm : m.AllData (fun q => ratBits q ≤ B))
    (hlen : xs.length = es.length) (h2 : m.index 2 = scratch) (h50 : m.index 50 = es.length)
    (h51 : m.index 51 = src) (h52 : m.index 52 = expSrc) (h55 : m.index 55 = dst)
    (h59 : m.index 59 = tokenStart) (hb : 41 < scratch) (hs : 64 ≤ src)
    (hd : 64 ≤ dst) (he : 64 ≤ expSrc) (hspace : 64+2*(es.length*(w+2))+8 ≤ tokenStart)
    (hse : expSrc+es.length ≤ scratch ∨ scratch+w ≤ expSrc)
    (hss : src+xs.length ≤ scratch ∨ scratch+w ≤ src)
    (hsd : src+xs.length ≤ dst ∨ dst+4+xs.length ≤ src)
    (bases : ∀ i, ∀ hi : i < xs.length, m.data (src+i) = xs[i])
    (exponents : ∀ i, ∀ hi : i < es.length, m.data (expSrc+i) = (es[i] : ℚ))
    (width : ∀ x ∈ es, x.natAbs < 2^w) :
    ∃ t k, k ≤ (w*(16*w+32)+37)*es.length+12*(es.length*(w+2))+7*es.length+51 ∧
      Block.Eval (Memory.AllData (fun q => ratBits q ≤ max B (2*w+5)))
        (packPowerPairsBlock scalarExponentTokenBlock) m k t ∧
      PowerPairsReady xs es dst (tokenStart-(2*(signedBitTape es).length+8)) m t ∧
      (∀ i, 6 ≤ i → i ≠ 40 → i ≠ 41 → (i < scratch ∨ scratch+w ≤ i) →
        (i < dst ∨ dst+(powerPairScalarWords xs).length ≤ i) → t.data i = m.data i) ∧
      ∀ i, 43 ≤ i → i ≠ 52 → i ≠ 54 → i ≠ 56 → i ≠ 57 → i ≠ 58 →
        (i < tokenStart-(2*(signedBitTape es).length+8) ∨ tokenStart+(signedBitTape es).length ≤ i) →
        t.index i = m.index i := by
  let P := fun q => ratBits q ≤ max B (2*w+5)
  have closed (v : ℕ) (hv : v ≤ 2^(2*w+2)) : P (v:ℚ) :=
    (natCast_ratBits_le hv).trans (le_max_right _ _)
  have zero : P 0 := by simpa using closed 0 (Nat.zero_le _)
  have one : P 1 := by simpa using closed 1 (Nat.one_le_pow _ _ (by decide))
  exact packPowerPairsBlock_spec (rationalPowerTokenEmitter closed) xs es m scratch src dst expSrc tokenStart
    (fun i => (hm i).trans (le_max_left _ _)) zero one hlen h2 h50 h51 h52 h55 h59 hb hs hd he hspace
    hse hss hsd bases exponents width

end Compression
end LinearProgramming
end Optimization
end OAI
