import OAI.ThreeFlat.Routing.StableBitCompaction
import OAI.ThreeFlat.Routing.StableCompactionPadRows

namespace OAI
/-! # Stable compaction for arbitrary row counts -/

namespace ThreeFlat.Routing.StableCompaction

/-- Fix the extra mask, source, and output pins of the dyadic stable compactor to zero. -/
noncomputable def paddedNetwork (K : Type*) [Zero K] [One K] (n m : ℕ) (_h : n ≤ 2^m) :
    BitNetwork K (n + (n+n)) :=
  restrictRows (network K m) n

theorem paddedNetwork_eval {K : Type*} [CommSemiring K] (n m : ℕ) (h : n ≤ 2^m)
    (M X Y : Fin n → Bool) :
    (paddedNetwork K n m h).eval (Fin.append M (Fin.append X Y)) =
      if Y = compact M X then 1 else 0 :=
  restrictRows_eval h _ (network_eval m) M X Y

theorem paddedNetwork_cells (K : Type*) [Zero K] [One K] (n m : ℕ) (h : n ≤ 2^m) :
    (paddedNetwork K n m h).cells ≤ 16384 * 2^m * (m+1)^3 :=
  network_cells K m

theorem paddedNetwork_internal (K : Type*) [Zero K] [One K] (n m : ℕ) (h : n ≤ 2^m) :
    (paddedNetwork K n m h).internal ≤ 16384 * 2^m * (m+1)^3 :=
  network_internal K m


end ThreeFlat.Routing.StableCompaction

end OAI
