import OAI.Hierarchy.TraceRegisteredPinFloor

namespace OAI
/-! # Total and peak archived work of the registered physical run -/

noncomputable section
namespace Hierarchy.TraceDistribution.Physical

open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open Filter Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Topology

variable {F Pins : Type} [Field F] [Fintype F] (B : Block F)

omit [Fintype F] in
/-- Total and largest charged words on the exact recast cursor run used by
the trace distribution. The starting seed and the rows may have different
prices inside their common bucket bound. -/
theorem registered_bounds {u s : ℕ → ℕ} (scale : Scale u s) (a b rate degree : ℕ) (pos : 0<a) :
    ∀ᶠ w : ℕ in atTop, ∀ (Pins : Type) {k : ℕ} (rem low offsets slots unitWork : ℕ)
      (e : k=(B.repeat (s w)).charge+rem) (hk : 2≤k),
      k≤2*(w+1) → k+low≤u w+1 → s w≤w → low≤w/2 →
      offsets*slots*3≤a*(w+1)^b → unitWork≤rate*(w+1)^degree →
      let X := B.cursorState hk low offsets slots
      let R := Program.recast e X ((B.repeat (s w)).run rem (e ▸ X))
      let reg := registerOnLanes B Pins (s w) rem X e
      ∀ (h : R.plan.History) (start : X.Site → ℕ), (∀ v,start v≤2^low*(a*(w+1)^b)) →
        (∑ v,publishedWork R h reg.2 start unitWork v) ≤
          2^(u w)*(rate*(4*a*⌈scanRate B⌉₊))*(w+1)^(degree+(b+2)) ∧
        ∀ v,publishedWork R h reg.2 start unitWork v ≤ 2^(3*w/5) := by
  filter_upwards [published_peak_room B scale a b rate degree pos] with w peak
  intro Pins k rem low offsets slots unitWork e hk axes round blocks small slot tariff
  subst k
  intro X R reg h start seeds
  have width : X.maxWidth≤2^low*(a*(w+1)^b) := X.maxWidth_le fun z=>by
    rw [B.cursorState_width]
    exact Nat.mul_le_mul_left _ slot
  constructor
  · rw [publishedWork_sum]
    have raw := cursor_scan_volume B hk pos axes round blocks slot h start seeds
    exact (Nat.mul_le_mul tariff raw).trans_eq (by rw [pow_add (w+1) degree (b+2)]; ac_rfl)
  · exact peak rem low unitWork X h start small tariff width seeds


end Hierarchy.TraceDistribution.Physical

end
end OAI
