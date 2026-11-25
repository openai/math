import OAI.Hierarchy.TracePhysicalTileCaps
import OAI.ThreeFlat.Diagonal.TraceFactorPins
import OAI.Hierarchy.TraceFactorHeight
import OAI.Hierarchy.TracePhysicalCharges
import OAI.ThreeFlat.Diagonal.PhysicalProgramFreshPrices

namespace OAI
/-! # Fresh resources of the physical cursor at the native clock

The block has finitely many fixed tiles. Their digit widths eventually fit the
native clock's sorter bound, uniformly in the number of repeated passes. The
actual terminal-charge estimate then bounds every intermediate successor.
-/

noncomputable section
namespace Hierarchy.TraceDistribution.Physical

open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open Filter Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Topology

variable {F Pins : Type} [Field F] [Fintype F] (B : PhysicalStage.Block F)

omit [Fintype F] in
/-- The sorter price is polynomial in the native clock even when the
repetition count and the number of lanes use a different schedule. -/
theorem repeated_fresh_prices :
    ∀ᶠ w : ℕ in atTop, ∀ (n rem : ℕ)
      (A : State (2^(B.exponent 0)) ((B.repeat n).charge+rem)),
      let P := B.repeat n
      let R := P.run rem A
      ∀ (h : R.plan.History) (start : A.Site → ℕ),
        (∀ v, R.chargeAt h (B.charges n rem A) start v ≤ 2^(3*w/5)) →
        R.FreshPath (B.localCoefficient*(16*w^10+1)^3) h
          ((P.assembly rem A : R.Assembler Pins).steps) (B.charges n rem A) start := by
  filter_upwards [fixed_tile_caps B] with w tiles
  intro n rem A P R h start peak
  have shrink : 3*w/5 ≤ w := by omega
  have cap : 2^(3*w/5) ≤ 2^(w^10) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (shrink.trans (Nat.le_self_pow (by decide : (10:ℕ)≠0) w))
  have room : R.LevelsCapped 1 (2^(w^10)) h (B.charges n rem A) start := by
    apply R.levels_capped_of_terminal
    intro v
    simpa only [Nat.mul_one] using (peak v).trans cap
  exact B.program_fresh_path (Pins:=Pins) w P (B.repeat_supported n) B.costFactors.sum
    (B.factor_bound n) rem A tiles.1 tiles.2 h start room

omit [Fintype F] in
/-- The same physical history and the same assembled factor have both the
local fresh-resource bound and a bounded-depth replay from genuine seed atoms. -/
theorem priced_atomic_terminal :
    ∀ᶠ w : ℕ in atTop, ∀ (n rem : ℕ)
      (A : State (2^(B.exponent 0)) ((B.repeat n).charge+rem)),
      let P := B.repeat n
      let R := P.run rem A
      ∀ (h : R.plan.History) (start : A.Site → ℕ)
        (L : A.Words Pins) (N : ∀ x, BitNetwork F (L.ports.form.width x)),
        (∀ v, R.chargeAt h (B.charges n rem A) start v ≤ 2^(3*w/5)) →
        R.FreshPath (B.localCoefficient*(16*w^10+1)^3) h
            ((P.assembly rem A : R.Assembler Pins).steps) (B.charges n rem A) start ∧
          ∀ v, Tree.Within (4+P.length)
            ((R.plan.assemble h ((P.assembly rem A : (P.run rem A).Assembler Pins) L) (fun x => Tree.atom (N x))).2 v) := by
  filter_upwards [repeated_fresh_prices (Pins:=Pins) B] with w price
  intro n rem A P R h start L N peak
  exact ⟨price n rem A h start peak, terminal_atomic_within P rem A L h N⟩

/-- The selected native cursor satisfies the actual fresh-resource certificate
using only its instruction-format and capacity hypotheses. -/
theorem native_fresh_prices {u s : ℕ → ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {pc regs words S base d fuel : ℕ}
      (M : Machine (64*w) pc regs words) (fit : NativeTrace.Fits M S base d fuel)
      (hF : Fintype.card F ≤ 2^(64*w)) (st : Word (64*w)) (rem low : ℕ)
      (hk : 2 ≤ (B.repeat (s w)).charge+rem) (_q : Fintype.card F ≤ 64*w) (_p : pc ≤ 64*w)
      (_r : regs ≤ 64*w) (_a : words ≤ 64*w) (_depth : d ≤ 64*w),
      let grid := TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs words d
      let desc := TraceSourceOwner.shape (64*w) pc regs words S fuel d grid.internal
      let A := B.cursorState hk low (1+(d+d)) grid.cells
      let P := B.repeat (s w)
      let R := P.run rem A
      ∀ (h : R.plan.History) (active : A.Site → Bool) (pairs : A.Site → ℕ),
        low ≤ w/2 → (∀ v, pairs v ≤ 2^low) →
        R.FreshPath (B.localCoefficient*(16*w^10+1)^3) h
          ((P.assembly rem A : R.Assembler Pins).steps) (B.charges (s w) rem A)
          (fun x => 1+(A.incidentWidth x+(if active x then
            pairs x+TraceBitHeader.seedTraceWork low desc.stride grid.cells B.cursorCopies d else 0))) := by
  filter_upwards [repeated_fresh_prices (Pins:=Pins) B, native_published_peak B scale 1 0] with w priced cap
  intro pc regs words S base d fuel M fit hF st rem low hk q p r a depth grid desc A P R h active pairs lowBound clipped
  apply priced (s w) rem A h
  have per := cap M fit hF st rem low hk q p r a depth h active pairs 1 lowBound (by simp) clipped
  simpa only [publishedWork, Nat.one_mul] using per

end Hierarchy.TraceDistribution.Physical

end
end OAI
