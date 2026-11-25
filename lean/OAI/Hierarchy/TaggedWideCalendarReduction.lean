import OAI.Hierarchy.TaggedWideCalendarEndpointSteps
import OAI.Hierarchy.TaggedWideCalendarCompiler

namespace OAI
/-! # Width reduction from the complete chronological protocol -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage Tagged Tagged.WideStack TaggedShorterBudget Filter
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ : ℝ}

/-- The funded calendar supplies its finite scalar identities on every
purchased parent carrying the compiler's actual numerical bounds. -/
theorem funded_calendar_inputs (v : FixedProtocolFormat F k p q Q σ Λ) (u : ℝ→ℝ) (positive : 0<κ) :
    v.PricedCalendarInputs (A:=A) (δ:=δ) (ξ:=ξ) u positive := by
  intro m prices short C nonneg
  apply Filter.Eventually.of_forall
  intro x routeAge height partyWord terminal N cpu room control support groups metadata items ext perm rank tag date
  exact v.calendar_day (C:=C) m v.calendarLaneExponent short u δ ξ x cpu room control support
    routeAge prices positive.le groups metadata v.calendar_lanes items ext perm rank tag height partyWord date

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

namespace Hierarchy.Tagged
open ProtocolRAM.Calendar TaggedShorterBudget

/-- The native chronological compiler supplies both readout quantifiers
for every fixed protocol format selected by the dichotomy. -/
def protocol_calendar_readouts {F : Type} [Field F] {k : ℕ} (hk : 0<k)
    (missing : ¬HasSpectralFlat F (k+1)) : CofinalReadouts F k :=
  calendar_readouts hk missing (fun _ hκ _ _ v _=>v.funded_calendar_inputs _ hκ)

/-- The tagged width reductions use only positivity and the missing next
spectral flat over the original field. -/
theorem width_reductions {F : Type} [Field F] {k : ℕ} (hk : 0<k)
    (missing : ¬HasSpectralFlat F (k+1)) : WidthReductions F k :=
  let actual:=protocol_calendar_readouts hk missing
  widthReductions_of_protocol hk actual.protocols actual.readout

/-- The tagged matching predicate with logarithmic payload width is feasible
at every positive exponent under the missing-flat hypothesis. -/
theorem feasible_log_width {F : Type} [Field F] {k : ℕ} (hk : 0 < k)
    (missing : ¬HasSpectralFlat F (k+1)) {r : ℝ} (hr : 0 < r) :
    Feasible F k 1 r :=
  feasible_of_protocol_readout hk (protocol_calendar_readouts hk missing) hr

open Filter in
/-- At all sufficiently large heights, the same physical network realizes
the work bound and both exposed error gaps. -/
theorem cheap_log_width {F : Type} [Field F] {k : ℕ} (hk : 0 < k)
    (missing : ¬HasSpectralFlat F (k+1)) {r : ℝ} (hr : 0 < r) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ᶠ h : ℕ in atTop,
      ∃ X : Catalyst.Approximation F k (pins h h), (X.size : ℝ) ≤ A * work h h r ∧
        X.Gap (coeff F h h) (gap C h) ∧
        X.Gap (coeff F h h) ((2 : ℝ)^h * (2 : ℝ)^(-Real.sqrt h)) :=
  cheap_of_protocol_readout hk (protocol_calendar_readouts hk missing) hr

end Hierarchy.Tagged
end

end OAI
