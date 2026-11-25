import OAI.Computability.BorderVNP.DiagonalSupportedPostRate
import OAI.Computability.BorderVNP.DiagonalChosenSignedCalendar

/-! # The two signed post-call bounds used at an admitted calendar length -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing Cover Packing PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open VPVNP TeamScales Filter DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins RoutingISA.SignedTaskArena
open scoped Classical

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {S : SiteSchedule paid} (cube : FixedCube K) {extra E dlog Q A B j : ℕ}
    {scales : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} scales (E+1) dlog Q A B j)
    (φ : K →+* F) (q : ℕ) (adv : ℕ → ℕ) (c charge : ℕ)

/-- The original parameter exponent slots and the complete positive reader fit
one batch at this length, simultaneously for every admissible chart. -/
def CalendarPostRateAt (n : ℕ) : Prop :=
  ∀ l, n=l+1 →
    let r := stretch b.ρ n
    let teams := b.physical.teamsPred n+1
    let w := b.physical.word n
    let limit := adv (adviceScale b.σ b.ρ n)
    ∀ {size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
      {common : CommonField paid (φ ∘ cube.table) q l size ord} (chart : AdvisedBranch common)
      [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
      (reader : ChosenReader chart teams r w w w (limit+6)), reader.charge≤c*(limit+1)^charge →
      let par := pairedTableParameters (l+1) size
      let scalars := Fintype.card (paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
      teams*(par*Nat.clog 2 (r*(2*l+1)+1))≤r ∧
        512*(teams+1)*(par+scalars+1)*(w+1)+(7+reader.charge)≤r

/-- The uniform post-call estimates of the signed scheduler impose a single
length cutoff before the finite-field reader or its positive prefix is chosen. -/
theorem JointSchedule.eventually_calendar_post_rate (growth : PolynomiallyBounded adv) :
    ∀ᶠ n : ℕ in atTop, CalendarPostRateAt cube b φ q adv c charge n := by
  filter_upwards [b.eventually_startup_post_rates (aux:=φ ∘ cube.table) (q:=q) cube adv growth c charge] with n fits
  intro l index r teams w limit size ord common chart _ _ reader charged par scalars
  exact fits l index chart reader charged 0 0 0 0 0 0 0 0 0 0 (cube.cubeID paid) ⟨0,0,0,0,0⟩

end Diagonal

end BorderVNP
end Computability
end OAI
