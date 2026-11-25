import OAI.Computability.BorderVNP.DiagonalJointReader
import OAI.Computability.BorderVNP.PackedHistoryPrefixBudget

/-! # The chosen reader and the reserved geometry circuit on the same team clock -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Branch Crossing VPVNP BurstRAM TeamScales TeamContraction TeamContraction.ProcessorSlots RoutingISA
open PackedHistoryCircuit.Normalized
open scoped Classical

universe u
variable {D m : ℕ} [NeZero D] {F : Type} [Field F] {e : PaidIdentity F D m} {S : SiteSchedule e}
    {a extra E dlog Q A B j : ℕ} {s : EpochScales S a extra}
    {ι : Type} [Fintype ι] {aux : ι → F} {q : ℕ}

private theorem eventually_exterior_ticks {ξ : ℝ} (positive : 0 < ξ) (factor : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, factor*exterior ξ r n ≤ ticks ξ r n := by
  filter_upwards [eventually_rpow_gap (show 1-ξ < 1-ξ/2 by linarith) factor] with n bound
  intro r
  apply Nat.le_floor
  have low := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) (1-ξ))
  change ((width n (1-ξ)):ℝ) ≤ _ at low
  simp only [exterior,Nat.cast_mul]
  calc
    _ = (r:ℝ)*((factor:ℝ)*(width n (1-ξ):ℝ)) := by ring
    _ ≤ (r:ℝ)*((factor:ℝ)*(n:ℝ)^(1-ξ)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg r)

/-- Any fixed share of the team clock pays for the real signed reader boot,
all broadcast comparisons, the full team pin scan and the geometry interpreter.
The measured geometry time includes the reserved, physically lowered gates. -/
theorem JointSchedule.eventually_signed_profile_clock (b : JointSchedule.{u} s (E+1) dlog Q A B j)
    (adv : ℕ → ℕ) (poly : PolynomiallyBounded adv) (c k factor : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let W := b.physical.word n
      let R := b.physical.teamsPred n+1
      let T := adv (adviceScale b.σ b.ρ n)
      let ξ := (s.τ:ℝ)/5
      ∀ {l size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
        {common : CommonField e aux q l size ord} (chart : AdvisedBranch common)
        [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
        (reader : ChosenReader chart R r (b.physical.multBits n) (b.physical.tally n) W (T+6)),
        reader.charge ≤ c*(T+1)^k →
        ∀ (loc : ReaderPlacement W) (f : BroadcastFrame) (frame geometry : ℕ), f.Fits W frame →
          f.processors = r → f.teams = R → f.link = link ξ R n →
          geometry ≤ r*width n (95/100:ℝ) →
          let p := reader.packetAt loc
          factor*(jointBudget p.bits.length W+f.readTicks+2+((pinSetup.slots+17*(r*literal s.α n)+1)+geometry)) ≤
            ticks ξ r n := by
  have hα : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have hτ : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have gap : (s.τ:ℝ)/5 < (s.α:ℝ)/3 := by linarith [s.tau_small]
  filter_upwards [b.physical.eventually_nativePackets (G := e) (aux := aux) (q := q) adv poly c k 1,
    eventually_literals_le gap 17,eventually_exterior_ticks (show 0 < (s.τ:ℝ)/5 by positivity) (500*factor),
    eventually_ge_atTop 1] with n packets lits time hn
  intro r W R T ξ l size ord common chart _ _ reader charge loc f frame geometry fit procs teams peer geo p
  have jp := packets chart reader charge loc.valuation loc.entry loc.row loc.column loc.totals loc.extension
  change 1*(p.bits.length+jointBudget p.bits.length W+_+1+_) < r at jp
  have read := f.readTicks_le_exterior fit ξ n (teams ▸ peer)
  rw [procs,teams] at read
  have positive : 0 < link ξ R n := peer ▸ fit.width
  have count : R ≤ width n (1-ξ) := (Nat.div_pos_iff.mp positive).2
  have hr : 1 ≤ r := stretch_one ..
  have xr : r ≤ exterior ξ r n := Nat.le_mul_of_pos_right _ (by have : 1 ≤ R := Nat.succ_pos _; omega)
  have xt : R ≤ exterior ξ r n := count.trans (Nat.le_mul_of_pos_left _ hr)
  have once : 17*(r*literal s.α n) ≤ exterior ξ r n := by rw [← Nat.mul_assoc]; exact lits r
  have wg : width n (95/100:ℝ) ≤ width n (1-ξ) := Nat.floor_mono
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : 1 ≤ (n:ℝ))
      (by dsimp only [ξ]; linarith [s.tau_small,s.alpha_small]))
  have gc : geometry ≤ exterior ξ r n := geo.trans (Nat.mul_le_mul_left r wg)
  have fixed : pinSetup.slots ≤ 100 := by decide
  have bound : jointBudget p.bits.length W+f.readTicks+2+((pinSetup.slots+17*(r*literal s.α n)+1)+geometry)
      ≤ 500*exterior ξ r n := by omega
  calc
    _ ≤ factor*(500*exterior ξ r n) := Nat.mul_le_mul_left factor bound
    _ = (500*factor)*exterior ξ r n := by ring
    _ ≤ _ := time r

end Diagonal

end BorderVNP
end Computability
end OAI
