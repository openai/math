import OAI.Computability.BorderVNP.DiagonalSelectedPhaseWindows
import OAI.Computability.BorderVNP.DiagonalFixedSignedSites
import OAI.Computability.BorderVNP.DiagonalEnrichedReaderBounds
import OAI.Computability.BorderVNP.DiagonalSelectedSchedule
import OAI.Computability.BorderVNP.PackedHistorySeedExecution
import OAI.Computability.BorderVNP.CellSparseExteriorBudget
import OAI.Computability.BorderVNP.PackedFrozenNativeSeed
import OAI.Computability.BorderVNP.PackedBankHookWordRoom
import OAI.Computability.BorderVNP.PackedInheritedWorkJointRange

/-! # A common calibration for the signed grid, sparse private calls and live field reader -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing Cover Epoch Packing TeamScales RoutingISA PackedHistoryCircuit.Normalized
open PackedHistoryCircuit.Normalized.SelectedSchedule VPVNP

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] (G : PaidIdentity F D m)

/-- The complete initial payload on this same physical grid fits the
half-power budget used to bound all scalar multiplicities in the reader. -/
theorem JointSchedule.eventually_signed_seed_mass {S : SiteSchedule G} {a extra E deg Q A B j : ℕ}
    {scales : EpochScales S a extra} (b : JointSchedule scales E deg Q A B j) (header : ℕ) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      1+initialMass (D:=D) n r (CoverScale.initialDepth (Cube D) r n-1) (width n scales.α) header ≤
        width n (1/2:ℝ) := by
  filter_upwards [b.eventually_programSeedStorage header,eventually_ge_atTop 1] with n paid hn
  let r := stretch b.ρ n
  let d := CoverScale.initialDepth (Cube D) r n-1
  let mass := initialMass (D:=D) n r d (width n scales.α) header
  let T := epochs scales.τ n
  have pos : 0 < S.publicProgramFactor^T := Nat.pow_pos (by
    unfold SiteSchedule.publicProgramFactor SiteSchedule.bankRecordFactor Epoch.Round.epochRecordFactor
    positivity)
  have old : mass ≤ S.publicProgramFactor^T*mass := Nat.le_mul_of_pos_left _ pos
  have fit : 7*(S.publicProgramFactor^T*mass) ≤ width n (1/5:ℝ) := paid.2.1
  have nonzero : 0 < mass := by
    have base (a b c : ℕ) : 0 < a+12+b+c := by omega
    exact base _ _ _
  have widen : width n (1/5:ℝ) ≤ width n (1/2:ℝ) :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))
  change 1+mass ≤ width n (1/2:ℝ)
  omega

/-- The actual grouped verifier before its private literals, coefficients and
raw input pins are filled. The start depth and copy count are chosen by the same
scales as the native processor. -/
def SignedSeedAt {S : SiteSchedule G} {a extra : ℕ} (scales : EpochScales S a extra)
    (hm : 0 < m) (header Q A a₀ B b₀ J j n r : ℕ) : Prop :=
  let d := CoverScale.initialDepth (Cube D) r n-1
  let T := epochs scales.τ n
  let copies := width n scales.α
  let w := 60*logWidth r n
  let mass := initialMass (D := D) n r d copies header
  ∃ plan : SeedPlan S n r d T copies header Q, ∃ wr : WidthRanges S (d+1) T w,
    EnrichedOuter.Machine.LocalSizes (r := r) (n := n) A a₀ B b₀ J j plan.compiled.machine ∧
    plan.TapeWithin S wr hm ∧ 2*(S.publicProgramFactor^T*mass) < 2^w ∧ Compiled.HookRoom S T w mass ∧
    1+mass ≤ width n (1/2:ℝ)

/-- Select the shortening, actual sparse interpreter and two stretch exponents
once. At every subsequent reader charge, one length threshold supplies the wired
seed, measured public compiler, sparse private clock, all numerical tally fields,
and the checked signed startup for every chart in the stated characteristic. -/
theorem exists_signed_seed_schedule (φ : K →+* F) (q : ℕ) (hm : 0 < m) (minimum : ℕ) :
    ∃ cube : FixedCube K, minimum ≤ cube.h*cube.b ∧
    ∃ S : SiteSchedule G, (∀ z ≥ S.floor, S.FitsLevels z ∧ S.HasLeaves z ∧ S.RunsEnriched.{1} z) ∧
    ∀ extra : ℕ, ∃ scales : EpochScales S (cube.pred+1) extra, ∃ C p : ℕ,
    ∀ header E d Q A T B j H R k phaseDegree routeK fixed finishCost readerCost : ℕ, ∃ A₀ a₀ B₀ b₀ J₀ j₀ : ℕ, ∀ limit : ℝ, 0 < limit →
    ∃ b : JointSchedule.{0} scales (E+1) (max d p) Q A B j, b.ω ≤ limit ∧
      ∀ (cut : ℕ) (f : ℕ → ℕ), PolynomiallyBounded f → ∀ c t : ℕ, ∀ᶠ n : ℕ in atTop,
        let r := stretch b.ρ n
        let time := scales.signedWindows phaseDegree routeK fixed finishCost readerCost n r
        LengthBudget b cut n ∧ selectedReceiptAt.{0,1} S scales C p n r ∧
        SignedSeedAt G scales hm header Q A₀ a₀ B₀ b₀ J₀ j₀ n r ∧ PrivateCellBudgetAt A T B j H R k n r ∧
        SparseExterior.PrivateCallsAt A T B j H R k n r ∧
        ReaderTallyInputsAt cube b n ∧ SignedSitesAt G cube b φ q f c t n ∧
        time.core+time.before+time.argumentsCalls+time.finish+time.reader ≤ ticks ((scales.τ:ℝ)/5) r n := by
  obtain ⟨cube,width,S,physical,choose⟩ := exists_selected_physical_schedule K G hm minimum
  refine ⟨cube,width,S,physical,?_⟩
  intro extra
  obtain ⟨scales,C,p,batches⟩ := choose extra
  refine ⟨scales,C,p,?_⟩
  intro header E d Q A T B j H R k phaseDegree routeK fixed finishCost readerCost
  obtain ⟨A₀,a₀,B₀,b₀,J₀,j₀,v,hv,seeds⟩ := eventually_native_seed S hm scales physical header Q
  refine ⟨A₀,a₀,B₀,b₀,J₀,j₀,?_⟩
  intro limit pos
  obtain ⟨z,hz,hooks⟩ := eventually_calibrated_hook_word_room S scales (Nat.succ_pos _) header
  obtain ⟨y,hy,phases⟩ := scales.signed_clock_range phaseDegree routeK fixed finishCost readerCost (Nat.succ_pos _)
  obtain ⟨u,hu,calls⟩ := SparseExterior.eventually_private_cell A T B j H R k
  have hp : AdmissibleRange u (SparseExterior.PrivateCallsAt A T B j H R k) := by
    filter_upwards [calls] with n all
    intro r hr small M E w p U
    exact all r M E w p U hr small
  obtain ⟨b,cap,_,_,lengths⟩ := batches E d Q A T B j H R k (min limit (min u (min v (min z y))))
    (lt_min pos (lt_min hu (lt_min hv (lt_min hz hy))))
  have bounds : b.ω ≤ limit ∧ b.ω ≤ u ∧ b.ω ≤ v ∧ b.ω ≤ z ∧ b.ω ≤ y := by
    simpa only [le_min_iff] using cap
  obtain ⟨lim,process,seed,hookFit,phaseFit⟩ := bounds
  refine ⟨b,lim,?_⟩
  intro cut f hf c t
  have call := (hp.shrink process).stretched b.rho_omega.le
  have windows := (phases.shrink phaseFit).stretched b.rho_omega.le
  obtain ⟨N,native⟩ := eventually_atTop.1 (b.eventually_fixed_signed_sites G cube φ q f hf c t)
  filter_upwards [lengths cut,seeds,hooks,b.eventually_inheritedWidthInputs header,b.eventually_signed_seed_mass G header,call,
    b.eventually_reader_tally_inputs cube,windows,eventually_ge_atTop (N+1)] with n measured init hook widths mass driver digits times hn
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let r := stretch b.ρ (l+1)
  have grow (a : ℝ) (ha : b.ω ≤ a) : (r : ℝ) ≤ 2^(((l+1 : ℕ):ℝ)^a) := by
    apply (Nat.floor_le (by positivity : 0 ≤ (2 : ℝ)^(((l+1 : ℕ):ℝ)^b.ρ))).trans
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos l) (b.rho_omega.le.trans ha))
  obtain ⟨plan,wr,localSize,tape⟩ := init r (stretch_one ..) (grow v seed)
  let depth := CoverScale.initialDepth (Cube D) r (l+1)-1
  have hd : depth+1 = CoverScale.initialDepth (Fin (Fintype.card (Cube D))) r (l+1) := by
    simp [depth,CoverScale.initialDepth,CoverScale.factor,CoverScale.sites]
  have address := hook r (stretch_one ..) (grow z hookFit) depth hd
  exact ⟨measured.1,measured.2.1,⟨plan,wr,localSize,tape,widths.2,(fun t ht i => (address t ht i).1),mass⟩,
    measured.2.2,driver,digits,native l (by omega),times⟩

end Diagonal

end BorderVNP
end Computability
end OAI
