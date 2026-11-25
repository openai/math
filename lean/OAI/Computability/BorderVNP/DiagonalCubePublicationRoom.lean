import OAI.Computability.BorderVNP.DiagonalCubeStartupWorkspace
import OAI.Computability.BorderVNP.CubeTeamOwnedGeometryWords

/-! # Actual optimizer scores and compact directory words at the joint schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing Cover Packing PackedHistoryCircuit.Normalized
open PackedHistoryCircuit.Normalized.SelectedSchedule TeamContraction.ProcessorSlots
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {a extra E dlog Q A B j : ℕ} {s : EpochScales S a extra}

/-- A single selected logarithmic-power word pays the address field width
and the full squared logarithm of the native label arithmetic. -/
theorem JointSchedule.eventually_directory_word (b : JointSchedule.{u} s (E+1) dlog Q A B j) :
    ∀ᶠ n : ℕ in atTop, let L := logWidth (stretch b.ρ n) n
      16*(L+2) ≤ b.physical.word n ∧ L^2 ≤ b.physical.word n := by
  filter_upwards [eventually_ge_atTop (2^32),eventually_ge_atTop 1] with n large hn
  intro L
  let r := stretch b.ρ n
  have hr := stretch_one b.ρ n
  have lo : 32 ≤ L := by
    rw [show L = Nat.clog 2 (2*n*r) from Shortening.PublicCapacity.public_logWidth n r,
      ← Nat.clog_pow 2 32 (by decide)]
    exact Nat.clog_mono_right _ (large.trans ((show n ≤ 2*n by omega).trans (Nat.le_mul_of_pos_right _ hr)))
  have lower : 16*(L+2) ≤ L^2 := by
    have k := Nat.mul_le_mul_right L lo
    rw [pow_two]
    omega
  have square : L^2 ≤ b.physical.word n :=
    Nat.pow_le_pow_right (by omega : 0 < L) (by omega : 2 ≤ (E+1)+1)
  exact ⟨lower.trans square,square⟩

/-- The true initial cover supplies at least one tile per processor, while
the number of inherited bundles never exceeds the physical team count. -/
theorem JointSchedule.eventually_directory_cover (b : JointSchedule.{u} s E dlog Q A B j) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let V := CoverScale.sites (Epoch.Cube D) (CoverScale.initialDepth (Epoch.Cube D) r n)
      r ≤ V ∧ V ≤ r*n ∧ (epochCopies S)^(epochs s.τ n) ≤ b.physical.teamsPred n+1 := by
  filter_upwards [b.eventually_lengths 0,eventually_rpow_gap (by norm_num : (0:ℝ) < 9/10)
    (CoverScale.factor (Epoch.Cube D)),eventually_ge_atTop 1] with n length cut hn
  intro r V
  rw [Real.rpow_zero,mul_one] at cut
  have fpos : (0:ℝ) < CoverScale.factor (Epoch.Cube D) := by
    exact_mod_cast zero_lt_one.trans (CoverScale.one_lt_factor (Epoch.Cube D))
  have low : (r:ℝ) ≤ V := ((le_div_iff₀ fpos).mpr (mul_le_mul_of_nonneg_left cut (by positivity))).trans
    length.cover.2.2.1.le
  have one : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have high := length.cover.2.2.2.1.trans (mul_le_mul_of_nonneg_left
    ((Real.rpow_le_rpow_of_exponent_le one (by norm_num : (9/10:ℝ) ≤ 1)).trans_eq (Real.rpow_one _)) (Nat.cast_nonneg r))
  have copies : 1 ≤ TeamScales.width n s.α := by
    have αpos : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
    apply Nat.le_floor
    simpa using Real.one_le_rpow one αpos.le
  refine ⟨by exact_mod_cast low,by exact_mod_cast high,?_⟩
  rw [(b.sizes hn).1]
  exact Nat.le_mul_of_pos_left _ copies

/-- The calibrated signed geometry bounds both the concrete packed label score
and every compact seven-word directory field. The size test here is the output
length of the actual geometry exporter. Its address bounds use the real final
cell and cable counts supplied to that exporter. -/
theorem JointSchedule.eventually_cube_publication_room {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s (E+1) dlog Q A B j) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let w := b.physical.word n
      let R := b.physical.teamsPred n+1
      let ξ := (s.τ:ℝ)/5
      let X := exterior ξ r n
      let V := CoverScale.sites (Epoch.Cube D) (CoverScale.initialDepth (Epoch.Cube D) r n)
      ∀ (dir : Directory.Layout) (slots wires base profile gates outputs width cables cells gap : ℕ),
        dir.DestinationBounds → dir.teams = R → dir.processors = r → dir.sites = V →
        dir.entries = (epochCopies S)^(epochs s.τ n)*V → dir.literal = literal s.α n →
        dir.link = TeamScales.link ξ R n → dir.block = blockWidth slots V →
        0 < slots → r*dir.literal ≤ slots → slots ≤ r*n → dir.description ≤ dir.literal/2 →
        dir.entries*dir.description ≤ dir.teams*r*(dir.literal/2) → gap ≤ n^2 → wires ≤ 2*R*X →
        let live := dir.teams*dir.sites
        let fresh := base+7*dir.candidates
        let origin := GeometryAdvice.Allocation.dest fresh profile gates outputs width
        let stop := GeometryAdvice.Allocation.stop fresh profile gates outputs width w
        let table := RoutingOutputs.bases origin cables cells dir.entries
        cables*3+RoutingOutputs.count cables cells dir.entries live+((cells+(dir.entries+cells))+37) ≤ outputs →
        stop ≤ 2*r*n → stop < 2^w →
        Cube.LabelIndex.wordEnvelope (Cube.labelCount s.α (cube.pred+1) n)
          (wires+dir.teams*((dir.fields+1)*(dir.processors*dir.literal))) < 2^w ∧
        fresh ≤ origin ∧ RoutingOutputs.controlsBase origin cables cells dir.entries live+36 < 2^w ∧
        TeamScales.width n (1/5)+gap+dir.entries*dir.description ≤ 3*(r*n)^2 ∧
        Directory.ISA.wordBound (Directory.ISA.placementBound dir table.privatePairs table.livePairs (3*(r*n)^2)) < 2^w := by
  have αpos : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have τpos : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have ξpos : 0 ≤ (s.τ:ℝ)/5 := by positivity
  have optimizer := Cube.LabelIndex.eventually_publication_words αpos (cube.pred+1) s.alpha_cube ξpos s.label_slack.1
  filter_upwards [b.eventually_directory_word,b.eventually_directory_cover,b.eventually_cube_primitives cube,
    optimizer,eventually_ge_atTop 1] with n machine cover scaled label hn
  intro r w R ξ X V dir slots wires base profile gates outputs width cables cells gap bound teams proc sites
    entries literalEq linkEq blockEq pos enough short desc tail gapFit wire live fresh origin stop table out stopBound stopFit
  have team : dir.teams ≤ n := teams ▸ scaled.2.2.1
  have actual := label dir w wires bound literalEq team (proc ▸ machine.2) (by simpa only [teams,proc] using wire)
  have bundles : dir.entries ≤ dir.teams*dir.sites := by
    rw [entries,teams,sites]
    exact Nat.mul_le_mul_right _ cover.2.2
  exact ⟨actual.2.2,output_directory_room dir hn (stretch_one ..) αpos.le ξpos team proc bound.fields
    literalEq (teams ▸ linkEq) (sites ▸ cover.1) (sites ▸ cover.2.1) (sites ▸ blockEq) pos enough short
    desc bundles tail gapFit machine.1 out stopBound stopFit⟩

end Diagonal

end BorderVNP
end Computability
end OAI
