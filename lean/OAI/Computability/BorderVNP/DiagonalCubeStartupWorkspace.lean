import OAI.Computability.BorderVNP.DiagonalCubeSelectedWorkspace
import OAI.Computability.BorderVNP.DiagonalCommonRouteHeader

/-! # The selected cube's public workspace before routing the actual descriptors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing Cover Packing PackedHistoryCircuit.Normalized
open PackedHistoryCircuit.Normalized.SelectedSchedule RoutingISA.CubeArena
open TeamContraction.ProcessorSlots _root_.OAI.Computability.BorderVNP.Cube.Physical
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {a extra E dlog Q A B j : ℕ}

/-- The complete common prefix alone fits a rounded physical link before any
route table or private payload is formed. -/
theorem JointSchedule.eventually_startup_header {s : EpochScales S a extra}
    (b : JointSchedule.{u} s E dlog Q A B j) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      ∀ len : ℕ, (len:ℝ) ≤ r*(n:ℝ)^(24/25:ℝ) → len ≤ r*b.physical.link n := by
  have pos : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have fit := Routing.eventually_fit_block (α := s.α) (ξ := (s.τ:ℝ)/5) (by positivity)
    (by linarith only [s.tau_small,s.alpha_small])
  filter_upwards [b.eventually_lengths 0,fit,eventually_ge_atTop 1] with n lengths small hn
  intro r len header
  let R := b.physical.teamsPred n+1
  have hR : 2 < R := lengths.teams.1
  let zero : Fin R → Fin R → ℕ := fun _ _ => 0
  let team : Fin R := ⟨0,by omega⟩
  have bound := small r R len hR (stretch_one ..) lengths.teams.2 header zero
    (fun u => by simp [Routing.demand,zero]) team team
  have eq : b.physical.link n = TeamScales.link ((s.τ:ℝ)/5) R n := by
    dsimp only [R]
    rw [(b.sizes hn).1]
    rfl
  rw [eq]
  omega

set_option maxRecDepth 4000 in
/-- The startup arena, true seven-word demand reservation, compiled geometry
scratch, and selected cube arena fit at one threshold. Only the physical slot
and geometry-packet inputs enter the estimate. The budget precedes every
actual geometry output or data placement. -/
theorem JointSchedule.eventually_cube_startup_workspace {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s (E+1) dlog Q A B j) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let w := b.physical.word n
      let ξ := (s.τ:ℝ)/5
      let X := R*exterior ξ r n
      let symbols := Cube.alphabet s.α n
      let start := CoverScale.initialDepth (Epoch.Cube D) r n
      let V := CoverScale.sites (Epoch.Cube D) start
      let T := epochs s.τ n
      let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start T)
      let cables := (boundary S start T).edges+4*(R*V)
      ∀ (dir : Directory.Layout) (len copied slots profile gates outputs width : ℕ),
        (len:ℝ) ≤ r*(n:ℝ)^(24/25:ℝ) → copied ≤ r → 0 < slots → r*literal s.α n ≤ slots →
        slots ≤ r*n → dir.teams = R → dir.processors = r → dir.entries = (epochCopies S)^T*V →
        dir.fields ≤ 2 → dir.block = blockWidth slots V → dir.literal = literal s.α n → 1 ≤ width →
        GeometryAdviceRate.packetWords gates profile outputs width*w ≤ r*TeamScales.width n (95/100:ℝ) →
        let initial : StartupArena := ⟨R,r,literal s.α n,b.physical.link n,len,copied⟩
        let base := GeometryAdvice.Allocation.stop (initial.next+7*dir.candidates) profile gates outputs width w
        let sizes := selectedSizes base symbols X cells cables dir.candidates R r n profile
        let arena := sizes.selected cube.pred cube.b cube.h cube.copies cube.width
        initial.frame+112 ≤ initial.next ∧ base ≤ 2*r*n ∧ 0 < arena.header.d ∧ 0 < arena.header.blocks ∧
          1000000 < 2^w ∧ 1000000*X < 2^w ∧ arena.stop < 2^w ∧
          ∀ pp lp, (dir.directory pp lp).length+symbols.choose 2 ≤ arena.maxRows := by
  have ha : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have ht : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have space := eventually_cover_workspace_fields (Epoch.Cube D) ha s.alpha_small ht s.tau_small
    (epochCopies_pos S) s.copy_rate
  filter_upwards [b.eventually_startup_header,b.eventually_selected_cube_workspace cube,space,
    b.eventually_word_capacity 1 1,eventually_ge_atTop 1] with n headerRoom cubeRoom cover word hn
  intro r R w ξ X symbols start V T cells cables dir len copied slots profile gates outputs width lenFit
    copiedFit slotsPos slotsLo slotsHi nt nr ne nf nb nl widthPos charged initial base sizes arena
  have hr := stretch_one b.ρ n
  have count := (b.sizes hn).1
  change R = TeamScales.teams s.α s.τ (epochCopies S) n at count
  have hl : b.physical.link n = TeamScales.link ξ R n := by rw [count]; rfl
  have one : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have blockExp : 0 ≤ 1-ξ/3 := by dsimp only [ξ]; linarith only [s.tau_small,s.alpha_small]
  have blockPos : 1 ≤ block ξ n := Nat.le_floor (by simpa using Real.one_le_rpow one blockExp)
  have positiveW : 1 ≤ w := by
    have wide := word.2.2.1
    change 1*(r*n+1)^1 < 2^w at wide
    by_contra! bad
    rw [show w = 0 by omega,pow_zero,pow_one,one_mul] at wide
    omega
  let actual : StartupArena := ⟨TeamScales.teams s.α s.τ (epochCopies S) n,r,literal s.α n,
    TeamScales.link ξ (TeamScales.teams s.α s.τ (epochCopies S) n) n,len,copied⟩
  have identical : initial = actual := by dsimp only [initial,actual]; rw [hl,count]
  have enough : len ≤ r*actual.link := by simpa only [actual,← count,← hl] using headerRoom len lenFit
  have support := cover r len copied w slots profile gates outputs width dir hr slotsPos slotsLo slotsHi
    (nt.trans count) nr ne nf nb nl enough (copiedFit.trans (Nat.le_mul_of_pos_right _ blockPos)) word.1
    widthPos positiveW charged
  change actual.frame+112 ≤ actual.next ∧ GeometryAdvice.Allocation.stop (actual.next+7*dir.candidates)
    profile gates outputs width w ≤ 2*r*n ∧ _ at support
  rw [← identical] at support
  exact ⟨support.1,support.2.1,cubeRoom dir initial.next profile gates outputs width support.2.1⟩

end Diagonal

end BorderVNP
end Computability
end OAI
