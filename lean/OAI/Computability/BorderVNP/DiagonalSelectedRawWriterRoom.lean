import OAI.Computability.BorderVNP.DiagonalCubeHistogramRoom
import OAI.Computability.BorderVNP.DiagonalCubePublicationRoom
import OAI.Computability.BorderVNP.DiagonalExternalFreeGroups
import OAI.Computability.BorderVNP.DiagonalSelectedPlacementWords
import OAI.Computability.BorderVNP.DiagonalCubeDeclarationRoom
import OAI.Computability.BorderVNP.CubeTeamOwnedReplaySetup

/-! # Unchecked-declaration arithmetic on the actual selected signed cube arena -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing Cover Packing PackedHistoryCircuit.Normalized
open PackedHistoryCircuit.Normalized.SelectedSchedule RoutingISA RoutingISA.CubeArena ExternalSew
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {extra E dlog Q A B j : ℕ}

/-- Arithmetic bounds used before the accepting cube/label tests. In particular they
apply to declarations whose replay returns zero or whose later data checks fail. -/
structure SelectedRawWriterRoom (ar : CubeArena.Layout) (dir : Directory.Layout)
    (w X next profile gates outputs width : ℕ) : Prop where
  template : ar.header = CubeHeaderInstall.geometryInputs (next+7*dir.candidates) profile gates outputs width w
    ar.header.d ar.n ar.header.blocks ar.b ar.h ar.s
  million : 1000000 < 2^w
  scaled : 1000000*X*dir.teams < 2^w
  totalScaled : 1000000*(dir.teams*X)*dir.teams < 2^w
  rawSpace : 1000000*(ar.stop+3*dir.teams*(dir.processors*dir.literal))+2*ar.stop < 2^w
  labels : ∀ wires ≤ 2*dir.teams*X,
    _root_.OAI.Computability.BorderVNP.Cube.LabelIndex.wordEnvelope ar.alphabet
      (wires+dir.teams*((dir.fields+1)*(dir.processors*dir.literal))) < 2^w

  two : 2 ≤ ar.header.d
  replay : ∀ frame, frame+112 ≤ ar.header.header → ar.ReplayRoom w frame

  placement : let origin := GeometryAdvice.Allocation.dest (next+7*dir.candidates) profile gates outputs width
    let tabs := Packing.RoutingOutputs.bases origin ar.cables ar.cells dir.entries
    dir.description ≤ dir.literal →
    ar.cables*3+Packing.RoutingOutputs.count ar.cables ar.cells dir.entries (dir.teams*dir.sites)+
      (ar.cells+(dir.entries+ar.cells)+37) ≤ outputs →
    ∀ extent ≤ ar.cellStride,
      Directory.ISA.wordBound (Directory.ISA.placementBound dir tabs.privatePairs tabs.livePairs extent) < 2^w

/-- The scale selected before the field, chart and raw declaration pays the exact
directory volume of the frozen program, the largest candidate histogram and all
intermediate label-index products. Only the allocated end of the geometry table
enters the address bound; its real gate program can use any index up to that end. -/
theorem JointSchedule.eventually_selected_raw_writer_room {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s (E+1) dlog Q A B j) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n
      let w := b.physical.word n
      let ξ := (s.τ:ℝ)/5
      let X := exterior ξ r n
      let start := CoverScale.initialDepth (Epoch.Cube D) r n
      let V := CoverScale.sites (Epoch.Cube D) start
      let T := epochs s.τ n
      let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start T)
      let cables := (boundary S start T).edges+4*((R+1)*V)
      ∀ desc next profile gates outputs width : ℕ,
        let dir := freeDirectory R r (literal s.α n) (b.physical.link n) V (blockWidth (r*n) V) ((epochCopies S)^T*V) desc
        let base := GeometryAdvice.Allocation.stop (next+7*dir.candidates) profile gates outputs width w
        let sizes := selectedSizes base (_root_.OAI.Computability.BorderVNP.Cube.alphabet s.α n) ((R+1)*X) cells cables dir.candidates (R+1) r n profile
        base ≤ 2*r*n → SelectedRawWriterRoom (sizes.selected cube.pred cube.b cube.h cube.copies cube.width)
          dir w X next profile gates outputs width := by
  let order := cube.pred+1
  let limit := LocalRow.templateLimit cube.pred cube.b cube.h cube.copies cube.width
  filter_upwards [b.eventually_cube_primitives cube,b.eventually_selected_histogram_room cube,
    b.eventually_word_capacity 1000000 3,b.eventually_word_capacity 9216 (4+6*order),
    b.eventually_word_capacity limit 0,b.eventually_declaration_room cube,b.eventually_selected_placement_words,
    eventually_ge_atTop 2] with n prim hist big env fixed caps placement large
  have hn : 1 ≤ n := by omega
  intro r R w ξ X start V T cells cables desc next profile gates outputs width dir base sizes baseFit
  let Z := r*n+1
  let ar := sizes.selected cube.pred cube.b cube.h cube.copies cube.width
  have hr : 1 ≤ r := stretch_one ..
  have nz : n ≤ Z := (Nat.le_mul_of_pos_left _ hr).trans (Nat.le_succ _)
  have team : R+1 ≤ Z := prim.2.2.1.trans nz
  have traffic : (R+1)*X ≤ Z^2 := prim.2.2.2.2.1
  have aPos : 0 ≤ (s.α:ℝ) := by exact_mod_cast s.alpha_pos.le
  have literalFit : literal s.α n ≤ n := Nat.floor_le_of_le
    ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ) ≤ n)
      (show (1:ℝ)-(s.α:ℝ)/3 ≤ 1 by linarith)).trans_eq (Real.rpow_one _))
  have volume : (R+1)*(r*literal s.α n) ≤ Z^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul team ((Nat.mul_le_mul_left _ literalFit).trans (Nat.le_succ _))
  have scaled : 1000000*((R+1)*X)*(R+1) < 2^w := by
    have small := Nat.mul_le_mul traffic team
    calc
      _ = 1000000*(((R+1)*X)*(R+1)) := by ring
      _ ≤ 1000000*(Z^2*Z) := Nat.mul_le_mul_left _ small
      _ = 1000000*Z^3 := by ring
      _ < _ := big.2.2.1
  have largeN : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have αpos : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have sy : 2 ≤ ar.header.d := Nat.lt_ceil.mpr (by
    simp only [Nat.cast_one]; exact Real.one_lt_rpow largeN (by linarith only [αpos]))
  refine ⟨rfl,prim.2.2.2.2.2.2.1,?_,scaled,?_,?_,sy,?_,?_⟩
  · exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left X (Nat.succ_pos _)))).trans_lt scaled
  · change 1000000*(ar.stop+3*(R+1)*(r*literal s.α n))+2*ar.stop < 2^w
    have mass := Nat.mul_le_mul_left (3*(R+1)) (Nat.mul_le_mul_left r literalFit)
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left 1000000
      (Nat.add_le_add_left mass ar.stop)) (2*ar.stop)).trans_lt (hist dir next profile gates outputs width baseFit)
  · intro wires fit
    have zy : 1 ≤ Z^order := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have zz : 1 ≤ Z^2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have labels : ar.alphabet ≤ Z^order :=
      Nat.pow_le_pow_left (prim.2.1.trans nz) order
    have vol : wires+dir.teams*((dir.fields+1)*(dir.processors*dir.literal))+1 ≤ 6*Z^2 := by
      change wires+((R+1)*(3*(r*literal s.α n)))+1 ≤ _
      change wires ≤ 2*(R+1)*X at fit
      have wide : wires ≤ 2*((R+1)*X) := by simpa [Nat.mul_assoc] using fit
      have v := Nat.mul_le_mul_left 3 volume
      have eqn : (R+1)*(3*(r*literal s.α n)) = 3*((R+1)*(r*literal s.α n)) := by ring
      omega
    change 4*(wires+dir.teams*((dir.fields+1)*(dir.processors*dir.literal))+1)^2*(ar.alphabet+1)^6 < 2^w
    calc
      _ ≤ 4*(6*Z^2)^2*(2*Z^order)^6 := Nat.mul_le_mul
        (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left vol 2)) (Nat.pow_le_pow_left (by omega) 6)
      _ = 9216*Z^(4+6*order) := by rw [pow_add Z 4 (6*order), Nat.mul_comm 6 order, pow_mul Z order 6]; ring
      _ < _ := env.2.2.1
  · intro frame before
    have space : 1000000*(ar.stop+3*(R+1)*(r*n))+2*ar.stop < 2^w :=
      hist dir next profile gates outputs width baseFit
    have fixedWord : limit < 2^w := by simpa using fixed.2.2.1
    have cap := (caps (((R+1)*X:ℕ):ℝ) (le_refl _)).2
    change ar.ReplayRoom w frame
    refine ⟨rfl,by omega,Nat.mul_pos prim.2.2.2.2.2.1 cube.block_pos,
      FixedCube.packet_bank_pos cube,before,by omega,fixedWord,?_⟩
    exact Nat.lt_trans (Nat.lt_succ_self _) cap
  · intro origin tabs short table extent fits
    exact placement desc next profile gates outputs width cables cells (short.trans literalFit) baseFit table extent fits

end Diagonal

end BorderVNP
end Computability
end OAI
