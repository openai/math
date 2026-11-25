import OAI.Computability.BorderVNP.DiagonalReservedGeometryClock
import OAI.Computability.BorderVNP.PackedFrozenNativePort

/-! # The physical word clock available to the selected public output frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing Cover Epoch Packing PackedHistoryCircuit PackedHistoryCircuit.Normalized
open SelectedSchedule EnrichedOuter VPVNP.VerifierNetwork GeometryAdviceRate
open scoped Classical BorderVNP.Epoch.Cube

/-- The outcome of lowering, ceiling-padding, evaluating and writing one
specific geometry frame. The word width is the width used by the native
interpreter, including both sorted original-bundle banks when present. -/
def NativeGeometryReceipt {X Y P : Type} [Fintype X] [Fintype Y] [Fintype P]
    {o active field : ℕ} (U degree n r w teams tiles origins : ℕ)
    (history : Frame (X ⊕ Y) (P ⊕ Unit)) (order : Y ≃ Fin active) (fit : active ≤ SeedPlan.profileReserve r n)
    (output : Frame ((X ⊕ Fin (SeedPlan.profileReserve r n)) ⊕ P) (Fin o × Fin field)) (x : X → Bool) : Prop :=
  let reserve := SeedPlan.profileReserve r n
  let table := geometryTable history order fit output x
  let ceiling := geometryGateCeiling U degree r n
  let bits := packetWords ceiling reserve o field*w
  table.size ≤ ceiling ∧ (table.reserve ceiling).size=ceiling ∧
    (GeometryAdviceRate.ticks ceiling reserve o field w+bits+reserve+deliveryScanTicks origins teams tiles:ℕ) <
      (r:ℝ)*(n:ℝ)^(93/100:ℝ) ∧
    GeometryAdviceRate.ticks ceiling reserve o field w+bits ≤ r*TeamScales.width n (95/100:ℝ)

/-- The schedule supplies this numerical bound for every finite DAG on this
particular length, teams, original sites, and physical word width. -/
def NativeGeometryWindow (U degree n r w teams tiles origins rows : ℕ) : Prop :=
  ∀ {X Y P : Type} [Fintype X] [Fintype Y] [Fintype P] {active o mult : ℕ}
    (history : Frame (X ⊕ Y) (P ⊕ Unit)) (order : Y ≃ Fin active) (fit : active ≤ SeedPlan.profileReserve r n)
    (output : Frame ((X ⊕ Fin (SeedPlan.profileReserve r n)) ⊕ P) (Fin o × Fin w)) (x : X → Bool),
    1 ≤ w → ((mult*history.size+active:ℕ):ℝ) ≤ r*(n:ℝ)^(92/100:ℝ) →
    history.size+output.size+o*w ≤ mult*history.size+U*rows*(logWidth r n)^degree →
    NativeGeometryReceipt U degree n r w teams tiles origins history order fit output x

variable {D m : ℕ} [NeZero D] {F : Type} [Field F] {e : PaidIdentity F D m} {S : SiteSchedule e}
    {a x E dlog Q A B j : ℕ} {scale : EpochScales S a x}

/-- The numerical window for the *chosen* physical sites and actual number
of original bundles. Its constant precedes all geometry runs and field data. -/
theorem JointSchedule.eventually_native_geometry_window (b : JointSchedule scale (E+1) dlog Q A B j)
    (U degree : ℕ) (power : degree+(E+2) ≤ dlog) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let tiles := ExternalSew.GridHosts.tileCount (Fintype.card (Cube D)) d
      let T := epochs scale.τ n
      let C := CoverScale.sites (Cube D) (EnrichedOuter.depth S (d+1) T)
      let R := b.physical.teamsPred n+1
      let J := (fan S)^T*tiles
      let rows := routingRows (boundaryShape S (d+1) T) C J (R*tiles)
      NativeGeometryWindow U degree n r (b.physical.word n) R tiles J rows := by
  filter_upwards [b.eventually_reserved_geometry_charge degree U power] with n clock
  intro r d tiles T C R J rows
  let start := CoverScale.initialDepth (Cube D) r n
  have level : d+1=start := Nat.sub_add_cancel (by change 1 ≤ start; exact Nat.succ_pos _)
  have card : tiles=CoverScale.sites (Cube D) start := (seedPortCount (D:=D) d).trans (congrArg _ level)
  change NativeGeometryWindow U degree n r (b.physical.word n) R tiles ((fan S)^T*tiles)
    (routingRows (boundaryShape S (d+1) T) (CoverScale.sites (Cube D) (EnrichedOuter.depth S (d+1) T))
      ((fan S)^T*tiles) (R*tiles))
  rw [card,level]
  intro X Y P _ _ _ active o mult history order fit output x hw paid bound
  exact clock history order fit output x hw paid bound

end Diagonal

end BorderVNP
end Computability
end OAI
