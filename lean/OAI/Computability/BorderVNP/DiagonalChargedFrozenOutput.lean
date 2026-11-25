import OAI.Computability.BorderVNP.DiagonalCalibratedSignedOutput
import OAI.Computability.BorderVNP.DiagonalChargedSignedPacket
import OAI.Computability.BorderVNP.DiagonalFixedSignedSites

/-! # The actual signed geometry table, input literal and paid reader on one schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Cover Epoch Packing DeckGrid PackedHistoryCircuit Packing.Inherited FrozenTape
open ExternalSew TeamContraction PackedHistoryCircuit.Normalized SelectedSchedule EnrichedOuter TeamScales Filter
open _root_.OAI.Computability.BorderVNP.Cube VPVNP TeamContraction.ProcessorSlots
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {e : PaidIdentity F D m} {S : SiteSchedule e}
local notation "axes" => Fintype.card (Cube D)

/-- The public descriptor directory of the selected signed startup. Its site
and entry counts are the original grid size and full replicated bundle count. -/
noncomputable def JointSchedule.signedStartupDirectory {a x e₀ deg Q a₀ b₀ j : ℕ} {scale : EpochScales S a x}
    (b : JointSchedule scale e₀ deg Q a₀ b₀ j) (n desc : ℕ) : Directory.Layout :=
  let r := stretch b.ρ n
  let sites := CoverScale.sites (Cube D) (CoverScale.initialDepth (Cube D) r n)
  freeDirectory (b.physical.teamsPred n) r (literal scale.α n) (b.physical.link n)
    sites (blockWidth (r*n) sites) ((epochCopies S)^epochs scale.τ n*sites) desc

/-- Select the geometry ceiling once, before the field reader or the candidate
word. The resulting receipt installs the actual lowered table of the frozen
signed program at its designated free literal and computes the native stop
and branch-clock share on that same startup arena and free directory. -/
theorem EpochScales.exists_charged_signed_output {extra : ℕ} (cube : FixedCube K)
    (scales : EpochScales S (cube.pred+1) extra) (φ : K →+* F) (q E : ℕ) :
    let g := Fintype.card (e.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width)
    ∃ A : ℕ, ∀ {deg Q a₀ b₀ j : ℕ} (b : JointSchedule.{0} scales (E+1) deg Q a₀ b₀ j), 5*(E+2) ≤ deg →
    ∀ adv : ℕ → ℕ, PolynomiallyBounded adv → ∀ c k factor : ℕ, ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let tiles := GridHosts.tileCount axes d
      let T := epochs scales.τ n
      let cells := CoverScale.sites (Cube D) (EnrichedOuter.depth S (d+1) T)
      let copies := TeamScales.width n scales.α
      let R := b.physical.teamsPred n
      NativeGeometryWindow (8*(11920000+1500000+16008100*A+37)) (4*(E+2)) n r
        (b.physical.word n) (R+1) tiles ((fan S)^T*tiles)
        (routingRows (boundaryShape S (d+1) T) cells ((fan S)^T*tiles) ((R+1)*tiles)) ∧
      SignedReaderInstallAt (aux:=φ ∘ cube.table) (q:=q) cube b (cube.signedSiteProgram e) adv c k factor
        (4*(E+2)) (8*(11920000+1500000+16008100*A+37)) n ∧
      ∀ {teams time pins link inner : ℕ} {Edge : Type} (G : Wiring teams r time pins link inner n Edge)
        (order : Fin tiles ≃ (Fin axes → Deck (d+2)))
        (position : (Fin axes → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
        (desc : ℕ) (number : e.Entry → ℕ),
        let dir := b.signedStartupDirectory n desc
        let physical : Directory.Layout := {dir with sites := tiles, entries := (fan S)^T*tiles}
        physical = dir ∧ SignedPacketInputBounds S (d+1) T cells ((R+1)*tiles) (60*logWidth r n) (b.physical.word n)
          (logWidth r n) E A g (Boundary.seedFormat G order position copies) physical rfl number := by
  intro g
  obtain ⟨A,selected⟩ := scales.exists_signed_output_calibration g E 37
  refine ⟨A,?_⟩
  intro deg Q a₀ b₀ j b power adv poly c k factor
  let U := 8*(11920000+1500000+16008100*A+37)
  have installed := b.eventually_install_signed_receipts (aux:=φ ∘ cube.table) (q:=q) cube
    (cube.signedSiteProgram e) adv poly c k factor (4*(E+2)) U (by omega)
  filter_upwards [selected b power,installed] with n checked deploy
  refine ⟨checked.1,deploy,?_⟩
  intro teams time pins link inner Edge G order position desc number dir physical
  let start := CoverScale.initialDepth (Cube D) (stretch b.ρ n) n
  let d := start-1
  have positive : 1 ≤ start := Nat.succ_pos _
  have depth : d+1=start := by dsimp only [d]; omega
  have grid : GridHosts.tileCount axes d=CoverScale.sites (Cube D) start := by
    rw [←depth]
    simp only [GridHosts.tileCount,CoverScale.sites,Fintype.card_fun,Fintype.card_fin]
  refine ⟨?_,checked.2 G order position dir number⟩
  dsimp only [physical,dir,JointSchedule.signedStartupDirectory,freeDirectory]
  rw [show GridHosts.tileCount axes (CoverScale.initialDepth (Cube D) (stretch b.ρ n) n-1) =
    CoverScale.sites (Cube D) (CoverScale.initialDepth (Cube D) (stretch b.ρ n) n) from grid]
  rfl

end Diagonal

end BorderVNP
end Computability
end OAI
