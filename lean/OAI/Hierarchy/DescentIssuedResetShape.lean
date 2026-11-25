import OAI.Hierarchy.DescentChronologicalBundle

namespace OAI
/-! # The issued reset's installed recipes at a chronological archive cut -/
namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentKernelHistory DescentRotor
noncomputable section
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k : ℕ} {W₀ W : MarkedWorld F d P bits}
variable {i₀ z₀ D₀ i z D w hist : ℕ} {start : Reached W₀ G q ε S k i₀ z₀ D₀ w hist}
variable {source : Reached W G q ε S k i z D w hist}
variable (hp : 0<p) (one : 1≤R) (pins : ∀a,p∣bits a)

def reset_shape_at {n h C f g cut tail : ℕ} {ctl : ResetRates G S k D n h C f g cut tail}
    (b : ClosedReset source ctl) (a : Archive W) (before : WorldShape p R a.bit)
    (pos : 0<b.reset.unit) (whole : p∣b.reset.unit) (wide : max 1 (max b.reset.width (C*b.reset.width))≤R) :
    WorldShape p R (resetArchive b p hp whole a).bit := by
  let split:=BitDescription.granular W b.count (z*G.b) b.fit a.bit
  have sg : WorldShape p R split := before.granular b.count (z*G.b) b.fit hp (b.unit ▸ pos) (b.unit ▸ whole)
  let key:=DescentOrderedReset.grains W b.count b.order
  have fit : b.reset.unit=b.reset.unit/p*p := (Nat.div_mul_cancel whole).symm
  exact WorldShape.follow hp pos whole b.reblock b.cuts
    (reentryWorldShape sg b.reset b.terminals key (b.reset.unit/p) hp fit (resetMenu b) one wide)

theorem archive_shape_reset {n h C f g cut tail : ℕ} {ctl : ResetRates G S k D n h C f g cut tail}
    (b : ClosedReset source ctl) (a : Archive W₀) (initial : WorldShape p R a.bit) (before : Path start source)
    (whole : (before.reset b).whole p) (aligned : (before.reset b).aligned p R) :
    archiveShape hp one pins a initial (before.reset b) whole aligned =
      reset_shape_at hp one b (before.archive p hp a whole.1)
        (archiveShape hp one pins a initial before whole.1 aligned.1) aligned.2.1 whole.2 aligned.2.2.2 := rfl

end
end Hierarchy.DescentBundleHistory

end OAI
