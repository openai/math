import OAI.Hierarchy.DescentIssuedChronology
import OAI.Hierarchy.DescentBundleSchedule
import OAI.Hierarchy.DescentBundleReentry

namespace OAI
/-! # Whole-word operand descriptors on the same recipes as the issued node order -/
namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentKernelHistory DescentRotor
noncomputable section
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {q ε u : ℝ} {S : DescentCompiler.AtomSchedule} {k : ℕ} {W₀ W : MarkedWorld F d P bits}
variable {i₀ z₀ D₀ i z D w hist : ℕ} {start : Reached W₀ G q ε S k i₀ z₀ D₀ w hist}
variable {source : Reached W G q ε S k i z D w hist}
variable (hp : 0<p) (one : 1≤R) (pins : ∀a,p∣bits a)

def afterOrdinary {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {z' D' : ℕ} {target : Reached n.result G q ε S k (i+1) z' D' w hist}
    (link : OrdinaryLink source he T c n target) (a : Archive W) (before : WorldShape p R a.bit)
    (unit : p∣T.z) : WorldShape p R (link.advance a).bit :=
  WorldShape.follow hp T.unitPos unit n (link.quantum.symm ▸ link.cuts)
    (WorldShape.scanned he hp one pins T before unit c)

private def afterReset {n h C f g cut tail : ℕ} {ctl : ResetRates G S k D n h C f g cut tail}
    (b : ClosedReset source ctl) (a : Archive W) (before : WorldShape p R a.bit)
    (pos : 0<b.reset.unit) (whole : p∣b.reset.unit) (wide : max 1 (max b.reset.width (C*b.reset.width))≤R) :
    WorldShape p R (resetArchive b p hp whole a).bit := by
  let split:=BitDescription.granular W b.count (z*G.b) b.fit a.bit
  have sg : WorldShape p R split := before.granular b.count (z*G.b) b.fit hp (b.unit ▸ pos) (b.unit ▸ whole)
  let key:=DescentOrderedReset.grains W b.count b.order
  have fit : b.reset.unit=b.reset.unit/p*p := (Nat.div_mul_cancel whole).symm
  exact WorldShape.follow hp pos whole b.reblock b.cuts
    (reentryWorldShape sg b.reset b.terminals key (b.reset.unit/p) hp fit (resetMenu b) one wide)

/-- The grouped operand addresses and the scalar-node ordinal use the identical
bit description, through the actual ordinary tapes, chosen profiles and installed banks. -/
def archiveShape (a : Archive W₀) (before : WorldShape p R a.bit) (path : Path start source)
    (whole : path.whole p) (aligned : path.aligned p R) : WorldShape p R (path.archive p hp a whole).bit := by
  induction path with
  | here=>exact before
  | ordinary prev link ih=>exact afterOrdinary hp one pins link _ (ih whole aligned.1) aligned.2
  | reset prev b ih=>exact afterReset hp one b _ (ih whole.1 aligned.1) aligned.2.1 whole.2 aligned.2.2.2

end
end Hierarchy.DescentBundleHistory

end OAI
