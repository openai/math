import OAI.Hierarchy.DescentNamedSeedInitialShape
import OAI.Hierarchy.DescentNamedEpochs
import OAI.Hierarchy.DescentChronologicalBundle
import OAI.Hierarchy.DescentBundleSeedEpoch

namespace OAI
/-! # Aligned bundles for the physical seed and its actual chosen ordinary/reset chronology -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentColonies DescentKernelHistory Catalyst
open DescentBundleHistory Chronology
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

attribute [local irreducible] Origin.archivePackage Origin.source

open private ShapeTransfer ShapeTransfer.destination shapeTransfer Origin.transferFor from
  OAI.Hierarchy.DescentNamedSeedInitialShape

private def shapeOfTransfer {P : Type} {d : ℕ} {bits : P → ℕ}
    {W V : MarkedWorld F d P bits} {a : Archive W}
    (pkg : ArchiveTransport a V) (p R : ℕ) (record : ShapeTransfer)
    (same : record = shapeTransfer pkg p R) (input : ShapeTransfer.destination record) : WorldShape p R pkg.data.bit := by
  subst record
  exact input

private def changeShapeArchive {P : Type} {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    (src dst : Archive W) (same : src = dst) (p R : ℕ) (shape : WorldShape p R src.bit) :
    WorldShape p R dst.bit := same ▸ shape

namespace Origin
variable {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ} {k s z wire : ℕ}
    {cp pins : ℕ} {X : Approximation F cp pins} {c : (initialGroup X S.copies s).Choice}
    {digits : Fin S.copies ≃ Fin (S.groupCount 0) × DescentColonies.Block k}
    (o : Origin (G:=G) (S:=S) (s:=s) (q:=q) (fee:=ε) (z:=z) (wire:=wire) X c digits)
-- Identify the archive before projecting its dependent bit description.
private theorem archive_fun_eq :
    @Origin.archive F _ cp pins X G S q ε k z wire s c digits =
      fun (root : Origin (S:=S) (s:=s) (G:=G) (q:=q) (fee:=ε) (z:=z) (wire:=wire) X c digits) =>
        (Origin.archivePackage root).data := rfl

private theorem archive_eq : o.archive = (Origin.archivePackage o).data :=
  congrFun (archive_fun_eq (X:=X) (G:=G) (S:=S) (q:=q) (ε:=ε) (k:=k) (z:=z)
    (wire:=wire) (s:=s) (c:=c) (digits:=digits)) o

private def archiveShape (p R : ℕ) (hp : 0 < p) (stride : 1 ≤ R) (width : p ∣ s) :
    WorldShape p R o.archive.bit :=
  changeShapeArchive o.archivePackage.data o.archive (archive_eq o).symm p R
    (shapeOfTransfer o.archivePackage p R (Origin.transferFor o p R) rfl (o.bundleShape p R hp stride width))

end Origin

section
variable {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
local notation "wire₀" => S.epochPower^S.priceExponent
local notation "s₀" => S.firstWidth G.b p
local notation "q₀" => (1/((s₀:ℝ)*(wire₀:ℝ)):ℝ)
local notation "ε₀" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => q₀*(wire₀:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
/-- The only stride premise is the literal lower bound of the chosen normalized
epoch's max stride. Every ordinary and reset recipe is inherited through its real tape. -/
def Branch.bundleShape {he : 0≤ε₀} {hu : 0≤u} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) («Ht»:=Ht) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0<p)
    (stride : 1≤R) : WorldShape p R (Branch.archive X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (r:=r) (c:=c) b hp).bit :=
  let whole : p∣s₀:=dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b
  DescentBundleHistory.archiveShape (start := b.origin.source) (source := b.target)
    hp stride (fun _ => dvd_mul_of_dvd_left whole 1) b.origin.archive
    (Origin.archiveShape b.origin p R hp stride whole) b.path (b.path.recorded_whole p b.recorded) b.aligned

end
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
