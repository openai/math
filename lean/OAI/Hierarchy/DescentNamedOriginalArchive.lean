import OAI.Hierarchy.DescentOriginalSeedArchive
import OAI.Hierarchy.DescentSeedOriginIdentity

namespace OAI
/-! # The original seed archive transported to the physical site and edge names -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentCompiler DescentKernelHistory DescentColonies Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

/-- Only the arguments of each original node change names. Its birth index, scalar,
and hidden-word order continue to be read from the original input archive. -/
def renamedArchive {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    (a : Chronology.Archive W) (v : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge) :
    Chronology.Archive (PhysicalRename.world W v e) where
  bit := a.bit.renamed v e
  count := a.count
  order := (NodeOrder.renamedNames a.bit v e).trans a.order
  hiddenOrder := (DescentHistoryOrder.renamedHidden a.bit v e).toEmbedding.trans a.hiddenOrder

/-- A transported archive and elimination into families that depend on its contents. -/
structure ArchiveTransport {P : Type} {d : ℕ} {bits : P → ℕ}
    {W : MarkedWorld F d P bits} (a : Chronology.Archive W) (V : MarkedWorld F d P bits) where
  data : Chronology.Archive V
  carry (D : (U : MarkedWorld F d P bits) → Chronology.Archive U → Type) : D W a → D V data

private def transportArchive {P : Type} {d : ℕ} {bits : P → ℕ} {W V : MarkedWorld F d P bits}
    (a : Chronology.Archive W) (h : W = V) : ArchiveTransport a V where
  data := Eq.ndrec (motive := fun U => Chronology.Archive U) a h
  carry := by cases h; exact fun _ x => x

variable {cp pins : ℕ} (X : Approximation F cp pins) {G : PoweredGadget F} {S : AtomSchedule}
    {q fee : ℝ} {k z wire s : ℕ}

namespace Origin
variable {X} {c : (initialGroup X S.copies s).Choice}
    {digits : Fin S.copies ≃ Fin (S.groupCount 0) × Block k}
    (o : Origin (G:=G) (q:=q) (fee:=fee) (z:=z) (wire:=wire) X c digits)

/-- Transport the original archive along its physical identification at the named seed. -/
def archivePackage : ArchiveTransport
    (renamedArchive (Chronology.seedArchive X S.copies s c) (site o.raw) (edge o.raw))
    ((initial X S.copies s (S.groupCount 0) k digits).state c) :=
  transportArchive (renamedArchive (Chronology.seedArchive X S.copies s c) (site o.raw) (edge o.raw))
    (linked_world X c digits o.seed)

/-- The transported original archive at the named seed. -/
abbrev archive : Chronology.Archive ((initial X S.copies s (S.groupCount 0) k digits).state c) :=
  (archivePackage o).data

end Origin

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
