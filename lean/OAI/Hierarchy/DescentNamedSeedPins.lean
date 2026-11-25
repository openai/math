import OAI.Hierarchy.DescentNamedSeedChronology
import OAI.Hierarchy.DescentPathParticles
import OAI.Hierarchy.DescentPinCohorts

namespace OAI
/-! # External pins of the genuinely named physical compiler seed -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentColonies DescentKernelHistory Catalyst
open PinCohorts Chronology
open scoped Classical
noncomputable section

variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ}
  {k s z wire : ℕ}

private abbrev pinPositionAt {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    (r : Reached W G q ε S k 0 z 3 wire s) (pin : P) : Fin (S.groupCount 0) × Block k :=
  letI : Fintype r.V := r.finite
  letI : DecidableEq r.V := r.eqV
  ((r.placement.pos (W.graph.attach pin)).1, r.placement.block (W.graph.attach pin))

private abbrev rankAt {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    (r : Reached W G q ε S k 0 z 3 wire s) (pin : P) : ℕ :=
  (r.vertex (host r pin)).val

private def pinRows {P : Type} [Fintype P] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    (r : Reached W G q ε S k 0 z 3 wire s) (a : Archive W)
    (coords : P → Fin (S.groupCount 0) × Block k) (rank : P → ℕ) : Prop :=
  a.Particles r ∧ (∀pin, pinPositionAt r pin = coords pin) ∧ ∀pin, rankAt r pin = rank pin

private def sameHost {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    (r : Reached W G q ε S k 0 z 3 wire s) (a b : P) : Prop :=
  host r a = host r b

open private transportArchive from OAI.Hierarchy.DescentNamedOriginalArchive in
private theorem transported {P : Type} [Fintype P] {d : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F d P bits}
    (r : Reached W G q ε S k 0 z 3 wire s) (a : Archive W) (eqn : world r=W')
    (coords : P→Fin (S.groupCount 0)×Block k) (rank : P→ℕ)
    (aligned : ∀pin, ((r.placement.pos (W.graph.attach pin)).1,r.placement.block (W.graph.attach pin))=coords pin)
    (ranks : ∀pin,(r.vertex (host r pin)).val=rank pin) (tokens : a.Particles r) :
    let t := transport r eqn
    let b := (transportArchive (renamedArchive a (site r) (edge r)) eqn).data
    pinRows t b coords rank := by
  cases eqn
  refine ⟨tokens.renamed (site r) (edge r),?_,?_⟩
  · intro pin
    change ((r.placement.pos ((site r).symm ((site r) (W.graph.attach pin)))).1,
      r.placement.block ((site r).symm ((site r) (W.graph.attach pin))))=coords pin
    simpa only [Equiv.symm_apply_apply] using aligned pin
  · intro pin
    change (r.vertex (r.placement.pos ((site r).symm ((site r) (W.graph.attach pin)))).2).val=rank pin
    simpa only [host, Equiv.symm_apply_apply] using ranks pin

private theorem equalHostOfRank {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    (r : Reached W G q ε S k 0 z 3 wire s) (a b : P) (h : rankAt r a = rankAt r b) :
    sameHost r a b := r.vertex.injective (Fin.ext h)

open private transportArchive from OAI.Hierarchy.DescentNamedOriginalArchive in
private theorem rowsAt {P : Type} [Fintype P] {d : ℕ} {bits : P → ℕ} {W W' : MarkedWorld F d P bits}
    (r : Reached W G q ε S k 0 z 3 wire s) (a : Archive W) (eqn : world r = W')
    (t : Reached W' G q ε S k 0 z 3 wire s)
    (pkg : ArchiveTransport (renamedArchive a (site r) (edge r)) W')
    (sourceEqn archiveEqn : world r = W')
    (sourceEq : t = transport r sourceEqn)
    (archiveEq : pkg = transportArchive (renamedArchive a (site r) (edge r)) archiveEqn)
    (coords : P → Fin (S.groupCount 0) × Block k) (rank : P → ℕ)
    (aligned : ∀pin, pinPositionAt r pin = coords pin) (ranks : ∀pin, rankAt r pin = rank pin)
    (tokens : a.Particles r) : pinRows t pkg.data coords rank := by
  cases sourceEq
  cases archiveEq
  exact transported r a eqn coords rank aligned ranks tokens

private structure StoredPinRows (P : Type) (rank : P → ℕ) (particles : Prop) where
  coordinates : P → Prop
  ranks : P → Prop
  equalHosts : P → P → Prop
  hostProof : ∀u v, rank u = rank v → equalHosts u v
  verified : particles ∧ (∀pin, coordinates pin) ∧ ∀pin, ranks pin

open private transportArchive from OAI.Hierarchy.DescentNamedOriginalArchive in
private def carriedRows {P : Type} [Fintype P] {d : ℕ} {bits : P → ℕ} {W W' : MarkedWorld F d P bits}
    (r : Reached W G q ε S k 0 z 3 wire s) (a : Archive W) (eqn : world r = W')
    (t : Reached W' G q ε S k 0 z 3 wire s)
    (pkg : ArchiveTransport (renamedArchive a (site r) (edge r)) W')
    (es ea : world r = W') (hs : t = transport r es)
    (ha : pkg = transportArchive (renamedArchive a (site r) (edge r)) ea)
    (b : Archive W') (hb : b = pkg.data)
    (coords : P → Fin (S.groupCount 0) × Block k) (rank : P → ℕ)
    (aligned : ∀pin, pinPositionAt r pin = coords pin) (ranks : ∀pin, rankAt r pin = rank pin)
    (tokens : a.Particles r) : StoredPinRows P rank (b.Particles t) where
  coordinates pin := pinPositionAt t pin = coords pin
  ranks pin := rankAt t pin = rank pin
  equalHosts a b := sameHost t a b
  hostProof u v h := by
    apply equalHostOfRank t
    have rr := (rowsAt r a eqn t pkg es ea hs ha coords rank aligned ranks tokens).2.2
    exact (rr u).trans (h.trans (rr v).symm)
  verified := by
    cases hb
    exact rowsAt r a eqn t pkg es ea hs ha coords rank aligned ranks tokens

set_option maxHeartbeats 80000
namespace Origin
variable {cp pins : ℕ} {X : Approximation F cp pins}
variable {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
    (o : Origin (S:=S) (G:=G) (q:=q) (fee:=ε) (z:=z) (wire:=wire) X c digits)
local notation "named" => initial X S.copies s (S.groupCount 0) k digits
local notation "pins₀" => Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))

/-- Expanding the archive as a function keeps the kernel from evaluating its full transported contents. -/
private theorem archiveDefinition :
    @Origin.archive = fun {F} [iF : Field F] {cp pins X G S q fee k z wire s c digits} o =>
      (@Origin.archivePackage F iF cp pins X G S q fee k z wire s c digits o).data := rfl

private theorem archiveData : o.archive = o.archivePackage.data :=
  congrArg (fun f => @f F _ cp pins X G S q ε k z wire s c digits o) archiveDefinition

include o in
private abbrev checkedPinRows : StoredPinRows pins₀
    (fun pin => (Fintype.equivFin (Site X.network.copyGraph) (.inr pin.2)).val)
    (o.archive.Particles o.source) :=
  carriedRows (P := pins₀) (W := (initialGroup X S.copies s).state c)
    (W' := (named).state c)
    (G := G) (S := S) (k := k) (q := q) (ε := ε) (z := z) (wire := wire) (s := s)
    o.raw (seedArchive X S.copies s c) (linked_world X c digits o.seed)
    o.source o.archivePackage (linked_world X c digits o.seed) (linked_world X c digits o.seed)
    rfl rfl o.archive (archiveData o) (fun pin=>digits pin.1)
    (fun pin=>(Fintype.equivFin (Site X.network.copyGraph) (.inr pin.2)).val)
    o.seed.pinCoordinates o.seed.pinRanks (Chronology.seed_particles X c o.raw digits o.seed)

theorem pin_rows :
    o.archive.Particles o.source ∧ (∀pin, (checkedPinRows o).coordinates pin) ∧
      (∀pin, (checkedPinRows o).ranks pin) :=
  (checkedPinRows o).verified

theorem particles : o.archive.Particles o.source :=o.pin_rows.1

attribute [local irreducible] Origin.source in
theorem pinCoordinates (pin : pins₀) :
    ((o.source.placement.pos (((named).state c).graph.attach pin)).1,
      o.source.placement.block (((named).state c).graph.attach pin)) = digits pin.1 :=
  o.pin_rows.2.1 pin

theorem pinRanks (pin : pins₀) :
    rankAt (W := (named).state c) o.source pin = (Fintype.equivFin (Site X.network.copyGraph) (.inr pin.2)).val :=
  o.pin_rows.2.2 pin

theorem pinHosts {u v : pins₀} (same : u.2=v.2) : sameHost (W := (named).state c) o.source u v :=
  (checkedPinRows o).hostProof u v
    (congrArg (fun slab => (Fintype.equivFin (Site X.network.copyGraph) (.inr slab)).val) same)

end Origin
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
