import OAI.Hierarchy.DescentNamedTerminalSliceLayout
import OAI.Hierarchy.DescentNamedHistoryShape
import OAI.Hierarchy.DescentPrefixArgumentCapacity
import OAI.Hierarchy.DescentChronologicalBundle
import OAI.Hierarchy.DescentDatedSeedOriginalNode
import OAI.Hierarchy.DescentPackedSeedLegs

namespace OAI
/-! Size of the operand array actually posted by the seed or by a later date. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentKernelHistory DescentBundleHistory Chronology
noncomputable section
variable {F U : Type} [Field F] {d p R : ℕ} {bits : U → ℕ} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z₀ D₀ z D w hist : ℕ}
  {W₀ W : MarkedWorld F d U bits} {start : Reached W₀ G q ε S k 0 z₀ D₀ w hist}
  {cur : Reached W G q ε S k i z D w hist}
-- At date zero the path can only be the initial path.
private theorem atZeroSlots (hp : 0 < p) (one : 1 ≤ R) (pins : ∀a,p ∣ bits a)
    (base : Archive W₀) (sh : WorldShape p R base.bit) (limit : ℕ)
    (bound : ∀y : NodeOrder.All base.bit, (DescentRetainedRangeDigits.occurrences (sh.sites y.1) y.2).length ≤ limit)
    (path : Path start cur) (whole : path.whole p) (aligned : path.aligned p R)
    (atZero : i=0) (y : NodeOrder.All (path.archive p hp base whole).bit) :
    (DescentRetainedRangeDigits.occurrences ((archiveShape hp one pins base sh path whole aligned).sites y.1) y.2).length ≤ limit := by
  subst i
  cases path with
  | here => exact bound y


open DescentColonies DescentInitialHost DescentRetainedRangeDigits Catalyst
open DescentSeedRoot DescentPackedSeed Computability.BorderVNP.Crossing DescentSixParty
open CorrectionBatch
open scoped Classical
open ThreeFlat Routing Catalyst Diagonal
private theorem legsLeThree {cp pins : ℕ} (X : Approximation F cp pins) (v : Vertex X) : legArity X v ≤ 3 := by
  cases v with
  | inl site =>
    have eqv : seedArity (hubbed X.network.copyGraph) (.inl site) = legArity X (.inl site) :=
      by apply Fintype.card_congr; exact Equiv.refl (LocalBoundary X (.inl site))
    exact eqv.symm.le.trans (seedArity_le _ (hubbed_trivalent X.network.copyGraph (physical_output X).1) _)
  | inr pin => exact (by decide : 2 ≤ 3)

open private ShapeTransfer ShapeTransfer.source ShapeTransfer.destination ShapeTransfer.move
  shapeTransfer Origin.transferFor Origin.transferInput Origin.physicalShape from
  OAI.Hierarchy.DescentNamedSeedInitialShape
open private changeShapeArchive shapeOfTransfer Origin.archive_eq Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape
open private across_arity from OAI.Hierarchy.DescentDatedSeedOriginalNode
open private transportArchive from OAI.Hierarchy.DescentNamedOriginalArchive
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
set_option maxHeartbeats 180000
variable {fee : ℝ} {s wire : ℕ}
section
variable {P : Type} {d : ℕ} {bits : P → ℕ} {W V : MarkedWorld F d P bits}
    (r : Reached W G q fee S k 0 z 3 wire s) (a : Archive W) (eqn : world r = V)
-- Move the seed operand bound through both the physical renaming and the archive identification.
private theorem namedBoundFor {p R : ℕ} (hp : 0<p) (sh : WorldShape p R a.bit) (cap : ℕ)
    (bounded : ∀raw : NodeOrder.All a.bit, ((sh.sites raw.1).recipe hp).arity raw.2 ≤ cap)
    (pkg : ArchiveTransport (renamedArchive a (site r) (edge r)) V) (eqPkg : pkg = transportArchive (renamedArchive a (site r) (edge r)) eqn)
    (tr : ShapeTransfer) (trEq : tr = shapeTransfer pkg p R)
    (i : ShapeTransfer.source tr) (iEq : HEq i (sh.renamed (site r) (edge r)))
    (installed : ShapeTransfer.destination tr) (installedEq : installed = ShapeTransfer.move tr i)
    (dst : Archive V) (same : pkg.data = dst)
    (actual : WorldShape p R dst.bit)
    (actualEq : actual = changeShapeArchive pkg.data dst same p R (shapeOfTransfer pkg p R tr trEq installed))
    (y : NodeOrder.All dst.bit) : (occurrences (actual.sites y.1) y.2).length ≤ cap := by
  subst actual
  subst dst
  subst tr
  subst installed
  have idInput : i = sh.renamed (site r) (edge r) := eq_of_heq iEq
  subst i
  subst pkg
  exact (across_arity r a eqn hp sh y).le.trans (bounded (acrossNodes r a eqn y))
end
variable {cp pins : ℕ} {X : Approximation F cp pins} {c : (initialGroup X S.copies s).Choice}
    {digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k}
    (o : Origin (G:=G) (q:=q) (fee:=fee) (z:=z) (wire:=wire) X c digits)
private theorem rawSeedBound {copies grain p R : ℕ} (X : Approximation F cp pins)
    (c : (initialGroup X copies grain).Choice) (hp : 0<p) (one : 1≤R) (width : p∣grain)
    (raw : NodeOrder.All (BitDescription.initial X copies grain c)) :
    ((((seedRetained X copies grain hp one width c).shape.sites raw.1).recipe hp).arity raw.2) ≤ 3*(grain/p) := by
  rcases raw with ⟨⟨j,v⟩,node⟩
  exact (DescentDatedNodeMetadata.Seed.original X c j v hp width node).le.trans
    (Nat.mul_le_mul_right _ (legsLeThree X v))

private theorem trEq (p R : ℕ) : Origin.transferFor o p R = shapeTransfer o.archivePackage p R := rfl
private theorem originalInputHEq (p R : ℕ) (hp : 0<p) (one : 1≤R) (width : p∣s) :
    HEq (Origin.transferInput o p R hp one width) (Origin.physicalShape o p R hp one width) := HEq.rfl
private def physicalNamed (p R : ℕ) (hp : 0<p) (one : 1≤R) (width : p∣s) :=
  Origin.physicalShape o p R hp one width
private theorem originalPhysicalEq (p R : ℕ) (hp : 0<p) (one : 1≤R) (width : p∣s) :
    physicalNamed o p R hp one width = ((seedRetained X S.copies s hp one width c).shape.renamed (site o.raw) (edge o.raw)) := rfl

-- Compare the archive-shape functions before specializing the seed world.
private theorem canonicalShape_function :
    @Origin.archiveShape F _ G S q fee k s z wire cp pins X c digits =
    fun (root : Origin (G:=G) (q:=q) (fee:=fee) (z:=z) (wire:=wire) X c digits)
      (p R : ℕ) (hp : 0<p) (one : 1≤R) (width : p∣s) =>
        changeShapeArchive root.archivePackage.data root.archive (Origin.archive_eq root).symm p R
          (shapeOfTransfer root.archivePackage p R (Origin.transferFor root p R) rfl (root.bundleShape p R hp one width)) := rfl

private abbrev canonicalShape_eq {p R : ℕ} (hp : 0<p) (one : 1≤R) (width : p∣s) :=
  congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (canonicalShape_function
    (G:=G) (S:=S) (q:=q) (fee:=fee) (z:=z) (wire:=wire) (k:=k) (s:=s) (c:=c) (digits:=digits)) o) p) R) hp) one) width

open private Palette.bundle_move Palette.package_identity from OAI.Hierarchy.DescentNamedTerminalSliceLayout in
private abbrev exactNamedBound {p R : ℕ} (hp : 0<p) (one : 1≤R) (width : p∣s) :=
  namedBoundFor (V := (initial X S.copies s (S.groupCount 0) k digits).state c)
    o.raw (Chronology.seedArchive X S.copies s c) (linked_world X c digits o.seed) hp
    (seedRetained X S.copies s hp one width c).shape (3*(s/p)) (rawSeedBound X c hp one width)
    o.archivePackage (Palette.package_identity o) (Origin.transferFor o p R) (trEq o p R)
    (Origin.transferInput o p R hp one width)
    ((originalInputHEq o p R hp one width).trans (heq_of_eq (originalPhysicalEq o p R hp one width)))
    (o.bundleShape p R hp one width) (Palette.bundle_move o hp one width)
    o.archive (Origin.archive_eq o).symm (Origin.archiveShape o p R hp one width) (canonicalShape_eq o hp one width)

end
end Hierarchy.DescentSixParty.SeedNamed

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentKernelHistory DescentResetInvoice Catalyst Chronology
open DescentBundleHistory
open scoped Classical BigOperators
noncomputable section
attribute [local irreducible] Origin.source Origin.archivePackage
variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ} {k s z wire : ℕ}

section
variable {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)
variable {U : MarkedWorld F 0 (Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width)))
    (fun _ => S.firstWidth G.b p * 1)} {i z' D : ℕ}
    {cur : Reached U G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent))
      (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower) S k i z' D
      (S.epochPower ^ S.priceExponent) (S.firstWidth G.b p)}
    (before : Path b.origin.source cur) (whole : before.whole p)

set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
local notation "s" => S.firstWidth G.b p
local notation "pins" => (Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width)))
local notation "widths" => (fun _ : pins => s*1)

private theorem Branch.prefix_from_seed (aligned : before.aligned p R) (one : 1≤R) (seedWidth : p∣s)
    (drift : ℕ) (stride : R≤drift) (height : 0<S.height) (base : G.b≤2^S.capGain)
    (seed : WorldShape p R b.origin.archive.bit)
    (seedBound : ∀y : NodeOrder.All b.origin.archive.bit,
      (DescentRetainedRangeDigits.occurrences (seed.sites y.1) y.2).length ≤ 3*(s/p))
    (y : NodeOrder.All (before.archive p hp b.origin.archive whole).bit) :
    let divides : ∀a : pins, p∣(widths) a := fun _=>by simpa using seedWidth
    let shape:=archiveShape hp one divides b.origin.archive
      seed before whole aligned
    (DescentRetainedRangeDigits.occurrences (shape.sites y.1) y.2).length ≤
      if i=0 then 3*(s/p) else S.retainedArgumentsAt G drift := by
  intro divides sh
  by_cases atSeed : i=0
  · rw [ite_eq_left atSeed]
    exact atZeroSlots hp one divides b.origin.archive seed (3*(s/p)) seedBound before whole aligned atSeed y
  · rw [ite_eq_right atSeed]
    have bounded := Branch.prefix_argument_capacity X G S b hp before whole height base
      sh y.1 y.2
    exact bounded.trans (Nat.mul_le_mul_right _ (Nat.succ_le_succ stride))


open private Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape in
theorem Branch.prefix_posted_slots (aligned : before.aligned p R) (one : 1≤R) (seedWidth : p∣s)
    (drift : ℕ) (stride : R≤drift) (height : 0<S.height) (base : G.b≤2^S.capGain)
    (y : NodeOrder.All (before.archive p hp b.origin.archive whole).bit) :
    let divides : ∀a : pins, p∣(widths) a := fun _=>by simpa using seedWidth
    let shape:=archiveShape hp one divides b.origin.archive
      (Origin.archiveShape b.origin p R hp one seedWidth) before whole aligned
    (DescentRetainedRangeDigits.occurrences (shape.sites y.1) y.2).length ≤
      if i=0 then 3*(s/p) else S.retainedArgumentsAt G drift := by
  exact Branch.prefix_from_seed X G S b hp before whole aligned one seedWidth drift stride height base
    (Origin.archiveShape b.origin p R hp one seedWidth) (exactNamedBound b.origin hp one seedWidth) y

end
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
