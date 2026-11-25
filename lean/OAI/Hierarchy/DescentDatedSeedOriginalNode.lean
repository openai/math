import OAI.Hierarchy.DescentDatedSeedOriginalCoordinates
import OAI.Hierarchy.DescentNamedSeedInitialShape
import OAI.Hierarchy.DescentDatedNodeMetadataSeedRole
import OAI.Hierarchy.DescentRetainedRangeDigits
import OAI.Hierarchy.DescentStableAtomFields

namespace OAI
/-! # Recovering the original copy, gate and operand count of a named seed node -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentKernelHistory DescentBundleHistory DescentColonies
open DescentSeedRoot DescentPackedSeed DescentRetainedRangeDigits Chronology Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} {q fee : ℝ} {S : AtomSchedule} {k s z wire : ℕ}
section Transport
variable {P : Type} {d : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F d P bits}
    (r : Reached W G q fee S k 0 z 3 wire s) (a : Archive W) (eqn : world r=W')
local notation "named" => Eq.ndrec (motive := fun V => Archive V) (renamedArchive a (site r) (edge r)) eqn

open private transportArchive
  from OAI.Hierarchy.DescentNamedOriginalArchive in
private theorem across_arity {p R : ℕ} (hp : 0<p) (sh : WorldShape p R a.bit) (y : NodeOrder.All (named).bit) :
    let carried := (transportArchive (renamedArchive a (site r) (edge r)) eqn).carry
      (fun _ b => WorldShape p R b.bit) (sh.renamed (site r) (edge r))
    let raw := acrossNodes r a eqn y
    (occurrences (carried.sites y.1) y.2).length = ((sh.sites raw.1).recipe hp).arity raw.2 := by
  cases eqn
  let oldSite := (site r).symm y.1
  let rename := namedMap (p := p) W (site r) (edge r) y.1
  exact (DescentRetainedRangeDigits.length ((sh.sites oldSite).reroute rename) y.2 hp).trans
    (reroute_arity hp (sh.sites oldSite) rename y.2)
private structure ArityFact where
  statement : Prop
  checked : statement

open private transportArchive
  from OAI.Hierarchy.DescentNamedOriginalArchive in
open private carriedCoordinates carriedNodes_eq Coordinates.nodes
  from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates in
private def transferredArity {p R : ℕ} (hp : 0 < p) (sh : WorldShape p R a.bit)
    (count : NodeOrder.All a.bit → ℕ)
    (counted : ∀ raw : NodeOrder.All a.bit, ((sh.sites raw.1).recipe hp).arity raw.2 = count raw) :
    ArityFact := by
  let pkg := transportArchive (renamedArchive a (site r) (edge r)) eqn
  let installed : WorldShape p R (named).bit := pkg.carry
    (fun _ b => WorldShape p R b.bit) (sh.renamed (site r) (edge r))
  let names := Coordinates.nodes (carriedCoordinates r a eqn pkg)
  refine ⟨(∀ y : NodeOrder.All (named).bit,
    (occurrences (installed.sites y.1) y.2).length = count (names y)), ?_⟩
  intro y
  exact (across_arity r a eqn hp sh y).trans
    ((counted (acrossNodes r a eqn y)).trans
      (congrArg count (DFunLike.congr_fun (carriedNodes_eq r a eqn) y).symm))

end Transport

namespace Origin
variable {cp pins : ℕ} {X : Approximation F cp pins} {c : (initialGroup X S.copies s).Choice}
    {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
    (o : Origin (G:=G) (q:=q) (fee:=fee) (z:=z) (wire:=wire) X c digits)
private abbrev rawSeedCount (copies grain width : ℕ) (X : Approximation F cp pins)
    (c : (initialGroup X copies grain).Choice) (raw : NodeOrder.All (BitDescription.initial X copies grain c)) : ℕ :=
  legArity X raw.1.2 * (grain/width)

private theorem rawSeedCounted {copies grain p R : ℕ} (X : Approximation F cp pins)
    (c : (initialGroup X copies grain).Choice) (hp : 0 < p) (units : 1 ≤ R) (width : p ∣ grain)
    (raw : NodeOrder.All (BitDescription.initial X copies grain c)) :
    ((((seedRetained X copies grain hp units width c).shape.sites raw.1).recipe hp).arity raw.2) =
      rawSeedCount copies grain p X c raw := by
  rcases raw with ⟨⟨j,v⟩,node⟩
  exact DescentDatedNodeMetadata.Seed.original X c j v hp width node

set_option maxHeartbeats 1600000 in
private def originalArityFact {p R : ℕ} (hp : 0 < p) (units : 1 ≤ R) (width : p ∣ s) : ArityFact :=
  transferredArity o.raw (Chronology.seedArchive X S.copies s c) (linked_world X c digits o.seed) hp
    (seedRetained X S.copies s hp units width c).shape
    (rawSeedCount S.copies s p X c) (rawSeedCounted X c hp units width)

theorem original_arity {p R : ℕ} (hp : 0 < p) (units : 1 ≤ R) (width : p ∣ s) :
    (originalArityFact o hp units width).statement :=
  (originalArityFact o hp units width).checked

end Origin
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
