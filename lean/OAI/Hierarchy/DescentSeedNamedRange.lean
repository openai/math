import OAI.Hierarchy.DescentDatedSeedOriginalNode
import OAI.Hierarchy.DescentTerminalSeedRoleWords

namespace OAI
/-! # The affine range at each original word after the initial site permutation -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentKernelHistory DescentBundleHistory
open DescentColonies DescentSeedRoot DescentPackedSeed DescentRetainedRangeDigits
open DescentTerminalSliceRuns Chronology Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k s z wire : ℕ}

private structure RangeFact where
  statement : Prop
  checked : statement

private theorem wholeRectangle (rows groups : ℕ) :
    repeatFields (List.replicate rows (List.replicate groups whole)).flatten =
      List.replicate (rows * groups) whole := by
  unfold repeatFields
  rw [List.flatten_replicate_replicate, List.flatMap_replicate, List.flatten_replicate_replicate]
  exact congrArg (fun n => List.replicate n whole) (Nat.mul_one (rows * groups))

private theorem rangeOfRectangle {p : ℕ} {Tag A : Type} {w : A → ℕ} {r : BitRecipe Tag A w}
    (sh : Shape p r) (u : r.Node) (rows groups : ℕ)
    (rect : sh.sliceFields u = List.replicate rows (List.replicate groups whole))
    (slot : ℕ) (f : Fin 3) :
    atSlot sh u slot f = if slot < rows * groups then value whole f else 0 := by
  have listed : occurrences sh u = List.replicate (rows * groups) whole :=
    (layout sh u).symm.trans ((congrArg (fun t : List (List SliceCode) => repeatFields t.flatten) rect).trans
      (wholeRectangle rows groups))
  change ((occurrences sh u)[slot]?).elim 0 (fun q => value q f) = _
  rw [listed, List.getElem?_replicate]
  split <;> rfl

section Map
variable {P : Type} {d : ℕ} {bits : P → ℕ} {W W' : MarkedWorld F d P bits}
    (r : Reached W G q ε S k 0 z 3 wire s) (a : Archive W) (eqn : world r = W')
local notation "named" => Eq.ndrec (motive := fun V => Archive V) (renamedArchive a (site r) (edge r)) eqn

open private transportArchive
  from OAI.Hierarchy.DescentNamedOriginalArchive in
private theorem across_fields {p R : ℕ} (sh : WorldShape p R a.bit) (y : NodeOrder.All (named).bit) :
    let installed := (transportArchive (renamedArchive a (site r) (edge r)) eqn).carry
      (fun _ b => WorldShape p R b.bit) (sh.renamed (site r) (edge r))
    let raw := acrossNodes r a eqn y
    (installed.sites y.1).sliceFields y.2 = (sh.sites raw.1).sliceFields raw.2 := by
  cases eqn
  rfl

open private transportArchive
  from OAI.Hierarchy.DescentNamedOriginalArchive in
open private carriedCoordinates carriedNodes_eq Coordinates.nodes
  from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates in
private def transferredRange {p R : ℕ} (sh : WorldShape p R a.bit) (count : NodeOrder.All a.bit → ℕ)
    (observed : ∀ raw : NodeOrder.All a.bit, ∀ slot f,
      atSlot (sh.sites raw.1) raw.2 slot f = if slot < count raw then value whole f else 0) :
    RangeFact := by
  let pkg := transportArchive (renamedArchive a (site r) (edge r)) eqn
  let installed : WorldShape p R (named).bit := pkg.carry
    (fun _ b => WorldShape p R b.bit) (sh.renamed (site r) (edge r))
  let names := Coordinates.nodes (carriedCoordinates r a eqn pkg)
  refine ⟨(∀ (y : NodeOrder.All (named).bit) (slot : ℕ) (f : Fin 3),
    atSlot (installed.sites y.1) y.2 slot f = if slot < count (names y) then value whole f else 0), ?_⟩
  intro y slot f
  let raw := acrossNodes r a eqn y
  exact (of_fields (installed.sites y.1) y.2 (sh.sites raw.1) raw.2
    (across_fields r a eqn sh y) slot f).trans
    ((observed raw slot f).trans (congrArg
      (fun n : NodeOrder.All a.bit => if slot < count n then value whole f else 0)
      (DFunLike.congr_fun (carriedNodes_eq r a eqn) y).symm))
end Map

namespace Origin
variable {cp pins : ℕ} {X : Approximation F cp pins} {c : (initialGroup X S.copies s).Choice}
    {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
    (o : Origin (G:=G) (q:=q) (fee:=ε) (z:=z) (wire:=wire) X c digits)
private abbrev seedRangeSize (copies grain width : ℕ) (X : Approximation F cp pins)
    (c : (initialGroup X copies grain).Choice) (raw : NodeOrder.All (BitDescription.initial X copies grain c)) : ℕ :=
  legArity X raw.1.2 * (grain / width)

private theorem readSeedRange {copies grain p R : ℕ} (X : Approximation F cp pins)
    (c : (initialGroup X copies grain).Choice) (hp : 0 < p) (unit : 1 ≤ R) (dvd : p ∣ grain)
    (raw : NodeOrder.All (BitDescription.initial X copies grain c)) (slot : ℕ) (f : Fin 3) :
    atSlot ((seedRetained X copies grain hp unit dvd c).shape.sites raw.1) raw.2 slot f =
      if slot < seedRangeSize copies grain p X c raw then value whole f else 0 := by
  rcases raw with ⟨⟨j,v⟩,u⟩
  exact rangeOfRectangle (initialShape X copies grain c ⟨j,v⟩ hp dvd) u
    (legArity X v) (grain / p) (DescentTerminalCombinedRole.seed_slices X c j v hp dvd u) slot f

set_option maxHeartbeats 1600000 in
private def originalRangeFact {p R : ℕ} (hp : 0 < p) (unit : 1 ≤ R) (dvd : p ∣ s) : RangeFact :=
  transferredRange o.raw (Chronology.seedArchive X S.copies s c) (linked_world X c digits o.seed)
    (seedRetained X S.copies s hp unit dvd c).shape (seedRangeSize S.copies s p X c)
    (readSeedRange X c hp unit dvd)

theorem original_range {p R : ℕ} (hp : 0 < p) (unit : 1 ≤ R) (dvd : p ∣ s) :
    (originalRangeFact o hp unit dvd).statement := (originalRangeFact o hp unit dvd).checked

end Origin
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
