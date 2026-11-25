import OAI.Hierarchy.DescentSeedRegisteredLivePointers
import OAI.Hierarchy.DescentDatedSeedSlotGeometry
import OAI.Hierarchy.DescentSeedNamedRange
import OAI.Hierarchy.DescentSeedRectangleOrder

namespace OAI
/-! # The three affine seed pages at original and unused operand slots -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler Catalyst DescentInitialHost DescentPackedSeed DescentDatedSeedStartup
open DescentKernelHistory DescentRetainedRangeDigits DescentLocalArchiveOrder SeedNamed Computability.BorderVNP.Crossing
open DescentSeedRoot DescentSeedInitialTable DescentColonies DescentDyadicSpan DescentRotor
open DescentDatedSeedStartup.Input DescentDatedPriorOperand DescentOperandStateBanks
open DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

open DescentBundleHistory

private structure SpanDigits (ordering : Type) (room : Prop) {k H groups N bits : ℕ}
    (values : Block k → Fin (3*N) → Fin 3 → Fin H → Fin groups → Cell (bits*1)) where
  atCell : ordering → room → Block k → Fin (3*N) → Fin 3 → Fin H → Fin groups → Cell (bits*1) → Prop
  read : ∀ nr ok x j f h g, atCell nr ok x j f h g (values x j f h g)

private theorem value_at_original_span {F : Type} [_root_.Field F] {cp pins H groups copies k N b : ℕ}
    (X : Approximation F cp pins) (seat : Vertex X ↪ Fin H)
    (digits : Fin copies ≃ Fin groups × Block k) (wide : 1 < 2^b)
    (v : Vertex X) (x : Block k) (g : Fin groups) (j : Fin (3*N)) (f : Fin 3) (n : Fin 1) :
    (((encode b 1).symm (Seed.Physical.value X seat (Equiv.refl _) digits N b 1 j.val
      (DescentRetainedRangeDigits.page f) x (seat v) g)) n).val =
        if j.val < legArity X v * N then value DescentTerminalSliceRuns.whole f else 0 := by
  let pair : Fin 3 × Fin N := finProdFinEquiv.symm j
  have pos : finProdFinEquiv (pair.1,pair.2) = j := finProdFinEquiv.apply_symm_apply j
  have idx := congrArg Fin.val pos
  have posted := Seed.Physical.value_live X seat (Equiv.refl _) digits N 1 b
    (by decide) (3*N) x v pair.1 pair.2 g (DescentRetainedRangeDigits.page f)
  rw [idx] at posted
  rw [posted]
  have before := DescentPackedSeed.Rectangle.before_rect (t := legArity X v) pair.1 pair.2 j pos
  by_cases hit : pair.1.val < legArity X v
  · rw [ite_eq_left (before.mpr hit)]
    simp only [Seed.Columns.scalar, Seed.Columns.leg?, dite_eq_left hit, Option.elim_some]
    have affine (ptr : Pointer) :
        ptr.fields ⟨0,1,1⟩ (DescentRetainedRangeDigits.page f) = value DescentTerminalSliceRuns.whole f :=
      DescentRetainedRangeDigits.header ptr DescentTerminalSliceRuns.whole f
    rw [affine]
    have digitBound : DescentRetainedRangeDigits.value DescentTerminalSliceRuns.whole f ≤ 1 := by
      fin_cases f <;> decide
    exact seed_single_digit b _ n (digitBound.trans_lt wide)
  · rw [ite_eq_right (fun lt => hit (before.mp lt))]
    simp only [Seed.Columns.scalar, Seed.Columns.leg?, dite_eq_right hit, Option.elim_none]
    exact seed_single_digit b 0 n (Nat.two_pow_pos _)

open private namedArchiveGeometry originalGeometry OrderedSlotGeometry.ordering OrderedSlotGeometry.room
  OrderedSlotGeometry.facts SlotGeometry.coordinates SlotFact.checked
  from OAI.Hierarchy.DescentDatedSeedSlotGeometry
open private transportArchive from OAI.Hierarchy.DescentNamedOriginalArchive
open private carriedCoordinates Coordinates.nodes
  from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates
open private transferredRange RangeFact.checked SeedNamed.Origin.readSeedRange
  from OAI.Hierarchy.DescentSeedNamedRange
open private SeedNamed.Origin.seedReadsAt
  from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates

variable {F : Type} [_root_.Field F] {S : AtomSchedule} (G : PoweredGadget F) (op : RotorSpec)
    {k cp p H : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k)
    (publicWide : Fintype.card (Vertex X)≤H) (l : DescentDatedSeedStartup.Layout) (header payload Z : ℕ)
local notation "g₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => DescentDatedSeedStartup.endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "Q" => nodeArities X publicWide l
local notation "finish" => (chart).seedEnd top
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "limit" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies l.seedWidth payload k H g₀ lanes finish
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "ports" => initial G op X S.copies l k H g₀ payload Z
local notation "final" => completeImage G op X digits publicWide l header payload Z
local notation "ob" => operandBase X l H g₀
local notation "db" => directoryBase X l H g₀ k
local notation "argBase" => Seed.Physical.bankStart X ob k g₀ l.operandLanes
local notation "L" => (ports).rangeLayout

local notation "spanValues" => (fun (x : Block k) (j : Fin (3*l.groupsPerNode)) (f : Fin 3) =>
  Seed.Physical.value X hs (Equiv.refl _) digits l.groupsPerNode l.operandBits 1 j.val
    (DescentRetainedRangeDigits.page f) x)

section Archive
variable {P : Type} {d : ℕ} {bits : P → ℕ} {W W' : MarkedWorld F d P bits}
    {q ε : ℝ} {s wire z : ℕ} (r : Reached W G q ε S k 0 z 3 wire s)
    (ar : Archive W) (eqn : world r = W')
    (old : NodeOrder.All ar.bit ≃ Fin S.copies × Vertex X)
    (seen : ∀ t : NodeOrder.All ar.bit,
      (r.vertex (r.placement.pos t.1).2).val = (Fintype.equivFin (Vertex X) (old t).2).val ∧
      (r.placement.pos t.1).1 = (digits (old t).1).1 ∧ r.placement.block t.1 = (digits (old t).1).2)
    (single : ∀ v : W.graph.Site, Fintype.card (ar.bit.recipe v).Node = 1)
local notation "geometry₀" => namedArchiveGeometry X digits publicWide op l payload Z r ar eqn old seen single

set_option maxHeartbeats 800000 in
private def physicalSpanDigits {a R : ℕ} (sh : WorldShape a R ar.bit) (wide : 1 < 2^l.operandBits)
    (pieces : l.groupsPerNode = s/a)
    (previous : ∀ t : NodeOrder.All ar.bit, ∀ j f, atSlot (sh.sites t.1) t.2 j f =
      if j < legArity X (old t).2 * (s/a) then value DescentTerminalSliceRuns.whole f else 0) :
    SpanDigits (OrderedSlotGeometry.ordering (geometry₀)) (OrderedSlotGeometry.room (geometry₀)) spanValues := by
  let pkg := transportArchive (renamedArchive ar (site r) (edge r)) eqn
  let names := Coordinates.nodes (carriedCoordinates r ar eqn pkg)
  let installed : WorldShape a R pkg.data.bit := pkg.carry
    (fun _ b => WorldShape a R b.bit) (sh.renamed (site r) (edge r))
  let current := SeedNamed.transport r eqn
  refine ⟨(fun nr ok x j f h g cell => ∀ (n : Fin 1) (y : NodeOrder.All pkg.data.bit),
    slotAt ports current pkg.data.bit nr ok x n h g = some y →
    (j.val < (occurrences (installed.sites y.1) y.2).length ∨ f = 2) →
    (((encode l.operandBits 1).symm cell) n).val = atSlot (installed.sites y.1) y.2 j.val f), ?_⟩
  intro nr ok x j f h g n y occupied _
  let v := (old (names y)).2
  have geometry := SlotFact.checked (SlotGeometry.coordinates (OrderedSlotGeometry.facts (geometry₀) nr ok))
  have atHost : h = hs v := (geometry x n h g y occupied).2.1
  have actual := RangeFact.checked (transferredRange r ar eqn sh
    (fun t => legArity X (old t).2 * (s/a)) previous)
  calc
    _ = (if j.val < legArity X v * l.groupsPerNode then value DescentTerminalSliceRuns.whole f else 0) := by
      rw [atHost]
      exact value_at_original_span X hs digits wide v x g j f n
    _ = (if j.val < legArity X v * (s/a) then value DescentTerminalSliceRuns.whole f else 0) :=
      congrArg (fun N => if j.val < legArity X v * N then value DescentTerminalSliceRuns.whole f else 0) pieces
    _ = _ := (actual y j.val f).symm
end Archive

variable {q ε : ℝ} {s wire z : ℕ} {choice : (initialGroup X S.copies s).Choice}
    (o : SeedNamed.Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z) (wire:=wire) choice digits)
    (ord : OrderedSlotGeometry.ordering (originalGeometry X digits publicWide op l payload Z o))
    (ready : OrderedSlotGeometry.room (originalGeometry X digits publicWide op l payload Z o))
    {a R : ℕ} (hp : 0<a) (units : 1≤R) (whole : a∣s)
set_option maxHeartbeats 800000 in
private def originalSpanDigits (wide : 1 < 2^l.operandBits) (pieces : l.groupsPerNode = s/a) :=
  physicalSpanDigits G op X digits publicWide l payload Z o.raw (Chronology.seedArchive X S.copies s choice)
    (linked_world X choice digits o.seed) (NodeOrder.seedSites X S.copies s choice)
    (fun t => SeedNamed.Origin.seedReadsAt o t.1) (DescentBundleHistory.initial_nodes X S.copies s choice)
    (seedRetained X S.copies s hp units whole choice).shape wide pieces
    (SeedNamed.Origin.readSeedRange X choice hp units whole)

set_option maxHeartbeats 800000 in
/-- All seven original page words are mounted together. On an occupied original
node its affine page contains the whole p-word descriptor, with zeros on unused legs. -/
theorem seed_argument_spans {w : ℕ} (m : Memory w) (fields : l.operandBits*l.operandLanes≤w)
    (early : header<l.base) (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish)
    (live : 0<lanes) (machine : payload≤w) (space : limit<2^w) (wide : 1<2^l.operandBits)
    (pieces : l.groupsPerNode=s/a) (x : Block k) (j : Fin (ports).argumentsPerNode) (f : Fin 3) :
    let face:=DescentRetainedRangeDigits.page f
    ∃cells : Fin H→Fin g₀→Cell (l.operandBits*1),
      Reads (previousBank L (ports).archive.arguments x (DescentOperandStateBanks.page face j))
          cells l.operandLanes ((final) m) ∧
      ∀h g, (originalSpanDigits G op X digits publicWide l payload Z o hp units whole wide pieces).atCell
        ord ready x j f h g (cells h g) := by
  intro face
  refine ⟨spanValues x j f, seed_operand_cells G op X digits publicWide l header payload Z
    m fields early sourceSpace live machine space face j x, ?_⟩
  exact (originalSpanDigits G op X digits publicWide l payload Z o hp units whole wide pieces).read
    ord ready x j f


end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
