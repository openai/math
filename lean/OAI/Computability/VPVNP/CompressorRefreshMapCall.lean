import OAI.Computability.VPVNP.CompressorRefreshMapCallData
import OAI.Computability.VPVNP.CompressorRefreshMapWorkspace
import OAI.Computability.VPVNP.CompressorRefreshArgumentPlan
import OAI.Computability.VPVNP.PairSimulationMapArgumentInput

/-!
# Publishing the raw refresh call into the private map interpreter

The linked writer computes every fixed argument from its six live input registers and the
constructed external level. It publishes a private descriptor for the selected map call.
The resulting config meets the interpreter's full raw input specification, including all
demand bits and all supply selector suffixes. The mathematical call supplies no descriptor
or bitstream to the writer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.MapCall

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh PhaseRecipe NewSlots
open OperandInputs PairSimulation PairSimulation.LocalHistory NodeArguments RefreshMapOperands MotifConversion MotifSelector MotifEntry

variable {bits g t histCount pcs regs params : ℕ} {k : Type} [_root_.Field k] {S : BlockSchedule k}
  (B : S.Templates) (X : State S.portExponent (S.portExponent+g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (p : (X.Base × BitWord g) × Fin (2^S.portExponent)) (A : Arena) (child parent : ℕ)
  (oldDir newDir : IncidenceDirectory bits) (ties : Fin t ≃ Tie (2^S.portExponent))
  (start stride : ℕ) (m : Memory bits) (I : OperandInputs.Input) (J : MapCallWords.WorkHeads)
  (old : X.network.Half (oldSite X p))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order))
    B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites p))
  (grid : B.refresh.grid.demands) (L : MapEntryTable.Allocation B.refresh grid p.2 regs params)
  (loc : L.Address → Fin pcs)
  (order : MapCallSetup.Arg (Tie (2^S.portExponent)) (Fin (2^S.portExponent) × Fin (2^S.expanderExponent)) ≃
    Fin (Fintype.card (MapCallSetup.Arg (Tie (2^S.portExponent)) (Fin (2^S.portExponent) × Fin (2^S.expanderExponent)))))
  (ptr : Expr)

local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "P" => S.graph.toSlotGraph
local notation "hD" => S.port_order
local notation "hd" => And.right S.degree_bounds
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "internal" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) S.graph (Nat.two_pow_pos _) hc B.refresh choice
local notation "Y" => dyadicRefreshNext X S.graph (Nat.two_pow_pos _) hc B.refresh hD hd choice
local notation "Pₗ" => Allocation.plan X (S.degreeExponent 0) H t stride start
local notation "Q" => Allocation.Plan.scratch Pₗ bits
local notation "src" => word (bits := bits) (Allocation.Plan.demand Pₗ)
local notation "term" => word (bits := bits) (Allocation.Plan.term Pₗ)
local notation "N" => Fintype.card X.Base*D*2^g*D
local notation "E₀" => entryInput B X choice p old new
local notation "u" => repetitions B.refresh (EntryInput.demand E₀)
local notation "d" => MotifEntry.demandBits tieSource tieTarget (Prod.snd p) (EntryInput.demandBits E₀)
local notation "x" => mapHalf S.portSupply (fun _ => MotifEntry.inputBits) (EntryInput.supplyBits E₀)
local notation "f" => (MapCallWords.fields P hd ties stride I J ∘ Equiv.symm order)
local notation "argc" => Fintype.card (MapCallSetup.Arg (Tie D) (Fin D × Fin H))

set_option maxHeartbeats 1400000 in
/-- A successful straight-line publication yields the raw interpreter input. It consumes
zero branch bits and charges exactly the reads appearing in the fixed expression bank. -/
theorem publish {fit : N ≤ 2^bits} {n limit : ℕ} (R : MapWorkspace.Regions (Tie D) (Fin D × Fin H))
    (capacity : MapWorkspace.Capacity B.refresh bits n limit) (copyBound : u ≤ n)
    (ordered : MapWorkspace.Ordered (L.program loc) (E₀).demand (E₀).payload R u histCount limit)
    (bases : R.base = operandBase X p P hD hd internal A child parent)
    (vm : Fin (RegisterSetup.regCount (MapArgumentWriter.recipes ptr f)) ↪ Fin regs)
    (inputs : Fin 6 → Fin regs) (aux : Fin 3 ↪ Fin regs)
    (place : MapArgumentWriter.Address ptr f → Fin pcs) (done : Fin pcs)
    (M : Machine bits pcs regs params) (link : ∀ a, M.code (place a) =
      (MapArgumentWriter.text ptr f vm inputs aux place done a).resize bits)
    (safe : ∀ i j, vm i ≠ inputs j) (apart : ∀ i j, vm i ≠ aux j) (c : Config bits pcs regs)
    (entry : c.pc = MapArgumentWriter.setupPC ptr f place 0)
    (oldCols : oldDir.ActualColumns X m) (newCols : newDir.ActualColumns Y m)
    (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice ties start stride fit m)
    (oldData : NodeFields A child X (oldSite X p) old c.privateMem)
    (newData : NodeFields A parent Y (promotedSites p) new c.privateMem) (wide : D < 2^bits) :
    let pub := fun j : Fin 5 => c.reg (inputs j.castSucc)
    let state := c.reg (inputs (Fin.last 5))
    let addr := ptr.eval pub state m
    let Wk := MapWorkspace.workspace (L.program loc) R d x capacity copyBound ordered
    Describes I pub state m X p P hD hd internal A child parent oldDir newDir Q src term →
    J.directory.eval pub state m = word R.directory → J.source.eval pub state m = word R.source →
    J.target.eval pub state m = word R.target → J.hist.eval pub state m = word R.hist →
    R.directory ≤ addr.val → addr.val+argc ≤ 2^bits →
    ∃ ev out, ev.length = MapArgumentWriter.clock ptr f ∧ countProbes ev = (∑ j, ((MapArgumentWriter.recipes ptr f) j).loads) ∧
      choiceBits ev = [] ∧ out.pc = done ∧ out.reg (aux 0) = addr ∧
      MapCallSetup.Input L order loc Wk (aux 0) out ∧ out.persistent = c.persistent ∧
      (∀ a : W bits, a.val < addr.val ∨ addr.val+argc ≤ a.val → out.privateMem a = c.privateMem a) ∧
      (∀ j, (∀ i, j ≠ vm i) → (∀ i, j ≠ aux i) → out.reg j = c.reg j) ∧
      ∀ fuel bs, execute M.program (fuel+ev.length) c m bs =
        (execute M.program fuel out m bs).map (fun r => ⟨ev++r.events,r.result⟩) := by
  intro pub state addr Wk args directory source target hist early room
  apply MapArgumentWriter.native_input L order loc Wk ptr (MapCallWords.fields P hd ties stride I J)
    vm inputs aux place done M link safe apart c m entry room
  · exact MapCallWords.values_eq B X choice p A child parent oldDir newDir ties start stride pub state m I J old new
      grid L loc Wk args oldCols newCols stored wide bases directory source target hist
  · exact MapCallData.resident_packed B X choice p A child parent old new grid L loc ties start stride m c.privateMem
      R capacity copyBound ordered addr early stored oldData newData bases

end CompressorRecords.PortRefresh.MapCall

end VPVNP
end Computability
end OAI
