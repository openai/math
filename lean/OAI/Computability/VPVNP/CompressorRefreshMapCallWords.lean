import OAI.Computability.VPVNP.CompressorRefreshMapFrameFields
import OAI.Computability.VPVNP.PairSimulationMapCallSetup

/-!
# The raw private descriptor of a refresh map call

The descriptor carries the actual field starts, all demand and selected payload widths,
the stored repetition word, and four private workspace heads. Its width words are
unmasked: the local port and the fixed motif determine which incident slices the map
driver subsequently uses. The integer words are recovered from the physical term and
demand tables of the selected refresh.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.MapCallWords

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh NewSlots PhaseRecipe
open OperandInputs PairSimulation PairSimulation.NodeArguments RefreshMapOperands MotifConversion MotifSelector
open scoped Fin.CommRing

/-- Expressions for the four workspace addresses passed to the refresh map interpreter. -/
structure WorkHeads where
  /-- Expression for the address of the map interpreter's workspace directory. -/
  directory : Expr
  /-- Expression for the base address of the map's source buffer. -/
  source : Expr
  /-- Expression for the base address of the map's target buffer. -/
  target : Expr
  /-- Expression for the base address of the map's history buffer. -/
  hist : Expr

/-- Reads the repetition count from word one of the selected block's strided term record. -/
def copies (degree stride : ℕ) (I : Input) : Expr :=
  let block := ArgumentSite.blockIndex degree I.parent.siteOrd I.lanes
  .load ((I.termBase.add (block.mul (.lit stride))).add (.lit 1))

/-- Builds the map-call setup operands from the node field bases, stored demand and payload
widths, repetition count and workspace heads. -/
def fields {d d₀ dH t : ℕ} (P : SlotGraph (Fin d) dH) (hd : dH+1 ≤ d₀)
    (ties : Fin t ≃ Tie d) (stride : ℕ) (I : Input) (J : WorkHeads) : MapCallSetup.Arg (Tie d) (Fin d × Fin dH) → Expr
  | .base f => MapFrameFields.base P hd I f
  | .demand e => MapFrameFields.storedWidth (dH := dH) ties stride I (.inl (false,e))
  | .payload e => MapFrameFields.storedWidth ties stride I (.inr (false,e))
  | .copies => copies d stride I
  | .directory => J.directory
  | .source => J.source
  | .target => J.target
  | .hist => J.hist

variable {bits g t histCount pcs regs params : ℕ} {k : Type} [_root_.Field k] {S : BlockSchedule k}
  (B : S.Templates) (X : State S.portExponent (S.portExponent+g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (p : (X.Base × BitWord g) × Fin (2^S.portExponent)) (A : Arena) (child parent : ℕ)
  (oldDir newDir : IncidenceDirectory bits) (ties : Fin t ≃ Tie (2^S.portExponent))
  (start stride : ℕ) (pub : Fin 5 → W bits) (state : W bits) (m : Memory bits) (I : Input) (J : WorkHeads)
  (old : X.network.Half (oldSite X p))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order))
    B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites p))
  (grid : B.refresh.grid.demands) (L : MapEntryTable.Allocation B.refresh grid p.2 regs params) (loc : L.Address → Fin pcs)

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

/-- The map interpreter's ordinary numerical workspace, specialized to the chosen
refresh entry and to its actual incident wire arguments. -/
noncomputable abbrev Workspace (histCount bits : ℕ) :=
  let E := entryInput B X choice p old new
  MapEntry.Program.Workspace (L.program loc) E.demand E.payload
    (MotifEntry.demandBits tieSource tieTarget p.2 E.demandBits)
    (mapHalf S.portSupply (fun _ => MotifEntry.inputBits) E.supplyBits) histCount bits

private theorem copies_eq {fit : N ≤ 2^bits} (args : Describes I pub state m X p P hD hd internal A child parent
    oldDir newDir Q src term) (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice ties start stride fit m)
    (wide : D < 2^bits) :
    (copies D stride I).eval pub state m =
      word (repetitions B.refresh (blockDemandWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) p.1)) := by
  let b := ArgumentSite.blockIndex D I.parent.siteOrd I.lanes
  let row := SupplyScan.recordBase X term stride p.1
  have hb : b.eval pub state m = word (DemandScan.blocks X p.1).val :=
    ArgumentSite.blockIndex_eval X p pub state m _ _ args.site args.lanes wide
  have head : term + word (DemandScan.blocks X p.1).val * word stride = row := by rw [DemandScan.blocks_val]; rfl
  have room := stored.terms.fits p.1
  change row.val+2+D*H < 2^bits at room
  have one : (1 : W bits).val = 1 := Nat.mod_eq_of_lt (show 1 < 2^bits by omega)
  have atRep : (row+1).val = row.val+1 := by rw [Fin.val_add,one,Nat.mod_eq_of_lt (by change row.val+1 < 2^bits; omega)]
  change m (I.termBase.eval pub state m + b.eval pub state m * word stride + 1).val = _
  rw [args.termBase,hb,head,atRep]
  exact stored.terms.repetitions p.1

/-- Each descriptor word computed from the level arrays is exactly the word the native
map setup expects at that ordinal. -/
theorem values_eq {fit : N ≤ 2^bits} (Wk : Workspace B X choice p old new grid L loc histCount bits)
    (args : Describes I pub state m X p P hD hd internal A child parent oldDir newDir Q src term)
    (oldCols : oldDir.ActualColumns X m) (newCols : newDir.ActualColumns Y m)
    (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice ties start stride fit m)
    (wide : D < 2^bits) (bases : Wk.base = operandBase X p P hD hd internal A child parent)
    (directory : J.directory.eval pub state m = Wk.directory) (source : J.source.eval pub state m = word Wk.source)
    (target : J.target.eval pub state m = word Wk.target) (hist : J.hist.eval pub state m = word Wk.hist) :
    ∀ a, (fields P hd ties stride I J a).eval pub state m = MapCallSetup.values L loc Wk a := by
  intro a
  cases a with
  | base f =>
    change (MapFrameFields.base P hd I f).eval pub state m = word (Wk.base f)
    rw [bases]; exact MapFrameFields.base_eval X p P hD hd internal A child parent oldDir newDir Q src term pub state m I
      args oldCols newCols stored.segments wide f
  | demand e =>
    exact MapFrameFields.storedWidth_eval B X choice p A child parent oldDir newDir ties start stride pub state m I
      args stored wide (.inl (false,e))
  | payload e =>
    exact MapFrameFields.storedWidth_eval B X choice p A child parent oldDir newDir ties start stride pub state m I
      args stored wide (.inr (false,e))
  | copies => exact copies_eq B X choice p A child parent oldDir newDir ties start stride pub state m I args stored wide
  | directory => exact directory
  | source => exact source
  | target => exact target
  | hist => exact hist

end CompressorRecords.PortRefresh.MapCallWords

end VPVNP
end Computability
end OAI
