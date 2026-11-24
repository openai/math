import OAI.Computability.VPVNP.PairSimulationShrinkRowAction
import OAI.Computability.VPVNP.PairSimulationMapScratchOutside
import OAI.Computability.VPVNP.PairShrinkUpdatedBelow

/-!
# Histogram readback for a shrinking resident row

The selector and label arrays are disjoint from the counter bank. For a successful
entry, the descriptor, directory and gather writes also leave this bank intact.
Each emitted ordinal then increments its own counter, including repeated ordinals.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapScratch

open MotifSelector MotifGrid MotifBlocks MotifConversion MotifEntry MapCallSetup MapEntryTable
open scoped Fin.CommRing
open private write_other apart_of_interval from OAI.Computability.VPVNP.PairSimulationMapScratchOutside

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {z : B.grid.demands} {j : J} {r k p w t u : ℕ}
  (A : Allocation B z j r k) (args : Arg D E ≃ Fin (Fintype.card (Arg D E)))
  (loc : A.Address → Fin p) {demand : D → ℕ} {v : E → ℕ}
  {d : DemandBits src dst demand j} {x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j}
  (W : MapEntry.Program.Workspace (A.program loc) demand v d x t w)
  (addr : BurstRAM.Word w) (sel : Selector B ↪ BurstRAM.Word w)
  (ord : (parameterData B).Entry → Fin t)

local notation "entry" => Prod.fst (MotifEntry.run src dst (baseDemand B z) demand G (basePayload B)
  (lookup B z) (selectorTable B) (selectorCode B) v j d x)
local notation:max "bin" l:max => ((W.hist + Fin.val (l : Fin t) : ℕ) : BurstRAM.Word w)

/-- On successful inputs the pure upper scratch update adds the exact number of emitted
occurrences at a live counter cell disjoint from the descriptor and pointer directory. -/
theorem upper_histogram (endAddr : ℕ) (saved : DFS.Scratch w endAddr)
    (good : (entry).isSome = true) (l : Fin t) (live : endAddr ≤ (bin l).val)
    (fit : addr.val + Fintype.card (Arg D E) ≤ 2 ^ w)
    (descriptor : (bin l).val < addr.val ∨ addr.val + Fintype.card (Arg D E) ≤ (bin l).val)
    (directory : ∀ i : MapDirectoryInit.Row A, bin l ≠ W.directory + (i.val : BurstRAM.Word w)) :
    NodeArguments.rawScratch (upper A args loc W addr sel ord endAddr saved) (bin l) =
      NodeArguments.rawScratch saved (bin l) + ((((entry).map (List.map ord)).getD []).count l :
        BurstRAM.Word w) := by
  let old := NodeArguments.rawScratch saved
  have ptr (i : Fin (Fintype.card (Arg D E))) : bin l ≠ addr + (i.val : BurstRAM.Word w) := by
    simpa only [Fin.cast_val_eq_self] using apart_of_interval (bin l) fit descriptor i
  have desc : published A args loc W addr old (bin l) = old (bin l) := write_other _ _ _ _ ptr
  have init : directoryMemory A loc W (published A args loc W addr old) (bin l) = old (bin l) :=
    (write_other _ _ _ _ directory).trans desc
  have value : (bin l).val = W.hist + l.val :=
    Nat.mod_eq_of_lt ((Nat.add_lt_add_left l.isLt W.hist).trans_le W.histogramFit)
  have exterior (base : ℕ) (apart : base + u ≤ W.hist ∨ W.hist + t ≤ base) :
      (bin l).val < base ∨ base + u ≤ (bin l).val := by
    rw [value]
    have := l.isLt
    omega
  have source := apart_of_interval (bin l) W.ordinalFit.le (exterior W.source W.sourceHistApart)
  have target := apart_of_interval (bin l) W.labelFit.le (exterior W.target W.targetHistApart)
  obtain ⟨θ, pick, valid⟩ := sequence_of_success good
  rw [NodeArguments.rawScratch, dite_eq_left live]
  change successMemory A args loc W addr sel ord old (bin l) = old (bin l) + _
  rw [successMemory, pick, Option.elim_some, MapEntry.Program.successMemory,
    PrivateLabels.accumulate_at W.hist _ _ W.histogramFit l, write_other _ _ _ _ target,
    write_other _ _ _ _ source, init, MapFinish.entry_value, pick, Option.bind_some,
    ite_eq_left valid, Option.map_some, Option.getD_some, List.map_ofFn]
  rfl

end PairSimulation.MapScratch

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.ShrinkSlots
open Compression Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifGrid MotifBlocks MotifConversion MapResidentRows MapHandlerOperand
open scoped Fin.CommRing

variable {K : Type} [Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {t shared w g endAddr packetEnd : ℕ} (F : MapHandlerImage.Family B t shared)
  (G : ShrinkGatherBank.Family F)
  (X : State G.a (packingLaneBits G.a g)) {δ : ℝ}
  {ready : Ready (2 ^ G.a) (2 * 2 ^ G.a + 1) (2 ^ G.b) δ} (sel : X.ShrinkSelection B)
  (site : Site X) (m : Memory w) (level term : Word w)
private noncomputable local instance histogramBase : DecidableEq X.Base := Classical.decEq _
variable {side : Bool}
variable (R : MapRowSource X sel side m level term) (i : Fin (order X side site).length)
  (I : LocalHistory.EntryInput B) {motif : X.packingData.Motif}
  (J : ShrinkPartyNative.Job (a := G.a) (b := G.b) (g := g) X B ready sel motif I.party w)
  (hw : MapConstants.widthThreshold B ≤ w) (P : Fin 5 → Word w)
  (W : Workspace F demandMass_pos I) (saved : DFS.Scratch w endAddr)

local notation "key" => Prod.mk (demandGrid B demandMass_pos I.demand) I.party
local notation "st" => rowOrdinalWord (w := w) (a := G.a) (g := g) X side site i
local notation "ptr" => PhaseRecipe.Expr.eval P (st) m (F.base key)
local notation "ptrAt" stage:max => PhaseRecipe.Expr.eval P stage m (F.base key)
local notation:max "bin" l:max => ((W.hist + Fin.val (l : Fin t) : ℕ) : Word w)

set_option maxHeartbeats 1800000 in
-- The gathered map and its scratch use the same dependent field buffers.
/-- A successful gather and map add the selected matrix multiplicities to the incoming counters. -/
theorem gathered_histogram (stage : Word w) {baseline : Word w → Word w}
    (packets : J.Packets packetEnd baseline)
    (floor : endAddr ≤ W.hist)
    (fit : (ptrAt stage).val + Fintype.card ShrinkCallFields.Arg ≤ 2 ^ w)
    (below : W.hist + t ≤ J.scratch.staging)
    (descriptor : ∀ l : Fin t, (bin l).val < (ptrAt stage).val ∨
      (ptrAt stage).val + Fintype.card ShrinkCallFields.Arg ≤ (bin l).val)
    (directory : ∀ (l : Fin t) (k : MapDirectoryInit.Row (F.layout key).core),
      bin l ≠ W.directory + (k.val : Word w))
    {es : List (Event w)} {out : DFS.Scratch w endAddr}
    (got : gatheredAction (g := g) F G (X := X) (ready := ready) (selection := sel) (motif := motif)
      I J hw P stage m W saved = some (es, out)) :
    ∀ l : Fin t, NodeArguments.rawScratch out (bin l) = NodeArguments.rawScratch saved (bin l) +
      (((names F demandMass_pos I).getD []).count l : Word w) := by
  unfold gatheredAction at got
  obtain ⟨⟨_, last⟩, raw, eq₂⟩ := Option.map_eq_some_iff.mp got
  obtain ⟨good, _, upper⟩ := (F.action_some_iff demandMass_pos I hw P stage m W endAddr
    (J.updated endAddr saved)).mp raw
  intro l
  have value : (bin l).val = W.hist + l.val :=
    Nat.mod_eq_of_lt ((Nat.add_lt_add_left l.isLt W.hist).trans_le W.histogramFit)
  have live : endAddr ≤ (bin l).val := by
    rw [value]
    exact floor.trans (Nat.le_add_right ..)
  have low : (bin l).val < J.scratch.staging := by
    rw [value]
    exact (Nat.add_lt_add_left l.isLt _).trans_le below
  rw [← (Prod.mk.inj eq₂).2, upper]
  exact (MapScratch.upper_histogram (F.layout key).core (F.layout key).args
    ((F.layout key).corePC (F.layout key).locations) W (ptrAt stage) _ F.ordinal endAddr
    (J.updated endAddr saved) good l live fit (descriptor l) (directory l)).trans
    (congrArg (· + _) (J.updated_below packets saved (bin l) low))

set_option maxHeartbeats 1800000 in
-- The gather, map and trace share dependent indices for the selected layout and row.
/-- A successful resident row adds its own parameter multiplicities to the incoming counters. -/
theorem rowAction_histogram {baseline : Word w → Word w} (packets : J.Packets packetEnd baseline)
    (bounds : Bounds F demandMass_pos I W endAddr ptr)
    (fit : (ptr).val + Fintype.card ShrinkCallFields.Arg ≤ 2 ^ w)
    (below : W.hist + t ≤ J.scratch.staging)
    (descriptor : ∀ l : Fin t, (bin l).val < (ptr).val ∨
      (ptr).val + Fintype.card ShrinkCallFields.Arg ≤ (bin l).val)
    (directory : ∀ (l : Fin t) (k : MapDirectoryInit.Row (F.layout key).core),
      bin l ≠ W.directory + (k.val : Word w))
    {es : List (Event w)} {out : DFS.Scratch w endAddr}
    (got : rowAction (g := g) (ready := ready) (side := side) (jobMotif := motif)
      F G X sel site m level term R i I J hw P W saved = some (es, out)) :
    ∀ l : Fin t, NodeArguments.rawScratch out (bin l) = NodeArguments.rawScratch saved (bin l) +
      (((names F demandMass_pos I).getD []).count l : Word w) := by
  unfold rowAction at got
  obtain ⟨⟨_, next⟩, gathered, eq₁⟩ := Option.map_eq_some_iff.mp got
  rw [← (Prod.mk.inj eq₁).2]
  exact gathered_histogram (g := g) F G X sel m I J hw P W saved (st)
    packets bounds.histogramBase fit below descriptor directory gathered

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
