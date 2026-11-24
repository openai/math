import OAI.Computability.VPVNP.CompressorTermWorkerRecipe
import OAI.Computability.VPVNP.CompressorShrinkTermInputs
import OAI.Computability.VPVNP.CompressorBundleKeyTable

/-!
# Online row planners for the shrinking motif gather and selection

Both phases visit one row per CD occurrence. The packed AB width and offset
rectangles precede the dense pair array, followed by the selected term rows.
The sorted CD widths occupy the second half of the sorted-width rectangle.
The planner obtains its shape scalars and allocation heads from level expressions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkTermRecipe

open BurstRAM BurstRAM.PrivateRAM PhaseRecipe Compression Compression.PackingData MotifConversion MotifGrid MotifBlocks
open scoped Fin.CommRing
open private pieces_arithmetic from OAI.Computability.VPVNP.SlotDemandEnergy

/-- Dynamic scalars and addresses read by the two planners. -/
structure Inputs where
  /-- Expression for the number of input base vertices at the selected shrinking level. -/
  vertices : Expr
  /-- Expression for the input degree used to count bundles and old port slots. -/
  degree : Expr
  /-- Expression for the number of input lanes per base vertex before shrinking. -/
  lanes : Expr
  /-- Expression for the residual lane count used to enumerate packed bundles. -/
  residualLanes : Expr
  /-- Base-address expression for the two sorted thick and CD width rectangles. -/
  sortedWidth : Expr
  /-- The row stride expression shared by the per-bundle sorted-width rectangles. -/
  sortedStride : Expr
  /-- The starting address expression for the balanced AB pieces, ahead of the dense pair and
  term tables. -/
  abStart : Expr

variable (a stride : ℕ) (I : Inputs)

/-- Number of CD motif ranks per bundle, computed from the input degree and the shrinking color
count. -/
def ranks (a : ℕ) := pieceCount (2^a) (Shrink.colors a)

/-- The runtime bundle count obtained from base vertices, tags, residual lanes and input
degree. -/
def bundles := (I.vertices.mul ((Expr.lit (2^(Shrink.J a))).mul I.residualLanes)).mul I.degree
/-- The runtime count of old directed slots over all base vertices and input lanes. -/
def oldSlots := (I.vertices.mul I.lanes).mul I.degree
/-- Total number of dense term visits, one for every bundle and motif rank. -/
def count := (bundles a I).mul (.lit (ranks a))
/-- The head of the sorted CD widths, following the entire thick-width rectangle. -/
def cdStart := I.sortedWidth.add ((bundles a I).mul I.sortedStride)
/-- Head of the dense two-word AB/CD demand pairs, following the AB width and offset
rectangles. -/
def dense := I.abStart.add ((Expr.lit 2).mul (count a I))
/-- Head of the selected term records, immediately after all dense demand pairs. -/
def term := (dense a I).add ((Expr.lit 2).mul (count a I))
/-- Exclusive end of the selected term table at the supplied record stride. -/
def stopAddress := (term a I).add ((count a I).mul (.lit stride))

/-- The rank counts, sorted stride and AB, CD and dense output heads used by the paired demand
gather. -/
def gatherOperands : Fin 6 → Expr :=
  ![.lit (ranks a),.lit (ranks a),I.sortedStride,I.abStart,cdStart a I,dense a I]

/-- The selector's dense demand base and stride of two, followed by the selected term base and
record stride. -/
def termHeads : Fin 4 → Expr := ![dense a I,.lit 2,term a I,.lit stride]

variable {k : Type*} [_root_.Field k] {H' : ℝ} (F : FixedBlock k ShrinkMotif.demandSource ShrinkMotif.demandTarget
  ShrinkMotif.supply (realWidths ShrinkMotif.demandMass) (realWidths ShrinkMotif.supplyMass) (31/16) H')
variable (supply : Fin 8 ≃ Bool × Fin 4)

/-- A planner phase launching the paired demand gather from zero over the full dense motif
count. -/
def gatherPhase {G : ℕ} (tag : ℕ) (room : 6 ≤ G) : Phase G :=
  Phase.ofParams room tag (.lit 0) (count a I) (gatherOperands a I)

/-- A planner phase launching the fused motif term selector with the computed addresses and
fixed supply ordering. -/
noncomputable def termPhase {G : ℕ} (tag : ℕ) (room : (TermWorker.motifPass F finTwoEquiv 8).params ≤ G) :
    Phase G :=
  Phase.ofParams room tag (.lit 0) (count a I) (TermWorker.motifExprs F finTwoEquiv supply (termHeads a stride I))

variable {a} {g w : ℕ} (X : State a (packingLaneBits a g))

/-- Number of base vertices in the input state used by the term recipe's address formulas. -/
abbrev N := Fintype.card X.Base
/-- The concrete number of packed bundles in this input state for the given degree and residual
lane exponents. -/
abbrev B := BundleKeys.numBundles (N X) a g
/-- The concrete number of dense motif rows, equal to the bundle count times the number of
ranks per bundle. -/
abbrev M := B X * ranks a
/-- Number of original directed input ports across the base vertices and all uncompressed
packing lanes. -/
abbrev originalSlots := (N X * 2^(packingLaneBits a g)) * 2^a

/-- The chosen physical interval indexes every motif exactly once. -/
theorem count_card : M X = ShrinkTermInputs.motifCount X :=
  ((Fintype.card_congr (ShrinkMotifOrder.stateNumber X)).trans (Fintype.card_fin _)).symm

/-- Exact cardinality before taking any word reduction. -/
theorem four_count : 4 * M X = 3 * originalSlots X := by
  let h := 2^(Shrink.colors a) * 2^a / 4
  have hq : ranks a = 3*h := (pieces_arithmetic (State.two_le_packingColors a) (Nat.two_pow_pos a)).1
  have total := BundleKeys.bundle_rows_total (N X) a g
  change B X*h + B X*ranks a = originalSlots X at total
  change 4*(B X*ranks a) = _
  rw [← total,hq]; ring

theorem count_le_slots : M X ≤ originalSlots X := by have := four_count X; omega

theorem count_eq_three_quarters : M X = 3*originalSlots X/4 := by have := four_count X; omega

variable (pub : Fin 5 → BurstRAM.Word w) (state : BurstRAM.Word w) (mem : Memory w)

/-- The input fields describe the current dyadic state and the already packed
source rectangle. The AB width rectangle starts at the supplied allocator cursor. -/
structure Describes (sorted : Fin 5 → BurstRAM.Word w) (abStart : ℕ) : Prop where
  vertices : I.vertices.eval pub state mem = (N X : BurstRAM.Word w)
  degree : I.degree.eval pub state mem = (2^a : ℕ)
  lanes : I.lanes.eval pub state mem = (2^(packingLaneBits a g) : ℕ)
  residual : I.residualLanes.eval pub state mem = (2^g : ℕ)
  sortedWidth : I.sortedWidth.eval pub state mem = sorted 4
  sortedStride : I.sortedStride.eval pub state mem = sorted 3
  abHead : I.abStart.eval pub state mem = (abStart : BurstRAM.Word w)

variable {sorted : Fin 5 → BurstRAM.Word w} {abStart : ℕ} (h : Describes I X pub state mem sorted abStart)
local notation "ev" => Expr.eval pub state mem

include h in
theorem eval_bundles : ev (bundles a I) = (B X : BurstRAM.Word w) := by
  simp only [bundles,Expr.mul,Expr.eval,BinaryOp.eval,h.vertices,h.degree,h.residual,← Nat.cast_mul]; rfl

include h in
theorem eval_oldSlots : ev (oldSlots I) = (originalSlots X : BurstRAM.Word w) := by
  simp only [oldSlots,Expr.mul,Expr.eval,BinaryOp.eval,h.vertices,h.degree,h.lanes,← Nat.cast_mul]

include h in
theorem eval_count : ev (count a I) = (M X : BurstRAM.Word w) := by
  change ev (bundles a I) * (ranks a : BurstRAM.Word w) = _
  rw [eval_bundles I X pub state mem h,Nat.cast_mul]

include h in
theorem eval_dense : ev (dense a I) = ((abStart+2*M X : ℕ) : BurstRAM.Word w) := by
  change ev I.abStart + 2*ev (count a I) = _
  simp only [h.abHead,eval_count I X pub state mem h,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]

include h in
theorem eval_term : ev (term a I) = ((abStart+2*M X+2*M X : ℕ) : BurstRAM.Word w) := by
  change ev (dense a I) + 2*ev (count a I) = _
  simp only [eval_dense I X pub state mem h,eval_count I X pub state mem h,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]

include h in
theorem eval_stopAddress : ev (stopAddress a stride I) =
    ((abStart+2*M X+2*M X+M X*stride : ℕ) : BurstRAM.Word w) := by
  change ev (term a I) + ev (count a I)*(stride : BurstRAM.Word w) = _
  simp only [eval_term I X pub state mem h,eval_count I X pub state mem h,Nat.cast_add,Nat.cast_mul]

include h in
theorem stop_val (fits : originalSlots X < 2^w) : (ev (count a I)).val = ShrinkTermInputs.motifCount X := by
  rw [eval_count I X pub state mem h,Fin.val_natCast,Nat.mod_eq_of_lt ((count_le_slots X).trans_lt fits),count_card]

include h in
theorem gather_bank (prefixHead : ℕ) (total : BurstRAM.Word w) :
    (fun i => ev (gatherOperands a I i)) = ShrinkTermInputs.operands
      (BundlePrefixGraph.prefixPublic sorted (B X) (2^a) (Shrink.colors a) prefixHead true)
      (DemandWidths.packedPublic total (B X) (ranks a) abStart)
      ((abStart+2*M X : ℕ) : BurstRAM.Word w) := by
  have cd : ev (cdStart a I) = (((sorted 4).val+B X*(sorted 3).val : ℕ) : BurstRAM.Word w) := by
    change ev I.sortedWidth + ev (bundles a I)*ev I.sortedStride = _
    simp [h.sortedWidth,h.sortedStride,eval_bundles I X pub state mem h]
  funext i
  fin_cases i <;> first | exact cd | exact eval_dense I X pub state mem h | exact h.sortedStride | exact h.abHead | rfl

include h in
theorem term_bank :
    (fun i => ev (TermWorker.motifExprs F finTwoEquiv supply (termHeads a stride I) i)) =
      TermWorker.motifData F finTwoEquiv supply w
        ![((abStart+2*M X : ℕ) : BurstRAM.Word w),2,((abStart+2*M X+2*M X : ℕ) : BurstRAM.Word w),stride] := by
  rw [TermWorker.eval_motifExprs]
  congr 1
  funext i
  fin_cases i <;> first | exact eval_dense I X pub state mem h | exact eval_term I X pub state mem h | rfl

/-- Read back the physical row emitted by the compiled planner. Fields above
the worker arity contain the zero padding of the shared dispatcher frame. -/
def Installed {K G : ℕ} (P : Phase G) (tag limit : ℕ) (bank : Fin K → BurstRAM.Word w) : Prop :=
  let row := Controller.rowBase G pub mem
  let out := after mem (P.recipe.report pub state mem).events
  out row.val = (tag : BurstRAM.Word w) ∧ out (row+1).val = 0 ∧ out (row+2).val = (limit : BurstRAM.Word w) ∧
    ∀ j : Fin G, Controller.field (row+2) out (j.val+1) = if hi : j.val < K then bank ⟨j.val,hi⟩ else 0

private theorem installed {K G : ℕ} (tag limit : ℕ) (stop : Expr) (params : Fin K → Expr) (room : K ≤ G)
    (bank : Fin K → BurstRAM.Word w) (values : (fun i => ev (params i)) = bank)
    (counter : ev stop = (limit : BurstRAM.Word w)) (rowFits : (Controller.rowBase G pub mem).val + (G+3) ≤ 2^w) :
    Installed pub state mem (Phase.ofParams room tag (.lit 0) stop params) tag limit bank := by
  let phase := Phase.ofParams room tag (.lit 0) stop params
  obtain ⟨tagged,first,last,fields⟩ := PhaseRecipe.row_fields phase pub state mem rowFits
  refine ⟨tagged,first,last.trans counter,fun j => ?_⟩
  rw [fields]
  change ev (if hi : j.val < K then params ⟨j.val,hi⟩ else .lit 0) = _
  split <;> first | exact congrFun values _ | rfl

include h in
theorem gather_compiled {G : ℕ} (tag : ℕ) (room : 6 ≤ G) (prefixHead : ℕ) (total : BurstRAM.Word w)
    (rowFits : (Controller.rowBase G pub mem).val+(G+3) ≤ 2^w) :
    Installed pub state mem (gatherPhase a I tag room) tag (ShrinkTermInputs.motifCount X)
      (ShrinkTermInputs.operands
        (BundlePrefixGraph.prefixPublic sorted (B X) (2^a) (Shrink.colors a) prefixHead true)
        (DemandWidths.packedPublic total (B X) (ranks a) abStart) ((abStart+2*M X : ℕ) : BurstRAM.Word w)) :=
  installed pub state mem _ _ _ _ _ _ (gather_bank I X pub state mem h prefixHead total)
    ((eval_count I X pub state mem h).trans (congrArg (fun n : ℕ => (n : BurstRAM.Word w)) (count_card X))) rowFits

include h in
theorem term_compiled {G : ℕ} (tag : ℕ) (room : (TermWorker.motifPass F finTwoEquiv 8).params ≤ G)
    (rowFits : (Controller.rowBase G pub mem).val+(G+3) ≤ 2^w) :
    Installed pub state mem (termPhase a stride I F supply tag room) tag (ShrinkTermInputs.motifCount X)
      (TermWorker.motifData F finTwoEquiv supply w
        ![((abStart+2*M X : ℕ) : BurstRAM.Word w),2,((abStart+2*M X+2*M X : ℕ) : BurstRAM.Word w),stride]) :=
  installed pub state mem _ _ _ _ _ _ (term_bank stride I F supply X pub state mem h)
    ((eval_count I X pub state mem h).trans (congrArg (fun n : ℕ => (n : BurstRAM.Word w)) (count_card X))) rowFits

end CompressorRecords.ShrinkTermRecipe

end VPVNP
end Computability
end OAI
