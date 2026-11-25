import OAI.Computability.BorderVNP.PackedFrozenEdgeRectangle
import OAI.Computability.BorderVNP.PackedFrozenTreeWork
import OAI.Computability.BorderVNP.PackedFrozenNamedKernel
import OAI.Computability.BorderVNP.PackedFrozenNamedEmitReadback
import OAI.Computability.BorderVNP.PackedInheritedWorkSelectedNodeCost

/-! # Sparse work of the selected native kernel including all immutable records -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.StaticRows Shortening.PublicCapacity
open Packing Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords
open EnrichedOuter TeamScales VPVNP.VerifierNetwork SourcePath.NamedRun
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
attribute [local irreducible] Node.frame VPVNP.VerifierNetwork.Frame.size selectedPass carryFrame
set_option maxRecDepth 5000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
variable {start T : ℕ} (deep : S.floor+1+S.drop*T ≤ start) {t : ℕ} (ht : t<T)

variable {S deep ht} {P : Type} [Fintype P] {bits : P → ℕ} {n r : ℕ}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} (R : Compiled bits deep budget cap (60*logWidth r n))
    (base : Format) (hm : 0 < m)
variable (wr : WidthRanges S start T (60*logWidth r n)) (header : WorkWords.Ports (CoverScale.sites (Cube D) start))
    (leaf : P ↪ Fin (CoverScale.sites (Cube D) start))

/-- The complete chronological kernel adds two copies of the true chosen geometry at
most, together with the width, histogram and immutable-record work per actual row.
The circuit in the conclusion is the one that returns every emitted word and flag. -/
theorem Compiled.tapeNative_rows (ht : t<T) (i : Fin S.rounds) (prior : Format) {C p den cut : ℕ}
    (rowCount : Fintype.card prior.Rows ≤ priorSlots S start (Fintype.card base.Rows) t i)
    (writers : NodeWork S hm start t i (Fintype.card base.Rows) (logWidth r n) C p)
    (range : Ranges S r n start t i den cut) (hL : 1≤logWidth r n)
    (hseeds : seedCount S start t i ≤ (CoverScale.sites (Cube D) start)*bins S) :
    (NativeTape.node (R.atLevel t ht).program i prior (header.outer S start t) (privatePorts S leaf t)
      (width_rectangle S deep ht) (tapeEdgeRectangle S deep ht) (wr.successor t ht) hm).size + (2*S.fanIn+4) ≤
      2*((R.machine t ht).step i.val i.isLt).size +
        rowWork (C+186+widthNodeFactor S+(2*S.fanIn+4)) (CoverScale.sites (Cube D) start) (logWidth r n) (max 3 p)
          ((before S start t i).parallel S.fanIn) := by
  let tiles := CoverScale.sites (Cube D) start
  let ports := header.outer S start t
  let portID := privatePorts S leaf t
  let level := R.atLevel t ht
  let shape := (before S start t i).parallel S.fanIn
  let O := level.program.operands i
  let f := prior
  let siteRect := width_rectangle S deep ht
  let cableRect := tapeEdgeRectangle S deep ht
  let fit := wr.successor t ht
  let L := logWidth r n
  have hkey : O.keyBits = PublicDenseReceipt.operandBits D (S.source.pattern i).bins.Bin
      (stageLevel S start t (i.val+1)) := (level.program.keyBits i).trans
    (congrArg (PublicDenseReceipt.operandBits D (S.source.pattern i).bins.Bin) (level_offset S deep ht (i.val+1)))
  have hports : Parallel.nestedCapacity S.fanIn (portCapacity S tiles t) (i.val+1) = portSlots S start t (i.val+1) :=
    WorkWords.path_count S t (i.val+1)
  have seed := ProgramSchemas.stage_seeds S start deep ht i
  have emit : (NativeTape.emit level.program i f ports portID siteRect cableRect fit hm).size ≤ rowWork C tiles L p shape := by
    let V := fun j => (before S start t j).sites
    let E := fun j => (before S start t j).edges
    let high := S.high (offset S start t)
    let w := 60*L
    let Geo := S.source.StatePins S.last high V E w
    let A := ProgramSchemas.Seeds S.source S.last high i
    let Input := (Fin S.fanIn × f.Output (Geo i.val) (V i.val) w w) ⊕ PublicDenseReceipt.Words A e.count w
    let Widths := WithWidths (Geo (i.val+1)) (V (i.val+1)) w
    let σ := Shared.Context Input O.Pin Widths shape.edges w
    let sel : O.Pin → σ := Shared.selected
    let digits (a : A) (u : Fin e.count) (j : Fin w) : σ := Shared.input (.inr (a,u,j))
    let earlier (z : Fin S.fanIn × Pins f.Rows f.Payload w) : σ := Shared.input (.inl (z.1,.inr z.2))
    have room := NativeTape.rawFit e (siteRect i) (fit i)
    have charge := writers.on_rows S f rowCount (σ:=σ) O hkey sel digits seed hports
      (level.program.directorySeed i) ((Nat.le_mul_of_pos_left _ S.positiveFanIn).trans room) room earlier
      (NativeTape.oldFields level.program i f ports siteRect fit)
      (Views.literalFields (NativeTape.newFields level.program i f ports siteRect cableRect fit) Shared.literal)
      (NativeTape.oldWord level.program i f false) (NativeTape.oldWord level.program i f true)
      (sel ∘ O.col.occupied) (NativeTape.portUsed (k:=S.fanIn) i portID)
      (NativeTape.newOccupied level.program i f cableRect)
    unfold NativeTape.emit
    apply (NativeTape.keepPins_size _ _).le.trans
    exact charge
  have full := Shared.install_rowWork shape (le_refl _) hL O
    (NativeTape.geoPin (path := S.source) (last := S.last) (high := S.high (offset S start t))
      (V := fun j => (before S start t j).sites) (E := fun j => (before S start t j).edges) (k := S.fanIn) (w := (60*logWidth r n)) i f)
    (NativeTape.widthStep level.program i f ports siteRect fit) _ emit
  have widths := R.widthSteps_rowWork header le_rfl ht wr i range hL hseeds
  simp only [SourcePath.NamedRun.widthSteps,NamedKernel.scheduled_size] at widths
  have nativeWidth : (NativeTape.widthStep level.program i f ports siteRect fit).size ≤
      (R.nodes t ht i).size+rowWork (widthNodeFactor S) tiles L 3 shape := by
    simpa only [NativeTape.widthStep,Frame.subst_size,Frame.initial_size,Nat.zero_add] using widths
  have comp := level.program.operand_size i
  let W := shape.volume tiles*L^(max 3 p)
  have positive : 1≤W := Nat.mul_pos (show 1 ≤ shape.volume tiles by unfold Shape.volume; omega) (Nat.one_le_pow _ _ hL)
  have extra : (2*S.fanIn+4) ≤ (2*S.fanIn+4)*W := Nat.le_mul_of_pos_right _ positive
  have a : rowWork (C+186) tiles L (max 1 p) shape ≤ (C+186)*W :=
    (Nat.mul_le_mul_left ((C+186)*shape.volume tiles) (Nat.pow_le_pow_right hL (max_le_max_right p (by decide : 1 ≤ 3)))).trans_eq (Nat.mul_assoc ..)
  have b : rowWork (widthNodeFactor S) tiles L 3 shape ≤ widthNodeFactor S*W :=
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL (le_max_left 3 p))).trans_eq (Nat.mul_assoc ..)
  rw [R.node_size t ht i]
  change (Shared.install O _ _ _).size + (2*S.fanIn+4) ≤ _
  apply (Nat.add_le_add_right full _).trans
  calc
    _ ≤ (R.nodes t ht i).size + ((R.nodes t ht i).size+(widthNodeFactor S)*W) + (C+186)*W + (2*S.fanIn+4)*W :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add comp (nativeWidth.trans (Nat.add_le_add_left b _))) a) extra
    _ = _ := by unfold rowWork; dsimp only [W]; ring

/-- In the attained stage format the earlier roster has exactly the number of
slots charged by the native writer. -/
theorem Compiled.tapeNative_rowWork (ht : t<T) (i : Fin S.rounds) {C p den cut : ℕ}
    (writers : NodeWork S hm start t i (Fintype.card base.Rows) (logWidth r n) C p)
    (range : Ranges S r n start t i den cut) (hL : 1≤logWidth r n)
    (hseeds : seedCount S start t i ≤ (CoverScale.sites (Cube D) start)*bins S) :
    (NativeTape.node (R.atLevel t ht).program i (ProgramSchemas.stage S start (60*logWidth r n) base t i.val)
      (header.outer S start t) (privatePorts S leaf t) (width_rectangle S deep ht) (tapeEdgeRectangle S deep ht) (wr.successor t ht) hm).size + (2*S.fanIn+4) ≤
      2*((R.machine t ht).step i.val i.isLt).size +
        rowWork (C+186+widthNodeFactor S+(2*S.fanIn+4)) (CoverScale.sites (Cube D) start) (logWidth r n) (max 3 p)
          ((before S start t i).parallel S.fanIn) :=
  R.tapeNative_rows base hm wr header leaf ht i (ProgramSchemas.stage S start (60*logWidth r n) base t i.val)
    (ProgramSchemas.stage_slots S start (60*logWidth r n) base deep ht i i.isLt.le).le writers range hL hseeds

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
