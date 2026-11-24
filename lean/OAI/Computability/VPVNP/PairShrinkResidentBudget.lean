import OAI.Computability.VPVNP.PairShrinkScanCoefficient
import OAI.Computability.VPVNP.PairShrinkRowBudget
import OAI.Computability.VPVNP.PairShrinkNodeClock
import OAI.Computability.VPVNP.PairShrinkRoleMapActions
import OAI.Computability.VPVNP.ShrinkFieldBounds

/-! # Cost of the shrinking vertex's real resident map scan

Each row uses the demand sizes of its selected motif. The native clock
therefore depends linearly on the maximum input width. The probe count
is independent of that width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.MapWitness

open BurstRAM DFS Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords CompressorRecords.ShrinkSlots ShrinkMapImage.Registers
open ResidentMapLoop.Exact MapResidentRows MotifGrid MotifConversion MotifBlocks

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  {t w endAddr : ℕ} (ord : B.Entry → Fin t) (i : Fin S.steps) {g : ℕ}
  (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
  (sel : X.ShrinkSelection B.shrink) (v : MapResidentRows.Site X)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

local notation "side" => selectedLayout X B.shrink sel
local notation "F" => ShrinkVertexImage.matrixFamily B ord i
local notation "G" => ShrinkVertexImage.gatherFamily B ord i
local notation "idx" => Fin (LocalHistory.Order.length (order X side v))

variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel)) v)
  (jobs : (q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v) →
    ShrinkPartyNative.Job X B.shrink (S.shrink i) sel q.1.1 q.1.2 w)
  (m : Memory w) (level term : Word w)
  (R : MapRowSource X sel (selectedLayout X B.shrink sel) m level term)
  (hw : MapConstants.widthThreshold B.shrink ≤ w)
  (pub : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v → Fin 5 → Word w)
  (workspace : (q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v) →
    MapHandlerOperand.Workspace (w := w) (ShrinkVertexImage.matrixFamily B ord i)
      demandMass_pos (jobInput B i X sel v hidden jobs q))

/-- The sizes here are the demand sizes used by the concrete matrix call. -/
theorem job_repetitions (q : X.packingData.ResidentMap side v) :
    repetitions B.shrink (jobInput B i X sel v hidden jobs q).demand ≤
      fieldFactor B.shrink * (X.maxWireWidth+1) :=
  (linear_field_bounds B.shrink _ _ (X.packingData.shrinkDemandWidths_le
    (State.two_le_packingColors _) (Nat.two_pow_pos _) X.shrinkNumber X.packingWidth
    (fun _ => X.width_le_maxWireWidth _) q.1.1)).1

local notation "cap" => MapResidentRows.capacity (S.degreeExponent i.castSucc)
local notation "call" => jobInput B i X sel v hidden jobs
local notation "qAt" => rowEquiv X side v
private noncomputable def gatherEvents (j : idx) : List (Event w) :=
  let q := (qAt) j
  let key := (demandGrid B.shrink demandMass_pos ((call) q).demand, ((call) q).party)
  (jobs q).trace ((G).operands key) ((G).node key) (pub q)
    (rowOrdinalWord (a := S.degreeExponent i.castSucc) (g := g) X side v j) m

local notation "gTrace" => gatherEvents B ord i X sel v hidden jobs m pub

set_option maxHeartbeats 2000000 in
-- Identify the party-indexed workspace and the selected row at each resident iteration.
theorem scan_cost (gTicks gProbes : ℕ)
    (gather : ∀ j : idx, ((gTrace) j).length ≤ gTicks ∧
      countProbes ((gTrace) j) ≤ gProbes)
    (node : Word w) (saved updated : Scratch w endAddr) (es : List (Event w))
    (hit : scan node (actions B ord i X sel v hidden jobs m level term R hw pub workspace) saved =
      some (es, updated)) :
    es.length ≤ 1 + 2*cap + cap*(27+2*Fintype.card B.shrink.grid.demands + gTicks +
      matrixFactor B ord i * (X.maxWireWidth+1)) ∧
    countProbes es ≤ cap*(3+gProbes+(F).probeBound) := by
  let action (j : idx) : Action w endAddr := fun _ s =>
    let q := (qAt) j
    rowAction (g := g) («side» := side) (ready := S.shrink i) (F) (G) X sel v m level term R j
      ((call) q) (jobs q) hw (pub q) (workspace q) s
  let rows := List.finRange (order X side v).length
  have actual : (rows.map action) = actions B ord i X sel v hidden jobs m level term R hw pub
      workspace := by
    exact List.ofFn_eq_map.symm
  let ticks := 27+2*Fintype.card B.shrink.grid.demands + gTicks +
    matrixFactor B ord i * (X.maxWireWidth+1)
  let loads := 3+gProbes+(F).probeBound
  have row (j : idx) (s : Scratch w endAddr) (log : List (Event w)) (out : Scratch w endAddr)
      (got : action j node s=some (log,out)) : log.length≤ticks ∧ countProbes log≤loads := by
    let q := (qAt) j
    let I := (call) q
    let key := (demandGrid B.shrink demandMass_pos I.demand, I.party)
    let u := repetitions B.shrink I.demand
    let C := (MapNativeClock.uniform B.shrink).choose
    obtain ⟨time,probe⟩ :=
      rowAction_cost (g := g) («side» := side) (ready := S.shrink i) (F) (G) X sel v m level term
        R j I
        (jobs q) hw (pub q) (workspace q) s got
    obtain ⟨gt,gp⟩ := gather j
    have rep := job_repetitions B i X sel v hidden jobs q
    change u ≤ fieldFactor B.shrink * (X.maxWireWidth+1) at rep
    have clock : (F).clock key u ≤ matrixFactor B ord i * (X.maxWireWidth+1) := by
      refine ((F).clock_le key u).trans ?_
      have hC : MapNativeClock.cap B.shrink key.1 key.2 u ≤ C*(u+1) :=
        (MapNativeClock.uniform B.shrink).choose_spec key.1 key.2 u
      calc
        _ ≤ (F).clockFactor * ((C+1)*(u+1)) := Nat.mul_le_mul_left _ (by rw [Nat.add_mul]; omega)
        _ ≤ (F).clockFactor * ((C+1)*((fieldFactor B.shrink+1)*(X.maxWireWidth+1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by rw [Nat.add_mul]; omega))
        _ = _ := by unfold matrixFactor; dsimp only [C]; ring
    change log.length ≤ 15+2*Fintype.card B.shrink.grid.demands+12+
      ((gTrace) j).length+(F).clock key u at time
    change countProbes log=3+countProbes ((gTrace) j)+(F).probes key at probe
    have base (k : ℕ) : 15+2*k+12=27+2*k := by omega
    rw [base] at time
    refine ⟨time.trans (Nat.add_le_add (Nat.add_le_add_left gt _) clock), ?_⟩
    rw [probe]
    exact Nat.add_le_add (Nat.add_le_add_left gp _) ((F).probes_le key)
  have result :=
    ShrinkNodeCost.scan_cost rows action (fun _ => ticks) (fun _ => loads) node saved updated es
    (fun j _ => row j) (by rwa [actual])
  have size : rows.length=cap := (List.length_finRange ..).trans (MapResidentRows.length_eq ..)
  simpa only [List.map_const',List.sum_replicate_nat,size,ticks,loads] using result

set_option maxHeartbeats 2000000 in
-- The dependent jobs project the same indexed layout and packed operand width.
/-- An accepted real row list at any shrinking stage, for every incoming
upper scratch. The coefficient only depends on the original templates
and the chosen finite entry numbering. -/
theorem scan_bound (node : Word w) (saved updated : Scratch w endAddr) (es : List (Event w))
    (hit : scan node (actions B ord i X sel v hidden jobs m level term R hw pub workspace) saved =
      some (es, updated)) :
    es.length ≤ scanCoefficient B ord * (X.maxWireWidth+1) ∧
    countProbes es ≤ scanCoefficient B ord := by
  let Q := (G).clockConstant (fieldFactor B.shrink+1)
  let W := X.maxWireWidth+1
  have each (j : idx) : ((gTrace) j).length ≤ Q*W ∧ countProbes ((gTrace) j)≤Q :=
    (G).trace_bound (g := g) (X := X) (ready := S.shrink i) (sel := sel)
      (demandGrid B.shrink demandMass_pos ((call) ((qAt) j)).demand)
      (jobs ((qAt) j)) (pub ((qAt) j))
      (rowOrdinalWord (a := S.degreeExponent i.castSucc) (g := g) X side v j) m
  obtain ⟨clock,probe⟩ := scan_cost B ord i X sel v hidden jobs m level term R hw pub workspace
    (Q*W) Q each node saved updated es hit
  have stage : stageCoefficient B ord i ≤ scanCoefficient B ord :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (stageCoefficient B ord j)) (Finset.mem_univ i)
  let fixed := 27+2*Fintype.card B.shrink.grid.demands
  let factor := matrixFactor B ord i
  have first : 1+2*cap ≤ (1+2*cap)*W := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have second : fixed ≤ fixed*W := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have localClock : es.length ≤ stageCoefficient B ord i * W := by
    refine clock.trans ?_
    change 1+2*cap + cap*(fixed+Q*W+factor*W) ≤
      (1+2*cap+cap*(fixed+Q+factor)+cap*(3+Q+(F).probeBound))*W
    rw [Nat.add_mul,Nat.add_mul, Nat.mul_assoc, Nat.add_mul (fixed+Q), Nat.add_mul fixed]
    exact (Nat.add_le_add first (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.add_le_add_right second _) _))).trans
      (Nat.le_add_right ..)
  exact ⟨localClock.trans (Nat.mul_le_mul_right _ stage),
    probe.trans ((Nat.le_add_left ..).trans stage)⟩

end PairSimulation.ShrinkRole.MapWitness

end VPVNP
end Computability
end OAI
