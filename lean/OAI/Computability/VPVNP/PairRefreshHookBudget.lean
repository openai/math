import OAI.Computability.VPVNP.PairRefreshHookSite
import OAI.Computability.VPVNP.PairRefreshTraversalQuiet
import OAI.Computability.VPVNP.PairMapSuccessBudget
import OAI.Computability.VPVNP.PairVertexOrdinalRoleCost

/-! # The cost of the selected refresh reader

The canonical trace includes every public load, guessed old wire bit and
private motif instruction. One fixed scan coefficient bounds the probes of
the dispatched job on every selected branch. The work threshold is independent
of the row, field specialization and branch choices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.Site

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords CompressorRecords.PortRefresh
open RefreshMapOperands MotifConversion NewSlots LocalHistory NodeArguments
open TraversalControllerInputs VertexImage DFS PhaseRecipe
open private eval_cost from OAI.Computability.VPVNP.CompressorRecordsRowRecipe
open private lines_probes from OAI.Computability.VPVNP.CompressorRecordRegisterSetup

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {w n hist t : ℕ}
  (R : Site B n hist w) (ties : Fin t ≃ Tie (2 ^ S.portExponent))
  (stride : ℕ) (order : B.Entry ≃ Fin hist)
  (pub : Fin 11 → BurstRAM.Word w) (m : Memory w)

local notation "D" => 2 ^ S.portExponent
local notation "T" => TraversalPlan.plan B ties stride order
local notation "K₀" => TraversalPlan.budget B ties stride order
local notation "X" => Site.state R
local notation "v" => Site.port R
local notation "ws" => groupedWidths (bitWordFinEquiv _) (splitWidths X)
local notation "perm" => oldPortMatching (splitSlots X) (bitWordFinEquiv _)
local notation "wo" => ws (v, Prod.snd v)
local notation "wi" => ws (Equiv.symm perm (v, Prod.snd v))
local notation "copies" =>
  repetitions B.refresh (blockDemandWidths (splitSlots X) (bitWordFinEquiv _)
    (splitWidths X) (Prod.fst v))

private theorem ticks (a : ℕ) : countProbes (List.replicate a (.tick : Event w)) = 0 := by
  induction a with
  | zero => rfl
  | succ a h => simpa only [List.replicate_succ, countProbes] using h

private theorem setup_cost {a : ℕ} (f : Fin a → Expr) (heads : Fin 5 → BurstRAM.Word w)
    (st : BurstRAM.Word w) (mem : Memory w) :
    let es := RefreshResidentImage.Plan.setupEvents f heads st mem
    es.length = (RegisterSetup.lines f).length ∧ countProbes es = ∑ i, (f i).loads :=
  ⟨(eval_cost heads st mem (RegisterSetup.lines f) (fun _ => 0)).1,
    lines_probes f heads st mem (fun _ => 0)⟩

set_option maxHeartbeats 1100000 in
-- The trace uses the same dependent finite map index in three instruction banks.
/-- Count the actual map trace, including both diagonal widths and each
repetition, independently of the other resident registers. -/
theorem action_cost {old : R.state.network.Half R.olderSite}
    {new : R.nextState.network.Half R.newerSite}
    {s updated : Scratch w n} {es : List (Event w)}
    (hit : R.action ties stride order pub m old new s = some (es, updated)) :
    countProbes es ≤ K₀ ∧ es.length ≤ K₀ * (wo + wi + copies + 1) := by
  rw [TraversalPlan.canonicalAction_events B ties stride order R.state R.choice R.port R.degree n
    R.rowEnd R.oldNode R.parent R.room old new m (levelHead pub m R.level).val
    (levelHead pub m (R.level + 1)).val R.geometry hit]
  let I := entryInput B R.state R.choice R.port old new
  let z := demandGrid B.refresh (fun _ => zero_lt_one) I.demand
  let heads := TraversalPlan.operands
    ((sites R.state.baseIndex (bitWordFinEquiv R.lanes)) R.port).val
    R.parent (levelHead pub m (R.level + 1)).val R.regions.histBase R.geometry
  let st : BurstRAM.Word w := word (levelHead pub m R.level).val
  have mapCost := (T).family.successEvents_cost (fun _ => zero_lt_one) I R.room.tableWidth
    heads st m
  have diag := setup_cost (T).diagonal heads st m
  have route := setup_cost (T).route heads st m
  obtain ⟨probe, work⟩ := (T).uniform.choose_spec z R.port.2 wo wi copies
  let clk := RefreshResidentDispatch.chainTicks
    ((RefreshResidentDispatch.gridOrder B).symm z).val R.port.2.val
  let map := (T).family.successEvents (fun _ => zero_lt_one) I R.room.tableWidth heads st m
  let d := RefreshResidentImage.Plan.setupEvents (T).diagonal heads st m
  let r := RefreshResidentImage.Plan.setupEvents (T).route heads st m
  let es' := List.replicate 4 (.tick : Event w) ++
    (((d ++ List.replicate (7 * (wo + wi) + 9) .tick) ++
    (r ++ List.replicate clk .tick)) ++ map)
  change countProbes es' ≤ (T).uniform.choose + 4 ∧
    es'.length ≤ ((T).uniform.choose + 4) * (wo + wi + copies + 1)
  let fields := (T).family.fields (z, R.port.2)
  have mapProbe : countProbes map =
      ∑ i, ((MapArgumentWriter.recipes (T).directory fields) i).loads := mapCost.2
  have mapWork : map.length ≤ MapArgumentWriter.clock (T).directory fields +
      MapInline.cap B.refresh (T).ordinal z R.port.2 copies := mapCost.1
  change d.length = _ ∧ countProbes d = _ at diag
  change r.length = _ ∧ countProbes r = _ at route
  change (RegisterSetup.lines (T).diagonal).length + (7 * (wo + wi) + 9) +
    ((RegisterSetup.lines (T).route).length + clk) + _ ≤ _ at work
  simp only [es', List.length_append, List.length_replicate, countProbes_append, ticks,
    diag.1, diag.2, route.1, route.2, mapProbe, Nat.add_zero, Nat.zero_add, Nat.add_mul]
  have four : 4 ≤ 4 * (wo + wi + copies + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  dsimp only [fields] at *
  constructor <;> omega

/-- The successful parser trace includes the locator, the singleton input
packet and the selected map. -/
theorem read_cost {node : BurstRAM.Word w} {s : Scratch w n} {bs out tail}
    (hit : R.read ties stride order pub m node s bs = some (out, tail)) :
    countProbes out.trace ≤ 15 + R.later + 3 * D + K₀ ∧
      out.trace.length ≤ 63 + 6 * R.later + 16 * D +
        6 * (packed R.state R.olderSite out.value.1).length + K₀ * (wo + wi + copies + 1) := by
  obtain ⟨_, _, es, hit', traceEq⟩ := (RefreshHook.read_some_iff R.state R.olderSite R.nextState
    R.newerSite R.arena R.oldNode R.parent (R.front pub m) (R.action ties stride order pub m)
    node s bs out tail).mp hit
  obtain ⟨probes, len⟩ := R.action_cost ties stride order pub m hit'
  have front := RefreshVertexAssembly.inputTrace_cost S.portExponent R.state R.olderSite out.value.1
    R.prev m R.listHead pub node R.level R.later
  rw [traceEq, List.length_append, countProbes_append]
  exact ⟨Nat.add_le_add front.2.1.le probes, Nat.add_le_add front.1.le len⟩

variable (B)

/-- The external probe coefficient, including the single role dispatch. -/
noncomputable def scan := 16 + 3 * D + K₀ + (S.steps + 1)

open Filter

/-- A single length threshold works for every represented site of every
branch. The dispatch trace is charged as part of this same visit. -/
theorem eventually_ordinal_cost :
    ∀ᶠ n : ℕ in atTop, ∀ {w : ℕ} (R : Site B n hist w) (pub : Fin 11 → BurstRAM.Word w)
      (m : Memory w) (offset node : BurstRAM.Word w) (s : Scratch w n) (bs out tail)
      (j : VisitPath w n),
      R.later ≤ (S.steps + 1) * (n.log2 + 1) →
      R.read ties stride order pub m node s bs = some (out, tail) →
      j.trace = dispatchEvents m offset node ++ out.trace →
      ordinalJobCost n 1 (scan B ties stride order) j := by
  let C := 72 + 16 * D + 6 * (S.steps + 1) + 12 * D + 3 * K₀
  filter_upwards [eventually_ge_atTop (2 * C), eventually_ge_atTop 2] with n hn two
  intro w R pub m offset node s bs out tail j later hit path
  obtain ⟨probe, time⟩ := R.read_cost ties stride order pub m hit
  obtain ⟨dispatchProbe, dispatchTime, _⟩ := dispatchEvents_cost m offset node
  have oldBits := (packed_length_le R.state R.olderSite out.value.1).trans
    (Nat.mul_le_mul_left _ R.room.oldWidth)
  have width (e) : groupedWidths (bitWordFinEquiv _) (splitWidths R.state) e ≤ n :=
    (R.state.width_le_maxWireWidth _).trans R.room.oldWidth
  have outWidth := width (R.port, R.port.2)
  have inWidth := width
    ((oldPortMatching (splitSlots R.state) (bitWordFinEquiv _)).symm (R.port, R.port.2))
  have copyBound := R.room.copyBound
  have log_le : n.log2 ≤ n := by simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 n
  have visit := Nat.mul_le_mul_left K₀
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add outWidth inWidth) copyBound) 1)
  have stepBound := Nat.mul_le_mul_left 6
    (later.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right log_le 1)))
  have bitsBound := Nat.mul_le_mul_left 6 oldBits
  constructor
  · rw [path, countProbes_append, dispatchProbe, pow_one]
    have fixed := Nat.le_mul_of_pos_right (16 + 3 * D + K₀) (Nat.succ_pos n.log2)
    change _ ≤ (16 + 3 * D + K₀ + (S.steps + 1)) * (n.log2 + 1)
    rw [Nat.add_mul]
    exact (show 1 + countProbes out.trace ≤ (16 + 3 * D + K₀) + R.later by omega).trans
      (Nat.add_le_add fixed later)
  · rw [path, List.length_append]
    have constant := Nat.le_mul_of_pos_right (72 + 16 * D) (Nat.succ_pos n)
    have bits : 6 * (2 * D * n) ≤ 12 * D * (n + 1) := by
      calc
        _ = 12 * D * n := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_succ n)
    have reps : K₀ * (n + n + n + 1) ≤ 3 * K₀ * (n + 1) := by
      rw [Nat.mul_comm 3 K₀, Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (by omega)
    have linear : (dispatchEvents m offset node).length + out.trace.length ≤ C * (n + 1) := by
      calc
        _ ≤ 72 + 16 * D + 6 * R.later +
            6 * (packed R.state R.olderSite out.value.1).length + _ := by
          exact (Nat.add_le_add dispatchTime time).trans_eq (by omega)
        _ ≤ (72 + 16 * D) * (n + 1) + 6 * ((S.steps + 1) * (n + 1)) +
            12 * D * (n + 1) + 3 * K₀ * (n + 1) :=
          Nat.add_le_add
            (Nat.add_le_add (Nat.add_le_add constant stepBound) (bitsBound.trans bits))
            (visit.trans reps)
        _ = C * (n + 1) := by dsimp [C]; ring
    calc
      _ ≤ C * (n + 1) := linear
      _ ≤ C * (2 * n) := Nat.mul_le_mul_left C (by omega)
      _ = (2 * C) * n := by ring
      _ ≤ n ^ 2 := (Nat.mul_le_mul_right n hn).trans_eq (pow_two n).symm
      _ ≤ n ^ 43 := Nat.pow_le_pow_right (by omega) (by decide)

end PairSimulation.RefreshHook.Site

end VPVNP
end Computability
end OAI
