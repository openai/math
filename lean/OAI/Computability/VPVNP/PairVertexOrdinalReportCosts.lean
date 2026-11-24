import OAI.Computability.VPVNP.PairVertexSelectedPaths
import OAI.Computability.VPVNP.PairSimulationVertexReportBudget

/-! # Time and probes of the actual selected vertex worker -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM Compression DFS LocalHistory NetworkKernel NodeArguments TreeDecode
  TraversalRows
open CompressorRecords SourceTransport TerminalLink
open scoped Fin.CommRing

variable {k R : Type*} [Field k] [CommRing R] {S : BlockSchedule k}
    (B : S.Templates) (κ : B.Entry → R) (hκ : B.IsSolution κ) {lanes : ℕ}
    (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute κ hκ T hT X).Choices) (rowBase : ℕ)
    {geometry rootFields leaf shrink refresh : Segment} {p r w g : ℕ}
    (A : Placement (segments geometry rootFields leaf shrink refresh) p r) (M : Machine w p r 11)
    (base grammar : ℕ) (order : Fin g ≃ B.Entry) (P : SiteParsers κ X.network)

local notation "exec₀" => B.execute κ hκ T hT X
local notation "data₀" => B.records κ hκ T hT X
local notation "chain₀" => StateExecution.termChain (exec₀) (data₀) z
local notation "readers₀" => selectedParsers B κ hκ T hT X z
local notation "trees₀" => selectedTrees B κ hκ T hT X z rowBase
local notation "Y" => StateExecution.finalState (exec₀) z
local notation "ord₀" => siteOrder (Y)
local notation "final₀" => finalParsers (chain₀) (readers₀) P
local notation "head₀" => TerminalLink.header (Machine.publicData M)
local notation "allow₀" => workerCell (head₀)

variable (half : ∀ u, ((B.execute κ hκ T hT X).finalState z).network.Half u)

local notation "selected₀" => siteOrdinals (final₀) (Order.entries (ord₀)) order half

variable {cap : ℕ} {m : Memory w} {i : Fin (siteOrder ((B.execute κ hκ T hT X).finalState
  z)).length}

local notation "rows₀" => OrdinalRows B κ hκ T hT X z rowBase A M base grammar order P half cap m i

open CursorNetwork

private theorem sum_jobs_le {J : Type*} (charge : J → ℕ) (js : List J) (rate : ℕ)
    (each : ∀ j ∈ js, charge j ≤ rate) : (js.map charge).sum ≤ js.length * rate := by
  induction js with
  | nil => simp
  | cons j js ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    exact (Nat.add_le_add (each j List.mem_cons_self) (ih fun t ht => each t (List.mem_cons_of_mem
      _ ht))).trans_eq
      (Nat.add_comm _ _)

/-- Charge a returning native ordinal against its own incident wires and DFS
occurrences. The local cost predicate comes from the installed role handlers.
The directory coefficient, schedule degree and number of parameter labels
are independent of the input length and of the choice at the site. -/
theorem OrdinalRows.ordinalChecks (row : rows₀) (linked : Contains A M) (n power setup scan : ℕ)
    (hn : 2048 ≤ n) (degree : S.baseDegree ≤ n) (labels : Fintype.card B.Entry ≤ n)
    (width : (Y).maxWireWidth ≤ n) (visits : (chain₀).occurrences (fun _ => 1) ((ord₀).entries i)
      ≤ n)
    (preProbes : countProbes row.pre ≤ 9 + setup + 5 * S.baseDegree + incidentBits (Y)
      ((ord₀).entries i))
    (preTicks : row.pre.length ≤ 44 + n ^ 3 + (15 + 21 * S.baseDegree + 5 * incidentBits (Y)
      ((ord₀).entries i)))
    (jobProbes : ∀ j, row.cost j → countProbes j.trace ≤ scan * (n.log2 + 1) ^ power)
    (jobTicks : row.maxTicks ≤ n ^ 43) (x : (selected₀).Choice i) (rep : Report w)
    (returned : execute M.program cap (M.program.start (i.val : Word w)) m ((selected₀).encode i
      x) = some rep) :
    1 + rep.probes ≤ siteAccesses (Y) (chain₀)
      (VertexReportBudget.coefficient S.baseDegree (Fintype.card B.Entry) setup scan 0 0)
      power n ((ord₀).entries i) ∧ rep.events.length + 107 ≤ n ^ 45 := by
  let v := (ord₀).entries i
  let tree := (trees₀) v
  let nodes := tree.preorder.map (fun a : ℕ => (a : Word w))
  let o := (chain₀).occurrences (fun _ => 1) v
  obtain ⟨control,run,_,hnodes,ctrlTicks,ctrlProbes⟩ :=
    selected_control B κ hκ T hT X z rowBase m (head₀) row.endAddr
      row.rows row.space row.hfit row.capacity v
  obtain ⟨out,call,_,_,_,_,_,jobs,size,valid,probes,ticks⟩ :=
    active_occurrence_costs B κ hκ T hT X z rowBase A M m row.G row.offset base grammar row.src
      order P
      row.valid row.domain row.handlers row.cost linked row.selected v (half v)
      (M.program.start (i.val : Word w)) row.cfg row.pre row.pref row.noChoice row.noWrite
        row.prefixReads
      row.persistent row.atRoot row.top row.stack row.endTop row.sp row.endReg row.one row.zero
        row.prepared
      row.rows row.space row.hfit row.capacity row.above row.hsrc row.hdst row.cells row.hbase
        row.hgrammar
      row.hg row.maxTicks cap row.small row.room x
  have same : out = rep := Option.some.inj (call.symm.trans returned)
  subst out
  have hlabels : g = Fintype.card B.Entry := (Fintype.card_fin g).symm.trans (Fintype.card_congr
    order)
  have length : nodes.length ≤ o := by simpa only [nodes, List.length_map] using hnodes
  have nJobs : jobs.length ≤ o := size.trans_le hnodes
  have incident : incidentBits (Y) v ≤ 2 * S.baseDegree * n :=
    (incidentBits_le (Y) v).trans (Nat.mul_le_mul_left _ width)
  let traffic := (jobs.map (fun j => countProbes j.trace)).sum
  let work := (jobs.map (fun j => j.trace.length)).sum
  have trafficBound : traffic ≤ scan * (o * (n.log2 + 1) ^ power) := calc
    _ ≤ jobs.length * (scan * (n.log2 + 1) ^ power) :=
      sum_jobs_le _ jobs _ (fun j hj => jobProbes j (valid j hj))
    _ ≤ o * (scan * (n.log2 + 1) ^ power) := Nat.mul_le_mul_right _ nJobs
    _ = _ := by ring
  have workBound : work ≤ n ^ 44 := calc
    _ ≤ jobs.length * row.maxTicks :=
      sum_jobs_le _ jobs _ (fun j hj => row.small j (valid j hj))
    _ ≤ n * n ^ 43 := Nat.mul_le_mul (nJobs.trans visits) jobTicks
    _ = _ := (pow_succ' n 43).symm
  change countProbes rep.events + 1 = countProbes row.pre + 3 * jobs.length +
    traffic + 2 * g at probes
  change rep.events.length + 4 = row.pre.length + 15 * jobs.length + work + 7 * g + 14 at ticks
  rw [← size] at ctrlTicks ctrlProbes
  constructor
  · rw [← hlabels]
    refine VertexReportBudget.probes_le (Y) (chain₀) v n power S.baseDegree g setup scan 0 0 m
      (tree.address : Word w) row.endAddr nodes control run length setup traffic 0 0 rep le_rfl
      (by simp) (by simp) ?_ ?_
    · change traffic ≤ 2 * nodes.length + 0 + 0 + scan * (o * (n.log2 + 1) ^ power)
      exact trafficBound.trans (Nat.le_add_left _ _)
    · change countProbes rep.events ≤ _
      change countProbes row.pre ≤ 9 + setup + 5 * S.baseDegree + incidentBits (Y) v at preProbes
      omega
  · refine VertexReportBudget.steps_le_45 (Y) (chain₀) v (geometry := n ^ 3) (hook := work)
      hn degree (hlabels ▸ labels) le_rfl incident visits m (tree.address : Word w) row.endAddr
        nodes control
      run length workBound rep ?_
    change row.pre.length ≤ 44 + n ^ 3 +
      (15 + 21 * S.baseDegree + 5 * incidentBits (Y) v) at preTicks
    omega

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
