import OAI.Computability.VPVNP.PairShrinkNodeStageCost
import OAI.Computability.VPVNP.PairShrinkRoleSetup
import OAI.Computability.VPVNP.PairShrinkRoleHeaderSetup
import OAI.Computability.VPVNP.PairShrinkRoleHandoff
import OAI.Computability.VPVNP.PairSimulationMapResidentInputs

/-! # Counts for a complete shrinking visit

All terms outside the selected map list are explicit native instruction
or probe counts. A resident map list contributes its test and increment
per item, its final exit test, and the traces of its actually executed items.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkNodeCost

open BurstRAM PrivateRAM DFS Compression CompressorRecords NodeArguments NodeArguments.ChildScan
open ShrinkRole ShrinkHiddenGuess
open scoped Fin.CommRing

variable {w endAddr a g : ℕ} {X : State a g}

private theorem noProbes (n : ℕ) : countProbes (List.replicate n (.tick : Event w)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, countProbes] using ih

/-- Counts for a map list that actually succeeded, parameterized by the
concrete resource bounds for each selected row. -/
theorem scan_cost {ι : Type*} (jobs : List ι) (action : ι → ResidentMapLoop.Exact.Action w endAddr)
    (ticks reads : ι → ℕ) (node : Word w) (saved out : Scratch w endAddr) (es : List (Event w))
    (row : ∀ i ∈ jobs, ∀ s e t, action i node s = some (e, t) →
      e.length ≤ ticks i ∧ countProbes e ≤ reads i)
    (got : ResidentMapLoop.Exact.scan node (jobs.map action) saved = some (es, out)) :
    es.length ≤ 1 + 2 * jobs.length + (jobs.map ticks).sum ∧
      countProbes es ≤ (jobs.map reads).sum := by
  induction jobs generalizing saved es out with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj got)
    exact ⟨le_rfl, le_rfl⟩
  | cons j js ih =>
    cases hx : action j node saved with
    | none => simp [ResidentMapLoop.Exact.scan, hx] at got
    | some pair =>
      obtain ⟨h, mid⟩ := pair
      cases hy : ResidentMapLoop.Exact.scan node (js.map action) mid with
      | none => simp [ResidentMapLoop.Exact.scan, hx, hy] at got
      | some pair =>
        obtain ⟨t, last⟩ := pair
        simp only [List.map_cons, ResidentMapLoop.Exact.scan, hx, hy, Option.some.injEq,
          Prod.mk.injEq] at got
        obtain ⟨rfl, rfl⟩ := got
        have first := row j List.mem_cons_self _ _ _ hx
        have rest := ih mid last t (fun i hi => row i (List.mem_cons_of_mem _ hi)) hy
        simp only [List.length_append, List.length_cons, List.length_nil, List.map_cons,
          List.sum_cons, countProbes_append, countProbes]
        omega

variable (A : Arena) (T : IncidenceDirectory w) (m : Memory w) (older cap : ℕ)
    (desc : Word w → ChildArguments.Descriptor w X)
    (args : List (Child X) → Args w) (seed : List (Child X) → List Row)
    (maps : List (Child X) → List Row → List (ResidentMapLoop.Exact.Action w endAddr))
    (pub : Fin 11 → Word w) (level later stages stage selectors stride oldHead : ℕ) (owner : Word w)
    (s₁ : Setup w endAddr) (s₂ : List (Child X) → Setup w endAddr)
    (s₃ : List (Child X) → List Row → Setup w endAddr)
    (node : Word w) (saved : Scratch w endAddr) (bs tail : List Bool) (out : Outcome w endAddr Unit)
    (childSetup : s₁.trace node saved = VertexLevel.trace pub m level later ++
      List.replicate (stages + 7 + 2 * stage) .tick ++ List.replicate 2 .tick ++
        List.replicate (2 ^ a) .tick)
    (hiddenSetup : ∀ xs s, (s₂ xs).trace node s =
      List.replicate (VertexLevel.hiddenCount + 1) .tick ++
      Header.canonicalTrace selectors stride (oldHead : Word w) m)
    (mapSetup : ∀ xs h s, (s₃ xs h).trace node s = List.replicate 4 .tick ++
      MapResidentInputs.headerEvents m (oldHead : Word w) owner)
    (got : visitReader A T m older cap desc args seed maps s₁ s₂ s₃ node saved bs =
      some (out, tail))

include childSetup hiddenSetup mapSetup got

/-- Instruction and probe counts for the child and hidden reads reached by the visit
and the resident map scan starting on their prepared scratch. -/
theorem native_cost_reached :
    ∃ child mid hidden mapOut ms,
      ChildArguments.reader A T m older cap desc node (s₁.updated node saved) bs =
        some (child, mid) ∧
      hiddenReader (args child.value) m (seed child.value) node
        ((s₂ child.value).updated node child.updated) mid = some (hidden, tail) ∧
      ResidentMapLoop.Exact.scan node (maps child.value hidden.value)
        ((s₃ child.value hidden.value).updated node hidden.updated) = some (ms, mapOut) ∧
      child.value.map Child.site = (desc node).sites ∧
      hidden.value.length = (seed child.value).length ∧
      (stream hidden.value).length = (stream (seed child.value)).length ∧
      out.trace.length = 88 + 6 * later + stages + 2 * stage + 2 ^ a + VertexLevel.hiddenCount +
        (RegisterSetup.lines (Header.recipe selectors stride)).length +
        (10 + 15 * 2 ^ a) * (desc node).sites.length +
        6 * ChildArguments.demand X (desc node).sites +
        25 * (seed child.value).length + 6 * (stream (seed child.value)).length + ms.length ∧
      countProbes out.trace = 25 + later + (1 + 3 * 2 ^ a) * (desc node).sites.length +
        3 * (seed child.value).length + countProbes ms := by
  obtain ⟨child, mid, hidden, mapOut, ms, hchild, hhidden, hscan, sites, hnum, hbits, trace⟩ :=
    visit_trace_reached A T m older cap desc args seed maps s₁ s₂ s₃ node saved bs tail out got
  refine ⟨child, mid, hidden, mapOut, ms, hchild, hhidden, hscan, sites, hnum, hbits, ?_⟩
  rw [trace, childSetup, hiddenSetup, mapSetup]
  obtain ⟨locT, locP, _⟩ := VertexLevel.trace_cost pub m level later
  obtain ⟨chP, chT, _⟩ := ChildHeader.cost m node (desc node).directoryBase
  obtain ⟨_, oldP, oldT⟩ := ChildScan.events_cost X T m (desc node).source child.value
  obtain ⟨hdrT, hdrP⟩ := hidden_header_cost selectors stride (oldHead : Word w) m
  obtain ⟨hidT, hidP, _⟩ := ShrinkHiddenGuess.cost (args child.value) m hidden.value
  obtain ⟨mapT, mapP, _⟩ := MapResidentInputs.headerCost m (oldHead : Word w) owner
  have nxs : child.value.length = (desc node).sites.length := by
    simpa only [List.length_map] using congrArg List.length sites
  have demand := (ChildArguments.payload_length X child.value).trans
    (congrArg (ChildArguments.demand X) sites)
  simp only [List.length_append, List.length_replicate, countProbes_append, noProbes,
    locT, locP, chT, chP, oldT, oldP, hdrT, hdrP, hidT, hidP, mapT, mapP, nxs, demand, hnum, hbits]
  constructor <;> omega

/-- Combined length of the level search, stage selection, child handoff,
child directory, hidden handoff, hidden header and loop, and map reload
and header. The list of per-item map events includes its own loop control. -/
theorem native_cost :
    ∃ xs hs mapIn mapOut ms, xs.map Child.site = (desc node).sites ∧ hs.length = (seed xs).length ∧
      (stream hs).length = (stream (seed xs)).length ∧
      ResidentMapLoop.Exact.scan node (maps xs hs) mapIn = some (ms, mapOut) ∧
      out.trace.length = 88 + 6 * later + stages + 2 * stage + 2 ^ a + VertexLevel.hiddenCount +
        (RegisterSetup.lines (Header.recipe selectors stride)).length +
        (10 + 15 * 2 ^ a) * (desc node).sites.length +
        6 * ChildArguments.demand X (desc node).sites +
        25 * (seed xs).length + 6 * (stream (seed xs)).length + ms.length ∧
      countProbes out.trace = 25 + later + (1 + 3 * 2 ^ a) * (desc node).sites.length +
        3 * (seed xs).length + countProbes ms := by
  obtain ⟨child, mid, hidden, mapOut, ms, _, _, hscan, sites, hnum, hbits, ticks, probes⟩ :=
    native_cost_reached A T m older cap desc args seed maps pub level later stages stage selectors
      stride oldHead owner s₁ s₂ s₃ node saved bs tail out childSetup hiddenSetup mapSetup got
  exact ⟨child.value, hidden.value, _, mapOut, ms, sites, hnum, hbits, hscan, ticks, probes⟩

end PairSimulation.ShrinkNodeCost

end VPVNP
end Computability
end OAI
