import OAI.Computability.VPVNP.PairVertexStageSegment
import OAI.Computability.VPVNP.PairVertexLevelSchedule

/-!
# Native prefix through the level locator and shrink-stage selector

Starting at a popped nonleaf, the full segment first recovers the old level
and packed site. It then transfers to the matching shrink handler with every
locator operand still available in that handler's shared prefix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexStageDispatch

open BurstRAM PrivateRAM VertexImage TraversalControllerInputs TraversalRows TraversalRoles
open scoped Fin.CommRing

variable {N w p r : ℕ}

/-- The located header and owner depend only on the fourteen locator registers. -/
theorem retainLocated {pub : Fin 11 → Word w} {m : Memory w} {locator : Fin 14 ↪ Fin r}
    {node owner : Word w} {stage : ℕ} {a b : Config w p r}
    (h : VertexLevel.Located pub m locator node stage owner a)
    (same : ∀ i, b.reg (locator i) = a.reg (locator i)) :
    VertexLevel.Located pub m locator node stage owner b := by
  obtain ⟨⟨node, head, pitch, index, current, stride, one, offset⟩, start, owner, old, fields,
    ordinal⟩ := h
  constructor
  · constructor <;> rwa [same]
  all_goals rwa [same]

variable (B : Fin N → Segment) (tail : Fin N → ℕ) (split : ∀ i, (B i).privateRegs = 14 + tail i)
variable (loc : Fin (locatedCount B) → Fin p) (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
    (reg : Fin (bankCount tail) ↪ Fin r) (done : Fin p) (M : Machine w p r 11)

private theorem placed_disjoint (j : Fin 14) :
    (locatorBank tail).trans reg j ∉ Set.range ((scratchBank tail).trans reg) := by
  rintro ⟨s,h⟩
  exact locator_disjoint_scratch tail j ⟨s, reg.injective h⟩

/-- The genuine linked trace reaches the indicated handler PC. The two
private register banks account for its entire frame and the producing
level's fields survive at the selected handler's shared register prefix. -/
theorem locatedFamily_run
    (rows : ∀ j, M.code (loc j) =
      ((locatedFamily B tail split).row loc dfs saved reg done j).resize w)
    {m : Memory w} {H first pitch offset cap base : ℕ} {old : TaggedLayer} {ls : List (Fiber w)}
    (d : Resident M.publicData m H first pitch offset cap base old ls)
    (j : Fin (old :: ls.map Prod.fst).length) (stage : ℕ) (hj : j.val = stage + 1)
    (id : Fin (old :: ls.map Prod.fst)[j].layer.count) (i : Fin N)
    (hN : N + 1 < 2 ^ w) (selects : stage % (N + 1) = i.val)
    (c : Config w p r) (hc : c.pc = loc (locatedFamily B tail split).entry)
    (node : (c.reg (dfs 7)).val = TraversalRows.address cap
      (layerBase cap base (old :: ls.map Prod.fst) j) id)
    (fit : layerBase cap base (old :: ls.map Prod.fst) (ls.length + 1) < 2 ^ w) :
    let lr := (locatorBank tail).trans reg
    let sr := (scratchBank tail).trans reg
    ∃ out, NodeArguments.ChildScan.Prefix M m c out []
        (VertexLevel.trace M.publicData m (stage + 1) (ls.length - (stage + 1)) ++
          List.replicate (N + 7 + 2 * i.val) .tick) ∧
      out.pc = bodyPC B (familyPC B loc) i (B i).entry ∧
      VertexLevel.Located M.publicData m lr (c.reg (dfs 7)) stage (id.val : Word w) out ∧
      RouteRange.Frame (fun a ↦ a ∉ Set.range lr ∧ a ∉ Set.range sr) c out := by
  intro lr sr
  obtain ⟨front, selector, _⟩ := locatedFamily_link B dfs saved done M tail split loc reg rows
  obtain ⟨mid, pre, atSel, info, fr⟩ := VertexLevel.run M (locatorPC B loc) dfs saved lr
    (selectorPC B (familyPC B loc) (entry N)) front d j stage hj id c hc node fit
  have hword : ls.length + 1 < 2 ^ w := by
    rw [← (VertexLevelBounds.resident_geometry d).1]
    exact (terminalField M.publicData m 1).isLt
  have hstage : stage < 2 ^ w := by
    have := j.isLt
    simp only [List.length_cons, List.length_map] at this
    omega
  have safe (t : Fin 14) : lr t ∉ Set.range sr := placed_disjoint tail reg t
  obtain ⟨out, dispatch, entryPC, rest⟩ := run_prefix selector (safe 13) hN stage hstage i
    selects mid atSel info.stage m
  refine ⟨out, pre.trans dispatch, entryPC, retainLocated info (fun t ↦ rest.regs _ (safe t)), ?_⟩
  exact ⟨fun a ha ↦ (rest.regs a ha.2).trans (fr.outside a ha.1),
    rest.memory.trans fr.privateMem, rest.persistent.trans fr.persistent⟩

section Schedule

open Compression CompressorRecords LocalHistory

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (Tmpl : S.Templates) (f : Tmpl.Entry → R) (hf : Tmpl.IsSolution f)
variable {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
variable (z : (Tmpl.execute f hf T hT X).Choices)
local notation "levels" => executeLevels Tmpl f hf T hT X z

/-- On a genuine selected shrinking pass, the stage reached by the native
dispatcher is the pass's block index and has its actual input degree exponent. -/
theorem scheduled_run {M : Machine w p r 11} {addr : Fin (count S.steps) → Fin p}
    {scratch : Fin 4 ↪ Fin r} {src : Fin r} {jump : Fin S.steps → Fin p}
    (rows : Linked M addr scratch src jump) (fresh : src ∉ Set.range scratch)
    (hN : S.steps + 1 < 2 ^ w) (j : Fin (levels).length) (fits : j.val < 2 ^ w)
    (shrink : tagLevel Tmpl f hf levels[j] = .shrink)
    (c : Config w p r) (start : c.pc = addr (entry S.steps)) (source : c.reg src = (j.val : Word w))
    (m : Memory w) :
    ∃ i : Fin S.steps, levels[j].origin.ordinal = i.val ∧
      levels[j].inputExponent = S.degreeExponent i.castSucc ∧
      ∃ out, NodeArguments.ChildScan.Prefix M m c out []
        (List.replicate (S.steps + 7 + 2 * i.val) .tick) ∧
        out.pc = jump i ∧ Frame scratch c out := by
  have hr : j.val % (S.steps + 1) ≠ S.steps := by
    intro he
    rw [VertexLevel.selected_pass_role Tmpl f hf T hT X z j, ite_eq_left he] at shrink
    cases shrink
  have hi : j.val % (S.steps + 1) < S.steps := by
    have : j.val % (S.steps + 1) < S.steps + 1 := Nat.mod_lt _ (Nat.succ_pos S.steps)
    omega
  let i : Fin S.steps := ⟨j.val % (S.steps + 1), hi⟩
  refine ⟨i, VertexLevel.selected_pass_ordinal Tmpl f hf T hT X z j, ?_,
    run_prefix rows fresh hN j.val fits i rfl c start source m⟩
  exact (VertexLevel.selected_inputExponent Tmpl f hf T hT X z j).trans (S.exponentAt_castSucc i)

end Schedule

end PairSimulation.VertexStageDispatch

end VPVNP
end Computability
end OAI
