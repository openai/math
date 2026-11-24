import OAI.Computability.VPVNP.CompressorRecordPrivateDescriptor
import OAI.Computability.VPVNP.CompressorRegisterSetupTrace
import OAI.Computability.VPVNP.RAMProcessorReportPrefix
import OAI.Computability.VPVNP.PrimedInputRAMFlowEval

/-!
# Publishing the live arguments of a motif call

The register compiler reads a fixed family of expressions from external records.
The last expression computes the private descriptor base. The writer sets the
map's descriptor pointer, stores the preceding results in consecutive words and
jumps to the map call. Its instruction and probe counts depend only on the
expressions, including when their values depend on the chosen term.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapArgumentWriter

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.PhaseRecipe
open PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {n w p r k : ℕ} (base : Expr) (fields : Fin n → Expr)

/-- The map's descriptor base is computed in the same pass as the argument values. -/
def recipes : Fin (n + 1) → Expr := Fin.snoc fields base

/-- Assignment list for all fields followed by the descriptor base. -/
abbrev lines := RegisterSetup.lines (recipes base fields)
/-- Code slots for the assignment list, pointer setup, and individual stores. -/
abbrev Address := Fin (lines base fields).length ⊕ Fin 3 ⊕ Fin n × Bool

variable (vm : Fin (RegisterSetup.regCount (recipes base fields)) ↪ Fin r)
  (inputs : Fin 6 → Fin r) (aux : Fin 3 ↪ Fin r)
  (loc : Address base fields → Fin p) (done : Fin p)

/-- Enter the indexed assignment or the pointer setup after the final one. -/
def setupPC (i : ℕ) : Fin p :=
  if h : i < (lines base fields).length then loc (.inl ⟨i, h⟩) else loc (.inr (.inl 0))

private def storePC (i : Fin (n + 1)) : Fin p :=
  if h : i.val < n then loc (.inr (.inr (⟨i.val, h⟩, false))) else done

private def output (i : Fin (n + 1)) := vm (RegisterSetup.output (recipes base fields) i)

/-- Relocatable instructions for expression evaluation, pointer installation
and publication of the argument words. The last store jumps through its
increment instruction to the caller's map-entry continuation. -/
def text : Address base fields → Instr 2 p r k
  | .inl i => RegisterSetup.instruction vm inputs (lines base fields)[i.val]
      (setupPC base fields loc (i.val + 1))
  | .inr (.inl i) =>
    ![.copy (aux 0) (output base fields vm (Fin.last n)) (loc (.inr (.inl 1))),
      .copy (aux 1) (aux 0) (loc (.inr (.inl 2))),
      .constant (aux 2) 1 (storePC base fields loc done 0)] i
  | .inr (.inr (i, false)) =>
    .storePrivate (aux 1) (output base fields vm i.castSucc) (loc (.inr (.inr (i, true))))
  | .inr (.inr (i, true)) =>
    .binary .add (aux 1) (aux 1) (aux 2) (storePC base fields loc done i.succ)

/-- Exact instruction count, including the private pointer copy and all stores. -/
def clock := (lines base fields).length + (3 + 2 * n)

private theorem tick_log (t : ℕ) : choiceBits (List.replicate t (.tick : Event w)) = [] ∧
    countProbes (List.replicate t (.tick : Event w)) = 0 := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih => simpa only [List.replicate_succ, choiceBits, countProbes] using ih

/-- External reads use the live six input registers and private stores preserve
every address outside the descriptor. The returned trace composes with every
fuel and branch-bit continuation on the same external memory. -/
theorem native_raw (M : Machine w p r k) (link : ∀ a,
    M.code (loc a) = (text base fields vm inputs aux loc done a).resize w)
    (safe : ∀ i j, vm i ≠ inputs j) (apart : ∀ i j, vm i ≠ aux j)
    (c : Config w p r) (m : Memory w) (start : c.pc = setupPC base fields loc 0) :
    let pub := fun i : Fin 5 ↦ c.reg (inputs i.castSucc)
    let state := c.reg (inputs (Fin.last 5))
    let addr := base.eval pub state m
    addr.val + n ≤ 2 ^ w →
    let ev := (RowRecipe.evaluate pub state m (lines base fields) (fun i ↦ c.reg (vm i))).1 ++
      List.replicate (3 + 2 * n) (.tick : Event w)
    ∃ out : Config w p r,
      ev.length = clock base fields ∧ countProbes ev = ∑ i, ((recipes base fields) i).loads ∧
      choiceBits ev = [] ∧ out.pc = done ∧ out.reg (aux 0) = addr ∧
      out.persistent = c.persistent ∧
      (∀ i : Fin n, out.privateMem (addr + (i.val : Word w)) = (fields i).eval pub state m) ∧
      (∀ a : Word w, a.val < addr.val ∨ addr.val + n ≤ a.val →
        out.privateMem a = c.privateMem a) ∧
      (∀ j, (∀ i, j ≠ vm i) → (∀ i, j ≠ aux i) → out.reg j = c.reg j) ∧
      ∀ fuel bs, execute M.program (fuel + ev.length) c m bs =
        (execute M.program fuel out m bs).map (fun rep ↦ ⟨ev ++ rep.events, rep.result⟩) := by
  intro pub state addr fit
  let f := recipes base fields
  have setup : RegisterSetup.Linked vm inputs M (setupPC base fields loc)
      (RegisterSetup.lines f) := by
    intro i
    have hi : i.val < (lines base fields).length := i.isLt
    rw [show setupPC base fields loc i.val = loc (.inl i) by simp [setupPC, hi], link]
    exact RegisterSetup.resize_instruction ..
  let ev := (RowRecipe.evaluate pub state m (RegisterSetup.lines f) (fun i ↦ c.reg (vm i))).1
  obtain ⟨d, len, probes, choices, atCopy, mem, pers, vals, frame, run⟩ :=
    RegisterSetup.execute_setup_raw f inputs vm M m _ setup safe c start
  have here : d.pc = loc (.inr (.inl 0)) := by
    simpa only [setupPC, f, lines, lt_self_iff_false, ↓reduceDIte] using atCopy
  let d' := d.put (loc (.inr (.inl 1))) (aux 0) addr
  have ptr : d.reg (output base fields vm (Fin.last n)) = addr := by
    simpa only [output, f, recipes, Fin.snoc_last, addr, pub, state] using vals (Fin.last n)
  have step : M.program.step d = .localStep d' := by
    change (M.code d.pc).run M.publicData d = _
    rw [here, link]
    change CallAction.localStep (d.put _ _ (d.reg (output base fields vm (Fin.last n)))) = _
    rw [ptr]
  let header : Fin 2 → Fin p := ![loc (.inr (.inl 1)), loc (.inr (.inl 2))]
  let next := fun i : Fin n ↦ loc (.inr (.inr (i, true)))
  let values := fun i : Fin n ↦ output base fields vm i.castSucc
  have store : PrivateDescriptor.Linked M values (aux 0) (aux 1) (aux 2) header
      (storePC base fields loc done) next := by
    refine ⟨link (.inr (.inl 1)), link (.inr (.inl 2)), ?_, ?_⟩
    · intro i
      rw [show storePC base fields loc done i.castSucc = loc (.inr (.inr (i, false))) by
        simp [storePC, i.isLt], link]
      rfl
    · intro i
      exact link (.inr (.inr (i, true)))
  have addr' : d'.reg (aux 0) = addr := Config.put_same ..
  obtain ⟨out, tail, atDone, pers', ptr', written, outside, keep⟩ :=
    PrivateDescriptor.publish M values (aux 0) (aux 1) (aux 2) header
      (storePC base fields loc done) next store (aux.injective.ne (by decide))
      (aux.injective.ne (by decide)) (aux.injective.ne (by decide))
      (fun _ ↦ ⟨apart _ _, apart _ _⟩) d' rfl (addr' ▸ fit)
  let ticks := List.replicate (3 + 2 * n) (.tick : Event w)
  have suffix : Prefix M d ticks out := by
    dsimp only [ticks]
    rw [show 3 + 2 * n = (2 + 2 * n) + 1 by omega, List.replicate_succ]
    exact .tick step tail
  have prop := tick_log (w := w) (3 + 2 * n)
  have endPtr := ptr'.trans addr'
  refine ⟨out, ?_, ?_, ?_, ?_, endPtr, pers'.trans pers, ?_, ?_, ?_, ?_⟩
  · change (ev ++ ticks).length = _
    rw [List.length_append, show ev.length = (RegisterSetup.lines f).length from len]
    simp only [ticks, List.length_replicate, clock, lines, f]
  · rw [countProbes_append, probes, prop.2, Nat.add_zero]
  · rw [PrimedInputRAM.Flow.choiceBits_append, choices, prop.1, List.nil_append]
  · simpa [storePC] using atDone
  · intro i
    rw [← endPtr, written]
    have h : values i ≠ aux 0 := apart _ _
    change Function.update d.reg (aux 0) addr (values i) = _
    rw [Function.update_of_ne h]
    simpa only [values, output, f, recipes, Fin.snoc_castSucc, pub, state] using vals i.castSucc
  · intro a ha
    exact (outside _ (addr' ▸ ha)).trans (congrFun mem a)
  · intro j hbank haux
    exact (keep j (haux 1) (haux 2)).trans
      ((Function.update_of_ne (haux 0) ..).trans (frame j hbank))
  · intro fuel bs
    change execute M.program (fuel + (ev ++ ticks).length) c m bs =
      (execute M.program fuel out m bs).map (fun rep ↦ ⟨(ev ++ ticks) ++ rep.events, rep.result⟩)
    change ∀ f bs, execute M.program (f + ev.length) c m bs =
      (execute M.program f d m bs).map (fun rep ↦ ⟨ev ++ rep.events, rep.result⟩) at run
    have hs := suffix.execute fuel m bs
    rw [prop.1, List.nil_append] at hs
    rw [List.length_append, show fuel + (ev.length + ticks.length) =
      (fuel + ticks.length) + ev.length by omega, run, hs]
    simp [Option.map_map, Function.comp_def, List.append_assoc]

/-- External reads use the live six input registers and private stores preserve
every address outside the descriptor. The returned trace composes with every
fuel and branch-bit continuation on the same external memory. -/
theorem native (M : Machine w p r k) (link : ∀ a,
    M.code (loc a) = (text base fields vm inputs aux loc done a).resize w)
    (safe : ∀ i j, vm i ≠ inputs j) (apart : ∀ i j, vm i ≠ aux j)
    (c : Config w p r) (m : Memory w) (start : c.pc = setupPC base fields loc 0) :
    let pub := fun i : Fin 5 ↦ c.reg (inputs i.castSucc)
    let state := c.reg (inputs (Fin.last 5))
    let addr := base.eval pub state m
    addr.val + n ≤ 2 ^ w →
    ∃ (ev : List (Event w)) (out : Config w p r),
      ev.length = clock base fields ∧ countProbes ev = ∑ i, ((recipes base fields) i).loads ∧
      choiceBits ev = [] ∧ out.pc = done ∧ out.reg (aux 0) = addr ∧
      out.persistent = c.persistent ∧
      (∀ i : Fin n, out.privateMem (addr + (i.val : Word w)) = (fields i).eval pub state m) ∧
      (∀ a : Word w, a.val < addr.val ∨ addr.val + n ≤ a.val →
        out.privateMem a = c.privateMem a) ∧
      (∀ j, (∀ i, j ≠ vm i) → (∀ i, j ≠ aux i) → out.reg j = c.reg j) ∧
      ∀ fuel bs, execute M.program (fuel + ev.length) c m bs =
        (execute M.program fuel out m bs).map (fun rep ↦ ⟨ev ++ rep.events, rep.result⟩) := by
  intro pub state addr fit
  obtain ⟨out, prop⟩ :=
    native_raw base fields vm inputs aux loc done M link safe apart c m start fit
  exact ⟨_, out, prop⟩

end PairSimulation.MapArgumentWriter

end VPVNP
end Computability
end OAI
