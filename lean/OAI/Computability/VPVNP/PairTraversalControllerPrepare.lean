import OAI.Computability.VPVNP.PairTraversalControllerCode

/-!
# The complete read-only traversal dispatcher prefix

From the native reset state, the controller reaches a unique destination using
only ticks and reads. Every computed operand is evaluated on the entry memory.
The worker scratch registers are zero at that point. The log may be replayed
against any memory, and its exact probe count is independent of the ordinal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController.Native

open BurstRAM BurstRAM.PrivateRAM CompressorRecords PrimedStackRAM PrimedInputRAM
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.execute from OAI.Computability.VPVNP.PairSimulationPrivateSlices
open private execute_lines lines_probes no_choices emit_list
  from OAI.Computability.VPVNP.CompressorRecordRegisterSetup
open private eval_cost from OAI.Computability.VPVNP.CompressorRecordsRowRecipe

variable {w : ℕ}

private theorem readOnly {M : Machine w P R 11} {m : Memory w} {c d : Config w P R}
    {es : List (Event w)} (he : ReadPrefix M m c es d) (n : Memory w) :
    (∀ a v, Event.write a v ∉ es) ∧ after n es = n := by
  induction he with
  | nil => exact ⟨by simp, rfl⟩
  | tick _ _ ih | read _ _ _ ih =>
    exact ⟨fun a v => by simp [ih.1 a v], ih.2⟩

private theorem scratch_apart (i : Fin 7) (j : Fin (RegisterSetup.regCount formulas)) :
    scratchRegs i ≠ vm j := by
  intro eqn
  have := congrArg Fin.val eqn
  change RegisterSetup.regCount formulas + i.val = j.val at this
  omega

private theorem scratch_zero (pub : Fin 11 → Word w) (s : Word w) (i : Fin 7) :
    (loaded pub s).reg (scratchRegs i) = 0 := by
  have outside (t : Fin 10) (ht : 7 ≤ t.val) : scratchRegs i ≠ extra t := by
    intro e
    have := congrArg Fin.val e
    change RegisterSetup.regCount formulas + i.val = RegisterSetup.regCount formulas + t.val at this
    omega
  simp only [loaded, Function.update_of_ne (outside 9 (by decide)),
    Function.update_of_ne (outside 8 (by decide)), Function.update_of_ne (outside 7 (by decide))]

private theorem tick_cost (n : ℕ) : countProbes (List.replicate n (.tick : Event w)) = 0 ∧
    choiceBits (List.replicate n (.tick : Event w)) = [] ∧
    ∀ m : Memory w, after m (List.replicate n .tick) = m := by
  induction n with
  | zero => exact ⟨rfl, rfl, fun _ => rfl⟩
  | succ n ih => simpa only [List.replicate_succ, countProbes, choiceBits, after, List.foldl_cons,
      BurstRAM.update] using ih

/-- Chronological log of the register setup and guard instructions. -/
def prefixTrace (pub : Fin 11 → Word w) (state : Word w) (m : Memory w) (rs : Regs w R) :
    List (Event w) :=
  [.tick, .tick, .tick] ++ (RowRecipe.evaluate (recipePub pub) state m
    (RegisterSetup.lines formulas) ((loaded pub state).reg ∘ vm)).1 ++
    List.replicate (route rs).ticks .tick

set_option maxRecDepth 8192 in
/-- Exact native setup and guard traversal, with all operand values, the
read-only prefix and the continuation at the selected machine label. -/
theorem prepare_trace (pub : Fin 11 → Word w) (state : Word w) (m : Memory w) :
    ∃ (es : List (Event w)) (rs : Regs w R),
      (∀ i, rs (value i) = (formulas i).eval (recipePub pub) state m) ∧
      (∀ i, rs (scratchRegs i) = 0) ∧
      es.length = 3 + (RegisterSetup.lines formulas).length + (route rs).ticks ∧
      countProbes es = ∑ i, (formulas i).loads ∧ choiceBits es = [] ∧
      (∀ a v, Event.write a v ∉ es) ∧ (∀ n : Memory w, after n es = n) ∧
      (∀ fuel bits, execute (machine pub).program (fuel + es.length)
          ((machine pub).program.start state) m bits =
        (execute (machine pub).program fuel ⟨(route rs).pc, state, rs, fun _ => 0⟩ m bits).map
          (Flow.prependEvents es)) ∧ es = prefixTrace pub state m rs := by
  let c := loaded pub state
  let start := c.reg ∘ vm
  let eval := RowRecipe.evaluate (recipePub pub) state m (RegisterSetup.lines formulas) start
  obtain ⟨d, run, endPC, mem, pers, vals, frame⟩ := execute_lines vm inputs (machine pub) m
    (RegisterSetup.lines formulas) (fun i j => (inputs_apart j i).symm) (recipePub pub) state
    start setupPC (linked_setup pub) c rfl (loaded_inputs pub state) (loaded_state pub state)
    (fun _ => rfl)
  let guards := List.replicate (route d.reg).ticks (.tick : Event w)
  let pre : List (Event w) := [.tick, .tick, .tick]
  let es := pre ++ eval.1 ++ guards
  have length : eval.1.length = (RegisterSetup.lines formulas).length :=
    (eval_cost (recipePub pub) state m (RegisterSetup.lines formulas) start).1
  have probes : countProbes eval.1 = ∑ i, (formulas i).loads := lines_probes formulas ..
  have bits : choiceBits eval.1 = [] := no_choices ..
  have readonly (n : Memory w) := readOnly run n
  have hguards := tick_cost (w := w) (route d.reg).ticks
  refine ⟨es, d.reg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro i
    have output := emit_list formulas (recipePub pub) state m (List.finRange 18) start i
    exact (vals _).trans (output.trans (ite_eq_left (List.mem_finRange i)))
  · intro i
    exact (frame _ (scratch_apart i)).trans (scratch_zero pub state i)
  · simp [es, pre, guards, length]
    omega
  · simp only [es, countProbes_append, show countProbes pre = 0 from rfl, probes, guards,
      hguards.1, Nat.zero_add, Nat.add_zero]
  · simp only [es, Flow.choiceBits_append, show choiceBits pre = [] from rfl, bits, guards,
      hguards.2.1, List.nil_append]
  · intro a v
    have noGuard : Event.write a v ∉ guards := by
      intro h
      have eqn : Event.write a v = .tick := List.eq_of_mem_replicate h
      cases eqn
    simpa [es, pre, noGuard] using (show Event.write a v ∉ eval.1 from (readonly m).1 a v)
  · intro n
    have ha : after n eval.1 = n := (readonly n).2
    simp only [es, after, List.foldl_append, show pre.foldl BurstRAM.update n = n from rfl]
    change after (after n eval.1) guards = n
    rw [ha]
    exact hguards.2.2 n
  · intro fuel bs
    have he := ReadPrefix.execute run (fuel + (route d.reg).ticks) bs
    have hd : d = ⟨guardPC 0, state, d.reg, fun _ => 0⟩ := by
      have pc := endPC.trans setup_end
      cases d
      simp_all only [c, loaded]
    change execute (machine pub).program (fuel + es.length)
        ((machine pub).program.start state) m bs = _
    rw [show fuel + es.length = fuel + (route d.reg).ticks + eval.1.length + 3 by
      simp [es, pre, guards]; omega, enter, he]
    have hg := dispatch pub state d.reg (fun _ => 0) m bs fuel
    rw [← hd] at hg
    rw [hg, Option.map_map, Option.map_map]
    congr 1
    funext rep
    simp [Function.comp_def, Flow.prependEvents, es, pre, guards, eval, List.append_assoc]

/-- Prepare the worker at its selected label with its complete read-only prefix. -/
theorem prepare (pub : Fin 11 → Word w) (state : Word w) (m : Memory w) :
    ∃ (es : List (Event w)) (rs : Regs w R),
      (∀ i, rs (value i) = (formulas i).eval (recipePub pub) state m) ∧
      (∀ i, rs (scratchRegs i) = 0) ∧
      es.length = 3 + (RegisterSetup.lines formulas).length + (route rs).ticks ∧
      countProbes es = ∑ i, (formulas i).loads ∧ choiceBits es = [] ∧
      (∀ a v, Event.write a v ∉ es) ∧ (∀ n : Memory w, after n es = n) ∧
      ∀ fuel bits, execute (machine pub).program (fuel + es.length)
          ((machine pub).program.start state) m bits =
        (execute (machine pub).program fuel ⟨(route rs).pc, state, rs, fun _ => 0⟩ m bits).map
          (Flow.prependEvents es) := by
  obtain ⟨es, rs, fields, zero, length, probes, bits, writes, memory, run, _⟩ :=
    prepare_trace pub state m
  exact ⟨es, rs, fields, zero, length, probes, bits, writes, memory, run⟩

end PairSimulation.TraversalController.Native

end VPVNP
end Computability
end OAI
