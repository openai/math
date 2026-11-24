import OAI.Computability.VPVNP.PairTraversalSiteWorker
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# External read addresses of a placement-fiber worker

The setup probes the count cell once. Every iteration reads its current
source identifier, then advances the source cursor by one. The translated
addresses and the two new header cells are written without being read.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows.SiteWorker

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM PrimedCounter CompressorRecords
open scoped Fin.CommRing

variable {w : ℕ}

private theorem unique_lines {r k : ℕ} {ops : List (Op r k)} {nonempty : ops ≠ []}
    {pub : Fin k → Word w} {state : Word w} {rs m es out m' fs out' m''}
    (first : Flow.Exec pub state (lines ops nonempty) rs m es out m')
    (second : Flow.Exec pub state (lines ops nonempty) rs m fs out' m'') :
    es = fs ∧ out = out' ∧ m' = m'' := by
  have e := (Admin.exec_lines_iff_trace nonempty).mp first
  have f := (Admin.exec_lines_iff_trace nonempty).mp second
  simpa only [Option.some.injEq, Prod.mk.injEq] using e.symm.trans f

open private advance events body_exec from OAI.Computability.VPVNP.PairSimulationDescriptorRows

private def loopOps : List (Op 7 0) :=
  [.read 6 0, .binary .mul 6 6 4, .binary .add 6 6 3, .write 2 6, .binary .add 0 0 5,
   .binary .add 2 2 5]

/-- In every successful loop derivation the sole read of an iteration is
at its current source address. -/
private theorem scan_reads (pub : Fin 0 → Word w) (state : Word w) (src count : ℕ)
    {rs m es out m'} (run : Flow.Exec pub state DescriptorRows.scan rs m es out m')
    (start : (rs 0).val = src) (stop : (rs 1).val = src + count) (unit : rs 5 = 1) :
    SourceTransport.Reads (fun x => src ≤ x ∧ x < src + count) es := by
  induction count generalizing src rs m es with
  | zero =>
    cases run with
    | whileDone => intro a v hv; simp at hv
    | whileStep lt _ _ =>
      have h : (rs 0).val < (rs 1).val := lt
      omega
  | succ n ih =>
    cases run with
    | whileDone => intro a v hv; simp at hv
    | @whileStep _ _ _ _ _ head mid mem' tail _ _ _ body later =>
      have hb : Flow.Exec pub state (lines loopOps (by decide)) rs m head mid mem' := body
      obtain ⟨traceEq, regsEq, _⟩ := unique_lines hb (body_exec pub state rs m)
      have bound : src + (n + 1) < 2 ^ w := stop ▸ (rs 1).isLt
      have start' : (mid 0).val = src + 1 := by
        rw [regsEq]
        simp (config := { decide := true }) [advance, Function.update, Fin.val_add, start, unit,
          Nat.mod_eq_of_lt (by omega : src + 1 < 2 ^ w)]
      have stop' : (mid 1).val = src + 1 + n := by
        rw [regsEq]
        simp (config := { decide := true }) [advance, Function.update, stop]
        omega
      have unit' : mid 5 = 1 := by
        rw [regsEq]
        simp (config := { decide := true }) [advance, Function.update, unit]
      have ht := ih (src + 1) later start' stop' unit'
      intro a v hv
      simp only [List.mem_cons, reduceCtorEq, false_or, List.mem_append] at hv
      rcases hv with h | h
      · rw [traceEq] at h
        simp only [events, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_false,
          Event.read.injEq] at h
        rw [h.1, start]
        omega
      · have bounds := ht a v h
        omega

open private setupOps setup_exec finish_exec from OAI.Computability.VPVNP.PairTraversalSiteWorker

private theorem setup_reads {pub : Fin 6 → Word w} {i : Word w} {rs m es out m'}
    (run : Flow.Exec pub i (lines setupOps (by decide)) rs m es out m') :
    SourceTransport.Reads (fun x => x = (counter pub i).val) es := by
  have h := (Admin.exec_lines_iff_trace (by decide)).mp run
  simp (config := { decide := true }) only [setupOps, Fin.isValue, trace, Op.effect, BinaryOp.eval,
    Nat.reducePow, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Fin.ofNat_eq_cast, Nat.cast_ofNat,
    Nat.one_mod, Nat.cast_one, Prod.mk.eta, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    Function.update, ↓reduceDIte, Function.update_idem, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.1]
  intro a v ha
  simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, Event.read.injEq, false_or,
    or_false] at ha
  exact congrArg Fin.val ha.1

/-- A successful native worker reads only its own count cell and its occupied
source row. The result applies to the report returned by the machine. -/
theorem native_reads (pub : Fin 6 → Word w) (i : Word w) (m : Memory w)
    (src nodeAddr count fuel : ℕ) (hs : source pub i = (src : Word w))
    (_hn : node pub i = (nodeAddr : Word w)) (hc : (m (counter pub i).val).val = count)
    (before : src + count ≤ nodeAddr) (fit : nodeAddr + 2 + count < 2 ^ w)
    (_clock : 7 * count + 24 < fuel) {rep : Report w}
    (exec : let M := (program.template (some 6)).instantiate w pub
      execute M.program fuel (M.program.start i) m [] = some rep) :
    SourceTransport.Reads (fun x => x = (counter pub i).val ∨ src ≤ x ∧ x < src + count)
      rep.events := by
  obtain ⟨out, m', run, _, _, _⟩ := (Flow.template_execute_iff program (some 6) pub i
    (fun _ => 0) (fun _ => 0) m fuel [] rep).mp exec
  generalize h : rep.events = es at run ⊢
  cases run with
  | @seq _ _ _ _ ss rs mid ts _ _ setup tail =>
    obtain ⟨ss', rs', first, h0, h1, _, _, _, h5, _, _, _⟩ := setup_exec pub i m (fun _ => 0)
    obtain ⟨_, regsEq, _⟩ := unique_lines setup first
    have heads := setup_reads setup
    cases tail with
    | @seq _ _ _ _ loopEs last mem' endEs _ _ renamed finish =>
      obtain ⟨loop, _⟩ := restrictExec (Function.Embedding.refl (Fin 7)) Fin.elim0 pub
        DescriptorRows.scan renamed
      have start : (rs 0).val = src := by
        rw [regsEq, h0, hs]
        exact Nat.mod_eq_of_lt (by omega)
      have stop : (rs 1).val = src + count := by
        rw [regsEq, h1, Fin.val_add, show (source pub i).val = src from h0 ▸ regsEq ▸ start, hc]
        exact Nat.mod_eq_of_lt (by omega)
      have ids := scan_reads (pub ∘ Fin.elim0) i src count loop start stop (regsEq ▸ h5)
      obtain ⟨last', ending, _⟩ := finish_exec pub i mem' last
      have hEnd := (unique_lines finish ending).1
      intro a v hv
      rcases List.mem_append.mp hv with h | h
      · exact Or.inl (heads a v h)
      rcases List.mem_append.mp h with h | h
      · exact Or.inr (ids a v h)
      · rw [hEnd] at h
        simp at h

end PairSimulation.TraversalRows.SiteWorker

end VPVNP
end Computability
end OAI
