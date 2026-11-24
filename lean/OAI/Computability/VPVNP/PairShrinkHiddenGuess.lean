import OAI.Computability.VPVNP.PairShrinkHiddenStep
import OAI.Computability.VPVNP.PairShrinkHiddenControl

/-!
# Executing the complete absorbed-field row

The native count probe controls a forward scan of the selected owner's ID
directory. Each iteration reads its actual term cells and consumes one
independent field in the restricted order. The private storage is indexed
by dense ID, so both motif incidences refer to the same guessed bit word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkHiddenGuess

open BurstRAM PrivateRAM NodeArguments.ChildScan
open scoped Fin.CommRing

variable {W p r k : ℕ} {M : Machine W p r k} {pc : Stage → Fin p} {reg : Fin 22 ↪ Fin r} {done : Fin p}

/-- Trace of the forward scan from the current ID pointer. Each field contributes a guard test,
its field trace, and two steps to decrement and advance. The final event tests the empty
remainder. -/
def loopEvents (g : Args W) (m : Memory W) : ℕ → List Row → List (Event W)
  | _, [] => [.tick]
  | ptr, e :: es => (.tick :: fieldEvents g m ptr e ++ [.tick,.tick]) ++ loopEvents g m (ptr+1) es

/-- Trace from initialization through the final loop test, scanning the supplied fields in
order from the owner's row start. -/
def events (g : Args W) (m : Memory W) (es : List Row) :=
  setupEvents m g ++ loopEvents g m g.row es

/-- The choice stream for an ordered row of hidden fields, formed by concatenating their bit
lists in scan order. -/
def stream (rows : List Row) := rows.flatMap Prod.snd

private theorem suffixValid (g : Args W) (m : Memory W) (ptr : ℕ) (e : Row) (es : List Row)
    (h : ∀ i : Fin (e::es).length, ValidAt g m (ptr+i.val) (e::es)[i.val]) :
    ValidAt g m ptr e ∧ ∀ i : Fin es.length, ValidAt g m (ptr+1+i.val) es[i.val] := by
  refine ⟨by simpa using h 0, fun i => ?_⟩
  simpa only [Fin.val_succ, List.getElem_cons_succ, ← Nat.add_assoc, Nat.add_right_comm] using h i.succ

private theorem tested {g : Args W} {m : Memory W} {c : Config W p r} (link : Linked M pc reg done)
    (entry : c.pc = pc (.inl .test)) (ready : Ready g reg c) (n : ℕ)
    (count : c.reg (reg 14) = (n : Word W)) (fit : n < 2^W) :
    ∃ d, Prefix M m c d [] [.tick] ∧ d.pc = (if n=0 then done else pc (.inr (.inl 0))) ∧
      d.reg = c.reg ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent :=
  test_run (controls link) m g c entry ready n count fit

private theorem iteration_run (link : Linked M pc reg done) (g : Args W) (m : Memory W) (c : Config W p r)
    (ptr rem : ℕ) (e : Row) (entry : c.pc = pc (.inl .test)) (ready : Ready g reg c)
    (count : c.reg (reg 14) = ((rem+1 : ℕ) : Word W)) (pointer : c.reg (reg 5) = (ptr : Word W))
    (countFit : rem+1 < 2^W) (valid : ValidAt g m ptr e) :
    ∃ d, Prefix M m c d e.2 (.tick :: fieldEvents g m ptr e ++ [.tick,.tick]) ∧
      d.pc = pc (.inl .test) ∧ d.reg (reg 14) = (rem : Word W) ∧ d.reg (reg 5) = ((ptr+1 : ℕ) : Word W) ∧
      Frame reg c d ∧ d.privateMem = PrivateFields.storeBits (g.slot e.1) e.2 c.privateMem ∧
      d.persistent = c.persistent := by
  obtain ⟨a, guard, hpc, hreg, hmem, hper⟩ := tested (m := m) link entry ready (rem+1) count countFit
  have fa : Frame reg c a := fun i _ => congrFun hreg i
  have ra := ready.frame fa
  obtain ⟨b, body, hb, h5, h14, fb, bm, bp⟩ := field_run link g m a ptr e
    (by simpa using hpc) ra (hreg ▸ pointer) valid
  obtain ⟨d, tail, hd, dc, dp, fd, dm, ds⟩ := advance_run (controls link) m g b hb
    (ra.frame fb) rem ptr (h14.trans ((congrFun hreg _).trans count)) (h5.trans ((congrFun hreg _).trans pointer))
  refine ⟨d, ?_, hd, dc, dp, (fa.trans fb).trans fd, ?_, ds.trans (bp.trans hper)⟩
  · simpa only [List.nil_append, List.append_nil, List.singleton_append, List.cons_append] using
      (guard.trans body).trans tail
  · rw [dm, bm, hmem]

private theorem loop_run (link : Linked M pc reg done) (g : Args W) (m : Memory W) (es : List Row)
    (c : Config W p r) (ptr : ℕ) (entry : c.pc = pc (.inl .test)) (ready : Ready g reg c)
    (count : c.reg (reg 14) = (es.length : Word W)) (pointer : c.reg (reg 5) = (ptr : Word W))
    (countFit : es.length < 2^W) (valid : ∀ i : Fin es.length, ValidAt g m (ptr+i.val) es[i.val]) :
    ∃ d, Prefix M m c d (stream es) (loopEvents g m ptr es) ∧ d.pc = done ∧ Frame reg c d ∧
      d.privateMem = storeRows g.scratchBase g.slotStride es c.privateMem ∧ d.persistent = c.persistent := by
  induction es generalizing ptr c with
  | nil =>
    obtain ⟨d, pref, hpc, hreg, hm, hp⟩ := tested (m := m) link entry ready 0 count countFit
    exact ⟨d,pref,hpc,fun i _ => congrFun hreg i,hm,hp⟩
  | cons e es ih =>
    obtain ⟨ve, vs⟩ := suffixValid g m ptr e es valid
    obtain ⟨a, step, hep, hcount, hptr, fa, hm, hp⟩ :=
      iteration_run link g m c ptr es.length e entry ready count pointer countFit ve
    obtain ⟨d, tail, hd, fd, dm, ds⟩ := ih a (ptr+1) hep (ready.frame fa) hcount hptr
      (by simpa using Nat.lt_trans (Nat.lt_succ_self es.length) countFit) vs
    refine ⟨d, step.trans tail, hd, fa.trans fd, ?_, ds.trans hp⟩
    rw [dm,hm]
    rfl

/-- Exact native prefix, including the public count probe, all field bits,
and the final empty test. The continuation receives the unconsumed suffix. -/
theorem native (link : Linked M pc reg done) (g : Args W) (m : Memory W) (es : List Row)
    (c : Config W p r) (entry : c.pc = pc (.inl .one)) (inputs : Inputs g reg c)
    (fit : g.countBase+g.owner < 2^W) (count : (m (g.countBase+g.owner)).val = es.length)
    (valid : ValidRows g m es) :
    ∃ d, Prefix M m c d (stream es) (events g m es) ∧ d.pc = done ∧
      (∀ i, i ≠ reg 3 → i ≠ reg 21 → (∀ j ∈ scratch, i ≠ reg j) → d.reg i = c.reg i) ∧
      d.privateMem = storeRows g.scratchBase g.slotStride es c.privateMem ∧ d.persistent = c.persistent := by
  obtain ⟨a, init, ep, hc, hp, ready, hm, hs, keep⟩ := setup_run (controls link) m g c entry inputs fit
  have cf : es.length < 2^W := count ▸ (m (g.countBase+g.owner)).isLt
  have hcount : a.reg (reg 14) = (es.length : Word W) := by
    apply Fin.ext
    rw [hc, count, Fin.val_natCast, Nat.mod_eq_of_lt cf]
  obtain ⟨d, tail, hd, frame, dm, ds⟩ := loop_run link g m es a g.row ep ready hcount hp cf valid
  exact ⟨d, init.trans tail, hd, fun i h3 h21 hi => (frame i hi).trans (keep i h3
    (hi 5 (by decide)) (hi 14 (by decide)) h21), dm.trans (congrArg _ hm), ds.trans hs⟩

/-- With any shorter stream, all complete leading fields still run once.
The first incomplete field prevents the burst from returning. -/
private theorem loop_short (link : Linked M pc reg done) (g : Args W) (m : Memory W) (es : List Row)
    (c : Config W p r) (ptr : ℕ) (entry : c.pc = pc (.inl .test)) (ready : Ready g reg c)
    (count : c.reg (reg 14) = (es.length : Word W)) (pointer : c.reg (reg 5) = (ptr : Word W))
    (countFit : es.length < 2^W) (valid : ∀ i : Fin es.length, ValidAt g m (ptr+i.val) es[i.val])
    (bs : List Bool) (short : bs.length < (stream es).length) : ¬ DFS.Returns M c m bs := by
  induction es generalizing ptr c bs with
  | nil => simp [stream] at short
  | cons e es ih =>
    obtain ⟨ve, vs⟩ := suffixValid g m ptr e es valid
    by_cases h : bs.length < e.2.length
    · obtain ⟨d, test, hpc, hr, _, _⟩ := tested (m := m) link entry ready (es.length+1) count countFit
      apply mt (test.returns bs).mp
      exact field_short link g m d ptr e (by simpa using hpc)
        (ready.frame (fun i _ => congrFun hr i)) (hr ▸ pointer) ve bs h
    · let first : Row := (e.1, bs.take e.2.length)
      have eqLen : first.2.length = e.2.length := by simpa [first] using Nat.min_eq_left (by omega : e.2.length ≤ bs.length)
      have vf : ValidAt g m ptr first := ⟨ve.1, ve.2.1.trans eqLen.symm, eqLen ▸ ve.2.2⟩
      obtain ⟨a, step, ep, hc, hp, fr, _, _⟩ :=
        iteration_run link g m c ptr es.length first entry ready count pointer countFit vf
      have reject := ih a (ptr+1) ep (ready.frame fr) hc hp
        (by simpa using Nat.lt_trans (Nat.lt_succ_self es.length) countFit) vs (bs.drop e.2.length) (by
          simp only [stream, List.flatMap_cons, List.length_append] at short
          simp only [stream, List.length_drop]; omega)
      have back := mt (step.returns (bs.drop e.2.length)).mp reject
      simpa only [first, List.take_append_drop] using back

theorem native_short (link : Linked M pc reg done) (g : Args W) (m : Memory W) (es : List Row)
    (c : Config W p r) (entry : c.pc = pc (.inl .one)) (inputs : Inputs g reg c)
    (fit : g.countBase+g.owner < 2^W) (count : (m (g.countBase+g.owner)).val = es.length)
    (valid : ValidRows g m es) (bs : List Bool) (short : bs.length < (stream es).length) :
    ¬ DFS.Returns M c m bs := by
  obtain ⟨a, init, ep, hc, hp, ready, _, _, _⟩ := setup_run (controls link) m g c entry inputs fit
  have cf : es.length < 2^W := count ▸ (m (g.countBase+g.owner)).isLt
  have hcount : a.reg (reg 14) = (es.length : Word W) := by
    apply Fin.ext
    rw [hc, count, Fin.val_natCast, Nat.mod_eq_of_lt cf]
  exact mt (init.returns bs).mp (loop_short link g m es a g.row ep ready hcount hp cf valid bs short)

end PairSimulation.ShrinkHiddenGuess

end VPVNP
end Computability
end OAI
