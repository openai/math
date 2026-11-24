import OAI.Computability.VPVNP.PrimedStackRAMNodeTable

/-!
# Native execution of the complete preorder-node table

The evaluator below reads the same finite word encodings as the linked loops
and retains the unused choice suffix for the surrounding program. A missing
choice or failed guard aborts the native execution at every sufficient fuel.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedCounter

variable {r k p w : ℕ}

/-- Result of a successful RAM segment, including its event trace, final registers and memory,
and the choice bits available to the continuation. -/
structure Output (w r : ℕ) where
  /-- RAM events in execution order, including ticks, choices, and memory probes. -/
  events : List (Event w)
  /-- Register contents passed to the next segment. -/
  regs : Regs w r
  /-- External memory after the segment has executed its writes. -/
  mem : Memory w
  /-- Suffix of the choice stream left for the next segment. -/
  bits : List Bool

/-- Prefix a successful segment’s trace with the events of an earlier segment. -/
def Output.prepend (es : List (Event w)) (o : Output w r) := {o with events := es ++ o.events}

/-- Partial execution of a RAM segment from public words, a state word, registers, memory, and
a choice stream. Success returns the trace and the state needed by the continuation. -/
abbrev Kernel (w r k : ℕ) :=
  (Fin k → Word w) → Word w → Regs w r → Memory w → List Bool → Option (Output w r)

/-- Execute a straight-line list of opcodes and carry the choice stream through to the
continuation. -/
def lineKernel (ops : List (Op r k)) : Kernel w r k := fun pub st rs mem bits =>
  (trace pub st ops rs mem).map fun (es,rs',m') => ⟨es, rs', m', bits⟩

/-- Consume one word’s worth of choice bits, record the guessing loop’s trace, and update its
three registers. A short stream causes rejection. -/
def guessKernel (reg : Fin 3 ↪ Fin r) : Kernel w r k := fun _ _ rs mem bits =>
  (takeWord w bits).map fun (v, tail) =>
    ⟨GuessWord.trace v, GuessWord.resultRegs reg rs v, mem, tail⟩

/-- Run two kernels in order, passing the first result’s registers, memory, and unused bits to
the second and appending their traces on success. -/
def seqKernel (a b : Kernel w r k) : Kernel w r k := fun pub st rs mem bits => do
  let x ← a pub st rs mem bits
  let y ← b pub st x.regs x.mem x.bits
  return y.prepend x.events

/-- Compare two registers to select a kernel and prefix its successful trace with the tick
spent on the comparison. -/
def eqKernel (l q : Fin r) (a b : Kernel w r k) : Kernel w r k := fun pub st rs mem bits =>
  ((if rs l = rs q then a else b) pub st rs mem bits).map (Output.prepend [.tick])

private def extend (es : List (Event w)) (rep : Report w) : Report w := ⟨es ++ rep.events, rep.result⟩

private theorem extend_comp (a b : List (Event w)) : extend a ∘ extend b = extend (a ++ b) := by
  funext z
  simp [extend, List.append_assoc]

/-- Bounded refinement for every containing table and every continuation. -/
structure Refines (a : Flow r k) (budget : ℕ) (f : Kernel w r k) : Prop where
  bounded {pub st rs mem bits out} (h : f pub st rs mem bits = some out) : out.events.length ≤ budget
  execute {p : ℕ} {M : Machine w p r k} {label : a.Label → Fin p} {stop bad : Fin p}
      (hl : Flow.Linked M a label stop bad) (hb : M.code bad = .reject)
      (st : Word w) (rs : Regs w r) (priv : Word w → Word w) (m : Memory w)
      (bs : List Bool) (fuel : ℕ) (hf : budget ≤ fuel) :
      BurstRAM.execute M.program fuel ⟨label a.entry,st,rs,priv⟩ m bs =
        (f M.publicData st rs m bs).bind fun o =>
          (BurstRAM.execute M.program (fuel-o.events.length) ⟨stop,st,o.regs,priv⟩ o.mem o.bits).map
            (extend o.events)

private theorem length_trace {ops : List (Op r k)} {pub : Fin k → Word w} {st : Word w}
    {rs rs' : Regs w r} {m m' : Memory w} {es} (ht : trace pub st ops rs m = some (es,rs',m')) :
    es.length = ops.length := by
  induction ops generalizing rs m es with
  | nil => simp [trace] at ht; rw [ht.1]; rfl
  | cons op ops ih =>
    cases he : op.effect pub st rs m with
    | none => simp [trace, he] at ht
    | some t =>
      obtain ⟨e,r₁,m₁⟩ := t
      cases hs : trace pub st ops r₁ m₁ with
      | none => simp [trace, he, hs] at ht
      | some t =>
        obtain ⟨es₁,r₂,m₂⟩ := t
        simp [trace, he, hs] at ht
        obtain ⟨rfl, rfl, rfl⟩ := ht
        simp [ih hs]

theorem lines_refine (ops : List (Op r k)) (hn : ops ≠ []) :
    Refines (lines ops hn) ops.length (lineKernel (w := w) ops) := by
  constructor
  · intro pub st rs mem bits out h
    obtain ⟨⟨es,rs',m'⟩,hs,rfl⟩ := Option.map_eq_some_iff.mp h
    exact (length_trace hs).le
  · intro p M label stop bad hl hb st rs priv m bs fuel hf
    have he := (contains_lines ops hn label stop bad hl).execute hb st rs priv m bs (fuel-ops.length)
    rw [Nat.sub_add_cancel hf, run_eq_trace] at he
    rw [he]
    cases ht : trace M.publicData st ops rs m with
    | none => simp [lineKernel, ht]
    | some t =>
      obtain ⟨es,rs',m'⟩ := t
      simp [lineKernel, ht, length_trace ht]
      rfl

private theorem takeWord_short {bits : List Bool} (hn : takeWord w bits = none) : bits.length < w := by
  by_contra! hlen
  obtain ⟨v,hv⟩ := GuessWord.exists_wordBits (w := w) (bits.take w) (by simp [hlen])
  have h := (takeWord_eq_some_iff (w := w) bits v (bits.drop w)).mpr (by rw [hv, List.take_append_drop])
  rw [hn] at h
  contradiction

theorem guess_refine (reg : Fin 3 ↪ Fin r) :
    Refines (GuessWord.flow (k := k) reg) (4*w+4) (guessKernel (w := w) reg) := by
  constructor
  · intro pub st rs mem bits o h
    obtain ⟨⟨v,t⟩,_,rfl⟩ := Option.map_eq_some_iff.mp h
    exact (show (GuessWord.trace v).length = 4*w+4 by simp [GuessWord.trace]).le
  · intro p M label stop bad hl _ st rs priv m bs fuel hf
    cases h : takeWord w bs with
    | none =>
      simp only [guessKernel, h, Option.map_none, Option.bind_none]
      exact GuessWord.native_short (GuessWord.contains_flow hl) _ rfl bs (takeWord_short h) fuel m
    | some t =>
      obtain ⟨v,tail⟩ := t
      have hbits := (takeWord_eq_some_iff ..).mp h
      have hp := GuessWord.flow_native_exact hl (⟨label _,st,rs,priv⟩ : Config w p r) rfl v
      have he := hp.execute (fuel-(4*w+4)) m tail
      have hlen : (GuessWord.trace v).length = 4*w+4 := by simp [GuessWord.trace]
      have hchoice : choiceBits (GuessWord.trace v) = wordBits v := by simp [GuessWord.trace, choiceBits]
      rw [hlen, Nat.sub_add_cancel hf, hchoice, ← hbits] at he
      simp only [guessKernel, h, Option.map_some, Option.bind_some, hlen]
      exact he

theorem Refines.seq {a b : Flow r k} {na nb : ℕ} {fa fb : Kernel w r k}
    (ha : Refines a na fa) (hb : Refines b nb fb) :
    Refines (.seq a b) (na + nb) (seqKernel fa fb) := by
  constructor
  · intro pub st rs mem bits o h
    simp only [seqKernel, bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, he⟩ := h
    cases he
    exact (List.length_append ..).trans_le (Nat.add_le_add (ha.bounded hx) (hb.bounded hy))
  · intro p M label stop bad hl hbad st rs priv m bs fuel hf
    have he := ha.execute hl.seqLeft hbad st rs priv m bs fuel (by omega)
    change BurstRAM.execute M.program fuel ⟨label (.inl a.entry),st,rs,priv⟩ m bs = _
    erw [he]
    cases hx : fa M.publicData st rs m bs with
    | none => simp [seqKernel, hx]
    | some x =>
      have hlen := ha.bounded hx
      have he' := hb.execute hl.seqRight hbad st x.regs priv x.mem x.bits (fuel-x.events.length) (by omega)
      simp only [seqKernel, hx, Option.bind_some]
      erw [he']
      cases hy : fb M.publicData st x.regs x.mem x.bits with
      | none => simp [hy]
      | some y =>
        simp [hy, Output.prepend, Option.map_map,
          extend_comp, Nat.sub_add_eq]

theorem Refines.ifEq {a b : Flow r k} {na nb : ℕ} {fa fb : Kernel w r k}
    (l q : Fin r) (ha : Refines a na fa) (hb : Refines b nb fb) :
    Refines (.ifEq l q a b) (1+max na nb) (eqKernel l q fa fb) := by
  constructor
  · intro pub st rs mem bits o h
    unfold eqKernel at h
    split at h <;> obtain ⟨x,hx,rfl⟩ := Option.map_eq_some_iff.mp h
    · have := ha.bounded hx; simp [Output.prepend]; omega
    · have := hb.bounded hx; simp [Output.prepend]; omega
  · intro p M label stop bad hl hbad st rs priv m bs fuel hf
    obtain ⟨f,rfl⟩ : ∃ f, fuel = f+1 := ⟨fuel-1, by omega⟩
    change BurstRAM.execute M.program (f+1) ⟨label (.inl ()),st,rs,priv⟩ m bs = _
    rw [hl.execute_ifEq]
    by_cases h : rs l = rs q
    · have he := ha.execute hl.ifEqYes hbad st rs priv m bs f (by omega)
      simp only [Function.comp_def] at he
      simp only [h, ite_true, eqKernel]
      erw [he]
      cases fa M.publicData st rs m bs <;> simp [Output.prepend, extend,
        Option.map_map, Function.comp_def, Report.prepend]
      rfl
    · have he := hb.execute hl.ifEqNo hbad st rs priv m bs f (by omega)
      simp only [Function.comp_def] at he
      simp only [h, ite_false, eqKernel]
      erw [he]
      cases fb M.publicData st rs m bs <;> simp [Output.prepend, extend,
        Option.map_map, Function.comp_def, Report.prepend]
      rfl

/-- Guess the terminal position into register 2, then run the leaf checks and record its
production. -/
def leafKernel : Kernel w 16 11 :=
  seqKernel (guessKernel (guessRegs 2 (by decide) (by decide))) (lineKernel leafLines)

/-- Guess the split and the two child states into registers 2, 3, and 4, then execute the
binary production and stack updates. -/
def binaryKernel : Kernel w 16 11 :=
  seqKernel (guessKernel (guessRegs 2 (by decide) (by decide))) <|
    seqKernel (guessKernel (guessRegs 3 (by decide) (by decide))) <|
      seqKernel (guessKernel (guessRegs 4 (by decide) (by decide))) (lineKernel binaryLines)

/-- Pop the pending frame, compare its degree with zero, and run the leaf or binary kernel
selected by that comparison. -/
def nodeKernel : Kernel w 16 11 :=
  seqKernel (lineKernel pop) (eqKernel 0 12 leafKernel binaryKernel)

/-- Refinement of the complete native node. The continuation receives the
true post-memory and remaining bits. -/
theorem node_refines : Refines nodeFlow (12*w+90) (nodeKernel (w := w)) := by
  have l := (guess_refine (w := w) (guessRegs 2 (by decide) (by decide))).seq
    (lines_refine leafLines (by decide))
  have b := (guess_refine (w := w) (guessRegs 2 (by decide) (by decide))).seq
    ((guess_refine (w := w) (guessRegs 3 (by decide) (by decide))).seq
      ((guess_refine (w := w) (guessRegs 4 (by decide) (by decide))).seq
        (lines_refine binaryLines (by decide))))
  have res := (lines_refine pop (by decide)).seq (Refines.ifEq 0 12 l b)
  have he : 12*w+90 = 13 + (1 + max (4*w+4+32) (4*w+4+(4*w+4+(4*w+4+64)))) := by omega
  rw [he]
  exact res

end PrimedStackRAM

end VPVNP
end Computability
end OAI
