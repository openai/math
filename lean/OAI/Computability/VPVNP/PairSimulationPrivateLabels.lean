import OAI.Computability.VPVNP.PairSimulationKernels
import OAI.Computability.VPVNP.PairSimulationCounters
import Mathlib.Data.List.Count

/-!
# Accumulating one map's labels in private memory

The motif interpreter emits one ordinal per copy, including repeated
ordinals. Seven opcodes visit these private words in sequence and increment
the corresponding private counters. This is the array read by the external
histogram flush at the end of the final-site call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.PrivateLabels

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r k t : ℕ}

private abbrev word (w n : ℕ) : Word w := (n : Word w)

private theorem val_word {n : ℕ} (h : n < 2^w) : (word w n).val = n := Nat.mod_eq_of_lt h

/-- Registers hold the label cursor, its exclusive end, histogram base, one,
a label/address, and a count. The same table works at every word width. -/
def instruction (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (done : Fin p) : Fin 7 → Instr w p r k :=
  ![.jumpEq (reg 0) (reg 1) done (pc 1), .loadPrivate (reg 4) (reg 0) (pc 2),
    .binary .add (reg 4) (reg 2) (reg 4) (pc 3), .loadPrivate (reg 5) (reg 4) (pc 4),
    .binary .add (reg 5) (reg 5) (reg 3) (pc 5), .storePrivate (reg 4) (reg 5) (pc 6),
    .binary .add (reg 0) (reg 0) (reg 3) (pc 0)]

theorem resize_instruction (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (done : Fin p) (i : Fin 7) :
    (instruction (w := 1) (k := k) pc reg done i).resize w = instruction pc reg done i := by
  fin_cases i <;> rfl

/-- The machine contains the seven instructions that scan emitted label ordinals and increment
their private histogram cells. -/
def Linked (M : Machine w p r k) (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (done : Fin p) : Prop :=
  ∀ i, M.code (pc i) = instruction pc reg done i

/-- The folded histogram uses a separate update for each emitted occurrence. -/
def accumulate (base : ℕ) : List (Fin t) → (Word w → Word w) → Word w → Word w
  | [], mem => mem
  | j :: js, mem =>
    let addr := word w (base + j.val)
    accumulate base js (Function.update mem addr (mem addr + 1))

theorem accumulate_at (base : ℕ) (names : List (Fin t)) (mem : Word w → Word w)
    (hfit : base+t ≤ 2^w) (i : Fin t) :
    accumulate base names mem (word w (base+i.val)) = mem (word w (base+i.val)) + (names.count i : Word w) := by
  induction names generalizing mem with
  | nil => simp [accumulate]
  | cons j js ih =>
    rw [accumulate, ih]
    by_cases h : j = i
    · subst j; simp [add_assoc]; exact add_comm _ _
    · have hne : word w (base+i.val) ≠ word w (base+j.val) := by
        intro e
        have hi := i.isLt
        have hj := j.isLt
        have he := congrArg Fin.val e
        rw [val_word (by omega : base+i.val < 2^w), val_word (by omega : base+j.val < 2^w)] at he
        exact h (Fin.ext (Nat.add_left_cancel he).symm)
      rw [Function.update_of_ne hne]
      simp [h]

variable {M : Machine w p r k} {pc : Fin 7 → Fin p} {reg : Fin 6 ↪ Fin r} {done : Fin p}

private theorem step_at (hl : Linked M pc reg done) (i : Fin 7) (c : Config w p r)
    (hc : c.pc = pc i) : M.program.step c = (instruction pc reg done i).run M.publicData c := by
  simp [Machine.program, hc, hl i]

private theorem iteration (hl : Linked M pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (src base : ℕ) (j : Fin t) (hs : c.reg (reg 0) = word w src) (hb : c.reg (reg 2) = word w base)
    (hone : c.reg (reg 3) = 1) (hne : c.reg (reg 0) ≠ c.reg (reg 1))
    (hj : c.privateMem (word w src) = word w j.val) :
    ∃ out, Prefix M c (List.replicate 7 .tick) out ∧ out.pc = pc 0 ∧
      out.reg (reg 0) = word w (src+1) ∧
      (∀ i, i ≠ reg 0 → i ≠ reg 4 → i ≠ reg 5 → out.reg i = c.reg i) ∧
      out.privateMem = Function.update c.privateMem (word w (base+j.val)) (c.privateMem (word w (base+j.val))+1) ∧
      out.persistent = c.persistent := by
  let c₁ := {c with pc := pc 1}
  let c₂ := c₁.put (pc 2) (reg 4) (word w j.val)
  let addr := word w (base+j.val)
  let c₃ := c₂.put (pc 3) (reg 4) addr
  let c₄ := c₃.put (pc 4) (reg 5) (c.privateMem addr)
  let c₅ := c₄.put (pc 5) (reg 5) (c.privateMem addr + 1)
  let c₆ := c₅.store (pc 6) addr (c.privateMem addr + 1)
  let out := c₆.put (pc 0) (reg 0) (word w (src+1))
  have s₀ : M.program.step c = .localStep c₁ := by rw [step_at hl 0 c hc]; simp [instruction,Instr.run,hne,c₁]
  have s₁ : M.program.step c₁ = .localStep c₂ := by
    rw [step_at hl 1 c₁ rfl]
    change CallAction.localStep (c₁.put (pc 2) (reg 4) (c.privateMem (c.reg (reg 0)))) = _
    rw [hs,hj]
  have s₂ : M.program.step c₂ = .localStep c₃ := by
    rw [step_at hl 2 c₂ rfl]
    change CallAction.localStep (c₂.put (pc 3) (reg 4) (c₂.reg (reg 2) + c₂.reg (reg 4))) = _
    simp [c₃,c₂,c₁,Config.put,hb,addr,word]
  have s₃ : M.program.step c₃ = .localStep c₄ := by
    rw [step_at hl 3 c₃ rfl]
    change CallAction.localStep (c₃.put (pc 4) (reg 5) (c.privateMem (c₃.reg (reg 4)))) = _
    simp [c₃,c₄,Config.put]
  have s₄ : M.program.step c₄ = .localStep c₅ := by
    rw [step_at hl 4 c₄ rfl]
    change CallAction.localStep (c₄.put (pc 5) (reg 5) (c₄.reg (reg 5) + c₄.reg (reg 3))) = _
    simp [c₅,c₄,c₃,c₂,c₁,Config.put,hone]
  have s₅ : M.program.step c₅ = .localStep c₆ := by
    rw [step_at hl 5 c₅ rfl]
    change CallAction.localStep (c₅.store (pc 6) (c₅.reg (reg 4)) (c₅.reg (reg 5))) = _
    simp [c₆,c₅,c₄,c₃,Config.put]
  have s₆ : M.program.step c₆ = .localStep out := by
    rw [step_at hl 6 c₆ rfl]
    change CallAction.localStep (c₆.put (pc 0) (reg 0) (c₆.reg (reg 0) + c₆.reg (reg 3))) = _
    simp [out,c₆,c₅,c₄,c₃,c₂,c₁,Config.store,Config.put,hs,hone,word]
  refine ⟨out,.tick s₀ (.tick s₁ (.tick s₂ (.tick s₃ (.tick s₄ (.tick s₅ (.tick s₆ (.nil _))))))),
    rfl,by simp [out],?_,rfl,rfl⟩
  intro i h0 h4 h5
  simp [out,c₆,c₅,c₄,c₃,c₂,c₁,Config.store,Config.put,Function.update_of_ne h0,
    Function.update_of_ne h4,Function.update_of_ne h5]

/-- The complete native scan has no probes or binary choices. Its private
state contains every histogram update and preserves every other cell. -/
theorem run_separated (hl : Linked M pc reg done) (names : List (Fin t)) (src base : ℕ)
    (c : Config w p r) (hc : c.pc = pc 0) (hs : c.reg (reg 0) = word w src)
    (he : c.reg (reg 1) = word w (src+names.length)) (hb : c.reg (reg 2) = word w base)
    (h1 : c.reg (reg 3) = 1) (fit : base+t ≤ 2^w) (apart : src+names.length ≤ base ∨ base+t ≤ src)
    (hend : src+names.length < 2^w)
    (hdata : ∀ i : Fin names.length, c.privateMem (word w (src+i.val)) = word w (names[i.val]).val) :
    ∃ out, Prefix M c (List.replicate (7*names.length+1) .tick) out ∧ out.pc = done ∧
      out.privateMem = accumulate base names c.privateMem ∧ out.persistent = c.persistent := by
  induction names generalizing src c with
  | nil =>
    have eq : c.reg (reg 0) = c.reg (reg 1) := hs.trans (by simpa using he.symm)
    let out := {c with pc := done}
    have s : M.program.step c = .localStep out := by rw [step_at hl 0 c hc]; simp [instruction,Instr.run,eq,out]
    exact ⟨out,.tick s (.nil _),rfl,rfl,rfl⟩
  | cons j js ih =>
    have neq : c.reg (reg 0) ≠ c.reg (reg 1) := by
      rw [hs,he]; intro eq
      have h := congrArg Fin.val eq
      rw [val_word (by omega : src < 2^w), val_word hend] at h
      simp at h
    have hj : c.privateMem (word w src) = word w j.val := by simpa using hdata 0
    obtain ⟨c', pre, hc', hs', other, hm, hp⟩ := iteration hl c hc src base j hs hb h1 neq hj
    have endEq : src+1+js.length = src+(j::js).length := by simp; omega
    have tailData (i : Fin js.length) : c'.privateMem (word w (src+1+i.val)) = word w (js[i.val]).val := by
      have hi := i.isLt
      have hj := j.isLt
      have hne : word w (src+1+i.val) ≠ word w (base+j.val) := by
        intro eq
        have h := congrArg Fin.val eq
        simp only [List.length_cons] at apart hend
        rw [val_word (by omega : src+1+i.val < 2^w), val_word (by omega : base+j.val < 2^w)] at h
        omega
      rw [hm, Function.update_of_ne hne]
      simpa [Nat.add_assoc,Nat.add_comm 1] using hdata ⟨i.val+1,by simp⟩
    obtain ⟨out, pre', hpc, hmem, hper⟩ := ih (src+1) c' hc' hs'
      ((other _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans
        (endEq ▸ he)) ((other _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
          (reg.injective.ne (by decide))).trans hb) ((other _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
          (reg.injective.ne (by decide))).trans h1) (by rcases apart with h | h; exact .inl (endEq ▸ h); exact .inr (by omega))
      (endEq ▸ hend) tailData
    refine ⟨out,?_,hpc,?_,hper.trans hp⟩
    · convert pre.append pre' using 1
      rw [← List.replicate_add]
      congr 1
      simp; omega
    · rw [hmem,hm]; rfl

/-- A forward allocation with the counter bank above its label words. -/
theorem run (hl : Linked M pc reg done) (names : List (Fin t)) (src base : ℕ)
    (c : Config w p r) (hc : c.pc = pc 0) (hs : c.reg (reg 0) = word w src)
    (he : c.reg (reg 1) = word w (src+names.length)) (hb : c.reg (reg 2) = word w base)
    (h1 : c.reg (reg 3) = 1) (fit : base+t ≤ 2^w) (before : src+names.length ≤ base)
    (hend : src+names.length < 2^w)
    (hdata : ∀ i : Fin names.length, c.privateMem (word w (src+i.val)) = word w (names[i.val]).val) :
    ∃ out, Prefix M c (List.replicate (7*names.length+1) .tick) out ∧ out.pc = done ∧
      out.privateMem = accumulate base names c.privateMem ∧ out.persistent = c.persistent :=
  run_separated hl names src base c hc hs he hb h1 fit (.inl before) hend hdata

/-- Counting copies in the emitted list recovers the formal map exponent. -/
theorem count_entry {Label : Type} [DecidableEq Label] {u : ℕ} (f : Fin u → Label)
    (idx : Label ≃ Fin t) (label : Label) :
    ((List.ofFn f).map idx).count (idx label) = MotifConversion.entryMultiplicity f label := by
  rw [List.count_map_of_injective _ _ idx.injective]
  induction u with
  | zero => simp [MotifConversion.entryMultiplicity]
  | succ u ih =>
    unfold MotifConversion.entryMultiplicity
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.count_cons]
    by_cases h : f 0 = label <;> simp [h, ih, MotifConversion.entryMultiplicity, Nat.add_comm]


/-- The last private scan of a vertex links directly to the common external
histogram suffix. Previously accumulated maps and every copy of the last
map are both present when the suffix is flushed. -/
theorem run_flush {entry : Fin 7 → Fin p} {flushPC : Fin 7 → Fin p} {flushReg : Fin 6 ↪ Fin r}
    {exit : Fin p} (hl : Linked M pc reg (entry 0)) (hf : Counters.Linked M flushPC flushReg exit)
    (param : Fin 4 → Fin k) (hcode : ∀ i, M.code (entry i) = Counters.entryCode entry flushReg param (flushPC 0) i)
    (names : List (Fin t)) (src base external grammar : ℕ) (c : Config w p r) (hc : c.pc = pc 0)
    (hs : c.reg (reg 0) = word w src) (he : c.reg (reg 1) = word w (src+names.length))
    (hb : c.reg (reg 2) = word w base) (h1 : c.reg (reg 3) = 1)
    (fit : base+t < 2^w) (before : src+names.length ≤ base)
    (hdata : ∀ i : Fin names.length, c.privateMem (word w (src+i.val)) = word w (names[i.val]).val)
    (hpub : M.publicData (param 0) = word w external)
    (hgrammar : M.publicData (param 1) = word w grammar) (hcount : M.publicData (param 2) = word w t)
    (hbase : M.publicData (param 3) = word w base) (hout : external+grammar+t < 2^w)
    (prior : Fin t → ℕ) (hprior : ∀ i : Fin t, c.privateMem (word w (base+i)) = word w (prior i)) (m : Memory w) :
    let target := Counters.addHistogram external grammar (fun i => prior i + names.count i) m
    ∃ out es, out.pc = exit ∧ es.length = 7*names.length+1+(7*t+8) ∧ countProbes es = 2*t ∧
      choiceBits es = [] ∧ after m es = target ∧ ∀ fuel bs,
      execute M.program (fuel+es.length) c m bs =
        (execute M.program fuel out target bs).map (fun r => ⟨es++r.events,r.result⟩) := by
  obtain ⟨q,hpre,hq,hm,_⟩ := run hl names src base c hc hs he hb h1 fit.le before
    (by omega) hdata
  have hh (i : Fin t) : q.privateMem (word w (base+i)) = word w (prior i + names.count i) := by
    rw [hm, accumulate_at base names _ fit.le i, hprior i]
    simp [word]
  obtain ⟨out, fs, hp, _, _, hlen, hpr, hchoices, hend, hrun⟩ :=
    Counters.execute_flush hf entry param hcode q hq external grammar base hpub hgrammar hcount hbase
      (fun i => prior i + names.count i) hh fit hout m
  let n := 7*names.length+1
  have prep (n : ℕ) (es : List (Event w)) : choiceBits (List.replicate n .tick ++ es) = choiceBits es ∧
      countProbes (List.replicate n .tick ++ es) = countProbes es ∧ after m (List.replicate n .tick ++ es) = after m es := by
    induction n with
    | zero => simp
    | succ n ih => simpa only [List.replicate_succ, List.cons_append, choiceBits, countProbes, after,
        List.foldl_cons, update] using ih
  have hbts : choiceBits (List.replicate n (.tick : Event w)) = [] := by simpa [choiceBits] using (prep n []).1
  refine ⟨out,List.replicate n .tick ++ fs,hp,by simp [n,hlen],(prep n fs).2.1.trans hpr,
    (prep n fs).1.trans hchoices,(prep n fs).2.2.trans hend,?_⟩
  intro fuel bs
  have hp := hpre.execute (fuel+7*t+8) m bs
  change execute M.program ((fuel+7*t+8)+(List.replicate n (.tick : Event w)).length) c m
    (choiceBits (List.replicate n .tick) ++ bs) = _ at hp
  rw [hbts,List.nil_append,List.length_replicate] at hp
  rw [List.length_append,List.length_replicate,hlen,
    show fuel + (n + (7*t+8)) = (fuel+7*t+8)+n by omega, hp, hrun]
  simp [Option.map_map,Function.comp_def,List.append_assoc,n]

end PairSimulation.PrivateLabels

end VPVNP
end Computability
end OAI
