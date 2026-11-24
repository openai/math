import OAI.Computability.VPVNP.PairSimulationHistory
import OAI.Computability.VPVNP.LiveNominationSweep
import OAI.Computability.VPVNP.RAMRecords
import OAI.Computability.VPVNP.RAMUniform
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases

/-!
# Flushing a final vertex's gadget histogram

At the end of its burst the vertex has a private array of gadget exponents.
The shared array holds the nominated production histogram first and the
gadget histogram second. Seven fixed instructions loop over the suffix.
Each iteration loads one private count and makes one external read and write.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.Counters

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- Registers hold external cursor, external end, private cursor, one,
external count, and local count. -/
def instruction (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (done : Fin p) : Fin 7 → Instr w p r k :=
  ![.jumpEq (reg 0) (reg 1) done (pc 1), .loadPrivate (reg 5) (reg 2) (pc 2),
    .readExternal (reg 4) (reg 0) (pc 3), .binary .add (reg 4) (reg 4) (reg 5) (pc 4),
    .writeExternal (reg 0) (reg 4) (pc 5), .binary .add (reg 0) (reg 0) (reg 3) (pc 6),
    .binary .add (reg 2) (reg 2) (reg 3) (pc 0)]

theorem resize_instruction (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (done : Fin p) (i : Fin 7) :
    (instruction (w := 1) (k := k) pc reg done i).resize w = instruction pc reg done i := by
  fin_cases i <;> rfl

/-- Require the seven code rows of the histogram flush at their assigned labels. They
accumulate the local gadget counts into the shared histogram suffix and jump to `done` at
its end. -/
def Linked (M : Machine w p r k) (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (done : Fin p) : Prop :=
  ∀ i, M.code (pc i) = instruction pc reg done i

variable {M : Machine w p r k} {pc : Fin 7 → Fin p} {reg : Fin 6 ↪ Fin r} {done : Fin p}

private abbrev word (w i : ℕ) : Word w := (i : Word w)

private theorem val_word {i : ℕ} (hi : i < 2 ^ w) : (word w i).val = i := Nat.mod_eq_of_lt hi

private theorem step_at (hl : Linked M pc reg done) (i : Fin 7) (c : Config w p r) (hc : c.pc =
    pc i) :
    M.program.step c = (instruction pc reg done i).run M.publicData c := by simp [Machine.program,
      hc, hl i]

private theorem local_step {c d : Config w p r} (hs : M.program.step c = .localStep d)
    (fuel : ℕ) (m : Memory w) (bits : List Bool) :
    execute M.program (fuel+1) c m bits = (execute M.program fuel d m bits).map
      (Report.prepend .tick) := by
  simp only [execute, hs]

private theorem read_step {c : Config w p r} {a : Word w} {f : Word w → Config w p r}
    (hs : M.program.step c = .read a f) (fuel : ℕ) (m : Memory w) (bits : List Bool) :
    execute M.program (fuel+1) c m bits =
      (execute M.program fuel (f (m a.val)) m bits).map (Report.prepend (.read a (m a.val))) := by
  simp only [execute, hs]

private theorem write_step {c d : Config w p r} {a v : Word w} (hs : M.program.step c =
    .write a v d)
    (fuel : ℕ) (m : Memory w) (bits : List Bool) :
    execute M.program (fuel+1) c m bits =
      (execute M.program fuel d (writeMemory m a v) bits).map (Report.prepend (.write a v)) := by
  simp only [execute, hs]

private def nextConfig (c : Config w p r) (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r)
    (src dst : ℕ) (old : Word w) : Config w p r :=
  let gain := c.privateMem (word w src)
  let cp := c.put (pc 2) (reg 5) gain
  let cr := cp.put (pc 3) (reg 4) old
  let ca := cr.put (pc 4) (reg 4) (old + gain)
  let cd := ca.put (pc 6) (reg 0) (word w (dst+1))
  cd.put (pc 0) (reg 2) (word w (src+1))

private def componentEvents (address old gain : Word w) : List (Event w) :=
  [.tick, .tick, .read address old, .tick, .write address (old+gain), .tick, .tick]

private theorem execute_component (hl : Linked M pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (src dst : ℕ) (hd : dst < 2 ^ w) (hsrc : c.reg (reg 2) = word w src)
    (hdst : c.reg (reg 0) = word w dst) (hone : c.reg (reg 3) = 1) (hne : c.reg (reg 0) ≠ c.reg
      (reg 1))
    (fuel : ℕ) (m : Memory w) (bs : List Bool) :
    let gain := c.privateMem (word w src)
    execute M.program (fuel+7) c m bs =
      (execute M.program fuel (nextConfig c pc reg src dst (m dst))
        (writeMemory m (word w dst) (m dst+gain)) bs).map
          (fun rep ↦ ⟨componentEvents (word w dst) (m dst) gain ++ rep.events, rep.result⟩) := by
  let gain := c.privateMem (word w src)
  let ct := {c with pc := pc 1}
  let cp := c.put (pc 2) (reg 5) gain
  let cr := cp.put (pc 3) (reg 4) (m dst)
  let ca := cr.put (pc 4) (reg 4) (m dst + gain)
  let cw := {ca with pc := pc 5}
  let cd := ca.put (pc 6) (reg 0) (word w (dst+1))
  have s0 : M.program.step c = .localStep ct := by
    rw [step_at hl 0 c hc]
    change CallAction.localStep {c with
      pc := if c.reg (reg 0) = c.reg (reg 1) then done else pc 1} = _
    simp [hne, ct]
  have s1 : M.program.step ct = .localStep cp := by
    rw [step_at hl 1 ct rfl]
    change CallAction.localStep (ct.put (pc 2) (reg 5) (c.privateMem (c.reg (reg 2)))) = _
    rw [hsrc]
    rfl
  have s2 : M.program.step cp = .read (word w dst) (fun v ↦ cp.put (pc 3) (reg 4) v) := by
    rw [step_at hl 2 cp rfl]
    change CallAction.read (cp.reg (reg 0)) _ = _
    simp [cp, Config.put, hdst]
  have s3 : M.program.step cr = .localStep ca := by
    rw [step_at hl 3 cr rfl]
    change CallAction.localStep (cr.put (pc 4) (reg 4) (cr.reg (reg 4) + cr.reg (reg 5))) = _
    simp [ca, cr, cp, Config.put]
  have s4 : M.program.step ca = .write (word w dst) (m dst + gain) cw := by
    rw [step_at hl 4 ca rfl]
    change CallAction.write (ca.reg (reg 0)) (ca.reg (reg 4)) cw = _
    simp [ca, cr, cp, Config.put, hdst]
  have s5 : M.program.step cw = .localStep cd := by
    rw [step_at hl 5 cw rfl]
    change CallAction.localStep (cw.put (pc 6) (reg 0) (cw.reg (reg 0) + cw.reg (reg 3))) = _
    simp [cd, cw, ca, cr, cp, Config.put, hdst, hone, word]
  have s6 : M.program.step cd = .localStep (nextConfig c pc reg src dst (m dst)) := by
    rw [step_at hl 6 cd rfl]
    change CallAction.localStep (cd.put (pc 0) (reg 2) (cd.reg (reg 2) + cd.reg (reg 3))) = _
    simp [nextConfig, cd, ca, cr, cp, Config.put, hsrc, hone, word, gain]
  dsimp only
  rw [local_step s0, local_step s1, read_step s2, val_word hd, local_step s3, write_step s4,
    local_step s5, local_step s6]
  simp [Option.map_map, Function.comp_def, Report.prepend, componentEvents, gain]

/-- Accumulation at consecutive addresses with the original memory elsewhere. -/
def addRange (src dst n : ℕ) (priv : Word w → Word w) (m : Memory w) (a : ℕ) : Word w :=
  if dst ≤ a ∧ a < dst+n then m a + priv (word w (src+(a-dst))) else m a

private theorem range_succ (src dst n : ℕ) (hd : dst < 2 ^ w) (priv : Word w → Word w)
    (m : Memory w) :
    addRange (src+1) (dst+1) n priv (writeMemory m (word w dst) (m dst+priv (word w src))) =
      addRange src dst (n+1) priv m := by
  funext a
  by_cases ha : a = dst
  · subst a
    simp [addRange, writeMemory, val_word hd]
  · simp only [addRange, writeMemory, val_word hd, ha, ↓reduceIte]
    split_ifs with h h' h' <;> first | rfl | (congr 3; omega)

/-- Genuine chronological transcript of all component updates, including the last loop test. -/
def events (priv : Word w → Word w) (m : Memory w) (src dst : ℕ) : ℕ → List (Event w)
  | 0 => [.tick]
  | n+1 =>
    let gain := priv (word w src)
    componentEvents (word w dst) (m dst) gain ++
      events priv (writeMemory m (word w dst) (m dst+gain)) (src+1) (dst+1) n

theorem events_cost (priv : Word w → Word w) (m : Memory w) (src dst n : ℕ) :
    (events priv m src dst n).length = 7*n+1 ∧ countProbes (events priv m src dst n) = 2*n ∧
      choiceBits (events priv m src dst n) = [] := by
  induction n generalizing m src dst with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨hl,hp,hb⟩ := ih (writeMemory m (word w dst) (m dst+priv (word w src))) (src+1) (dst+1)
    simp [events, componentEvents, countProbes, choiceBits, hl, hp, hb]
    omega

/-- Replaying the burst log at the next call produces exactly the same
memory as the continuation within the current call. -/
theorem after_events (priv : Word w → Word w) (m : Memory w) (src dst n : ℕ)
    (fit : dst + n < 2 ^ w) :
    after m (events priv m src dst n) = addRange src dst n priv m := by
  induction n generalizing m src dst with
  | zero => funext a; simp [after, events, update, addRange]
  | succ n ih =>
    rw [events, show ∀ es tail, after m (es ++ tail) = after (after m es) tail by simp [after]]
    change after (writeMemory m (word w dst) (m dst+priv (word w src))) _ = _
    rw [ih _ (src+1) (dst+1) (by omega)]
    exact range_succ _ _ _ (by omega) _ _

/-- Run the whole suffix within the current burst, then pass control to any
continuation with the updated external memory and original private histogram. -/
theorem execute_range (hl : Linked M pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (src dst n : ℕ) (hsrc : src + n < 2 ^ w) (hdst : dst + n < 2 ^ w)
    (hr : c.reg (reg 0) = word w dst) (he : c.reg (reg 1) = word w (dst + n))
    (hs : c.reg (reg 2) = word w src) (ho : c.reg (reg 3) = 1) (m : Memory w) :
    ∃ out, out.pc = done ∧ out.persistent = c.persistent ∧ out.privateMem = c.privateMem ∧
      out.reg (reg 0) = word w (dst+n) ∧ out.reg (reg 2) = word w (src+n) ∧
      (∀ j, j ≠ reg 0 → j ≠ reg 2 → j ≠ reg 4 → j ≠ reg 5 → out.reg j = c.reg j) ∧
      ∀ fuel bs, execute M.program (fuel+7*n+1) c m bs =
        (execute M.program fuel out (addRange src dst n c.privateMem m) bs).map
          (fun rep ↦ ⟨events c.privateMem m src dst n ++ rep.events, rep.result⟩) := by
  induction n generalizing c src dst m with
  | zero =>
    have h0 : c.reg (reg 0) = c.reg (reg 1) := hr.trans (by simpa using he.symm)
    have s0 : M.program.step c = .localStep {c with pc := done} := by
      rw [step_at hl 0 c hc]
      change CallAction.localStep {c with
        pc := if c.reg (reg 0) = c.reg (reg 1) then done else pc 1} = _
      simp [h0]
    refine ⟨{c with pc := done},rfl,rfl,rfl,by simpa using hr,by simpa using hs,
      fun _ _ _ _ _ ↦ rfl,?_⟩
    intro fuel bs
    have hmem : addRange src dst 0 c.privateMem m = m := by funext a; simp [addRange]
    simp [local_step s0, hmem, events]
    rfl
  | succ n ih =>
    let next := nextConfig c pc reg src dst (m dst)
    let m' := writeMemory m (word w dst) (m dst + c.privateMem (word w src))
    have hn : c.reg (reg 0) ≠ c.reg (reg 1) := by
      rw [hr, he]
      intro h
      have hv := congrArg Fin.val h
      rw [val_word (by omega : dst < 2^w), val_word hdst] at hv
      omega
    have ea : src+1+n = src+(n+1) := by omega
    have eb : dst+1+n = dst+(n+1) := by omega
    have other (j : Fin r) (h0 : j ≠ reg 0) (h2 : j ≠ reg 2) (h4 : j ≠ reg 4) (h5 : j ≠ reg 5) :
        next.reg j = c.reg j := by
      simp [next, nextConfig, Config.put, Function.update_of_ne, h0, h2, h4, h5]
    obtain ⟨out,hpc,hpers,hpriv,hd,hs',ho',run⟩ := ih next rfl (src+1) (dst+1) (ea ▸ hsrc)
      (eb ▸ hdst)
      (by simp [next, nextConfig, Config.put]) (by rw [other,eb,he] <;> simp)
      (by simp [next, nextConfig, Config.put]) (by rw [other,ho] <;> simp) m'
    refine ⟨out,hpc,hpers,hpriv,eb ▸ hd,ea ▸ hs',fun j a b d e ↦ (ho' j a b d e).trans
      (other j a b d e),?_⟩
    intro fuel bs
    rw [show fuel+7*(n+1)+1 = (fuel+7*n+1)+7 by omega,
      execute_component hl c hc src dst (by omega) hs hr ho hn]
    change (execute M.program _ next m' bs).map _ = _
    rw [run]
    have hm : addRange (src+1) (dst+1) n next.privateMem m' =
        addRange src dst (n+1) c.privateMem m := range_succ _ _ _ (by omega) _ _
    rw [hm]
    simp [Option.map_map, Function.comp_def, events, m', next, nextConfig, Config.put]

/-- Logical effect of a single successful vertex. The label number is an
offset in the gadget suffix of the contiguous production/gadget array. -/
def addHistogram {g : ℕ} (base grammar : ℕ) (h : Fin g → ℕ) (m : Memory w) (a : ℕ) : Word w :=
  if ha : base+grammar ≤ a ∧ a < base+grammar+g then
    m a + word w (h ⟨a-(base+grammar), by omega⟩)
  else m a

theorem addHistogram_at {g : ℕ} (base grammar : ℕ) (h : Fin g → ℕ) (m : Memory w) (i : Fin g) :
    addHistogram base grammar h m (base+grammar+i) = m (base+grammar+i) + word w (h i) := by
  simp [addHistogram, i.isLt]

theorem addHistogram_outside {g : ℕ} (base grammar : ℕ) (h : Fin g → ℕ) (m : Memory w) (a : ℕ)
    (ha : a < base + grammar ∨ base + grammar + g ≤ a) : addHistogram base grammar h m a = m a := by
  have he : ¬ (base+grammar ≤ a ∧ a < base+grammar+g) := by omega
  simp [addHistogram, he]

private theorem range_eq_histogram {g : ℕ} (base grammar src : ℕ) (h : Fin g → ℕ)
    (priv : Word w → Word w) (hm : ∀ i : Fin g, priv (word w (src+i)) = word w (h i))
      (m : Memory w) :
    addRange src (base+grammar) g priv m = addHistogram base grammar h m := by
  funext a
  by_cases ha : base+grammar ≤ a ∧ a < base+grammar+g
  · let i : Fin g := ⟨a-(base+grammar),by omega⟩
    have he : base+grammar+i.val = a := by dsimp [i]; omega
    rw [← he, addHistogram_at]
    simp [addRange, i.isLt]
    simpa [word] using hm i
  · simp [addRange, addHistogram, ha]

/-- Native vertex flush with no new branches. The continuation receives
the combined histogram and all private state accumulated by the expansion. -/
theorem execute_vertex_events {g : ℕ} (hl : Linked M pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (base grammar src : ℕ) (h : Fin g → ℕ) (hpriv : ∀ i : Fin g, c.privateMem (word w (src+i)) =
      word w (h i))
    (hsrc : src+g < 2^w) (hdst : base+grammar+g < 2^w)
    (hr : c.reg (reg 0) = word w (base+grammar)) (he : c.reg (reg 1) = word w (base+grammar+g))
    (hs : c.reg (reg 2) = word w src) (ho : c.reg (reg 3) = 1) (m : Memory w) :
    ∃ out es, out.pc = done ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧
      es = events c.privateMem m src (base+grammar) g ∧
      es.length = 7*g+1 ∧ countProbes es = 2*g ∧ choiceBits es = [] ∧
      after m es = addHistogram base grammar h m ∧
      ∀ fuel bs, execute M.program (fuel+7*g+1) c m bs =
        (execute M.program fuel out (addHistogram base grammar h m) bs).map
          (fun rep ↦ ⟨es ++ rep.events, rep.result⟩) := by
  obtain ⟨out,hpc,hpersist,hmem,_,_,_,run⟩ :=
    execute_range hl c hc src (base+grammar) g hsrc hdst hr he hs ho m
  have cost := events_cost c.privateMem m src (base+grammar) g
  refine ⟨out,_,hpc,hmem,hpersist,rfl,cost.1,cost.2.1,cost.2.2,?_,?_⟩
  · rw [after_events _ _ _ _ _ hdst, range_eq_histogram base grammar src h _ hpriv m]
  simpa only [range_eq_histogram base grammar src h _ hpriv m] using run

theorem execute_vertex {g : ℕ} (hl : Linked M pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (base grammar src : ℕ) (h : Fin g → ℕ) (hpriv : ∀ i : Fin g, c.privateMem (word w (src+i)) =
      word w (h i))
    (hsrc : src+g < 2^w) (hdst : base+grammar+g < 2^w)
    (hr : c.reg (reg 0) = word w (base+grammar)) (he : c.reg (reg 1) = word w (base+grammar+g))
    (hs : c.reg (reg 2) = word w src) (ho : c.reg (reg 3) = 1) (m : Memory w) :
    ∃ out es, out.pc = done ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧
      es.length = 7*g+1 ∧ countProbes es = 2*g ∧ choiceBits es = [] ∧
      after m es = addHistogram base grammar h m ∧
      ∀ fuel bs, execute M.program (fuel+7*g+1) c m bs =
        (execute M.program fuel out (addHistogram base grammar h m) bs).map
          (fun rep ↦ ⟨es ++ rep.events, rep.result⟩) := by
  obtain ⟨out, es, pc, mem, state, _, rest⟩ :=
    execute_vertex_events hl c hc base grammar src h hpriv hsrc hdst hr he hs ho m
  exact ⟨out, es, pc, mem, state, rest⟩

/-- Entry code from a vertex continuation. Its four parameter words give
the shared base, production count, gadget count, and private histogram base.
The total width is part of the fixed problem's parameters. -/
def entryCode (atPC : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (param : Fin 4 → Fin k)
    (loop : Fin p) : Fin 7 → Instr w p r k :=
  ![.publicWord (reg 0) (param 0) (atPC 1), .publicWord (reg 4) (param 1) (atPC 2),
    .binary .add (reg 0) (reg 0) (reg 4) (atPC 3), .publicWord (reg 1) (param 2) (atPC 4),
    .binary .add (reg 1) (reg 0) (reg 1) (atPC 5), .publicWord (reg 2) (param 3) (atPC 6),
    .constant (reg 3) 1 loop]

/-- The full flush starts at its first public-word instruction. Every
register may hold arbitrary data left by the preceding vertex expansion.
The parameter loads cost seven local steps once for the whole suffix. -/
theorem execute_flush {g : ℕ} (hl : Linked M pc reg done) (atPC : Fin 7 → Fin p) (param : Fin 4
    → Fin k)
    (hcode : ∀ i, M.code (atPC i) = entryCode atPC reg param (pc 0) i)
    (c : Config w p r) (hc : c.pc = atPC 0) (base grammar src : ℕ)
    (hbase : M.publicData (param 0) = word w base) (hgrammar : M.publicData (param 1) =
      word w grammar)
    (hg : M.publicData (param 2) = word w g) (hprivate : M.publicData (param 3) = word w src)
    (h : Fin g → ℕ) (hpriv : ∀ i : Fin g, c.privateMem (word w (src+i)) = word w (h i))
    (hsrc : src+g < 2^w) (hdst : base+grammar+g < 2^w) (m : Memory w) :
    ∃ out es, out.pc = done ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧
      es.length = 7*g+8 ∧ countProbes es = 2*g ∧ choiceBits es = [] ∧
      after m es = addHistogram base grammar h m ∧
      ∀ fuel bs, execute M.program (fuel+7*g+8) c m bs =
        (execute M.program fuel out (addHistogram base grammar h m) bs).map
          (fun rep ↦ ⟨es ++ rep.events, rep.result⟩) := by
  have step (i : Fin 7) (d : Config w p r) (hp : d.pc = atPC i) :
      M.program.step d = (entryCode atPC reg param (pc 0) i).run M.publicData d := by
    simp [Machine.program, hp, hcode i]
  let c1 := c.put (atPC 1) (reg 0) (M.publicData (param 0))
  let c2 := c1.put (atPC 2) (reg 4) (M.publicData (param 1))
  let c3 := c2.put (atPC 3) (reg 0) (c2.reg (reg 0)+c2.reg (reg 4))
  let c4 := c3.put (atPC 4) (reg 1) (M.publicData (param 2))
  let c5 := c4.put (atPC 5) (reg 1) (c4.reg (reg 0)+c4.reg (reg 1))
  let c6 := c5.put (atPC 6) (reg 2) (M.publicData (param 3))
  let start := c6.put (pc 0) (reg 3) 1
  let ticks : List (Event w) := [.tick,.tick,.tick,.tick,.tick,.tick,.tick]
  have pre : PrimedCounter.GuessWord.Prefix M c ticks start :=
    .tick (step 0 c hc) (.tick (step 1 c1 rfl) (.tick (step 2 c2 rfl) (.tick (step 3 c3 rfl)
      (.tick (step 4 c4 rfl) (.tick (step 5 c5 rfl) (.tick (step 6 c6 rfl) (.nil start)))))))
  have hr : start.reg (reg 0) = word w (base+grammar) := by
    simp [start, c6, c5, c4, c3, c2, c1, Config.put, hbase, hgrammar, word]
  have he : start.reg (reg 1) = word w (base+grammar+g) := by
    simp [start, c6, c5, c4, c3, c2, c1, Config.put, hbase, hgrammar, hg, word]
  have hs : start.reg (reg 2) = word w src := by simp [start, c6, Config.put, hprivate]
  obtain ⟨out,es,ho,hm,hp,hlen,hpr,hb,ha,hex⟩ := execute_vertex hl start rfl base grammar src h
    hpriv hsrc hdst hr he hs (by simp [start]) m
  refine ⟨out,ticks++es,ho,hm,hp,by simp [ticks, hlen],hpr,hb,ha,?_⟩
  intro fuel bs
  have pref := pre.execute (fuel+7*g+1) m bs
  change execute M.program (fuel+7*g+1+7) c m bs = _ at pref
  rw [show fuel+7*g+8 = fuel+7*g+1+7 by omega, pref, hex]
  simp [Option.map_map, Function.comp_def, ticks]

private def entryPC (i : Fin 7) : Fin 15 := ⟨i.val,by omega⟩
private def loopPC (i : Fin 7) : Fin 15 := ⟨7+i.val,by omega⟩

/-- Fixed finite table for the complete flush with an accepting exit. The
linked version can replace the exit with the caller's next instruction. -/
def template : Template 15 6 4 where
  entry := entryPC 0
  literalWidth := 1
  code j := if hj : j.val < 7 then
      entryCode entryPC (Function.Embedding.refl _) id (loopPC 0) ⟨j.val,hj⟩
    else if hj' : j.val < 14 then
      instruction loopPC (Function.Embedding.refl _) 14 ⟨j.val-7,by omega⟩
    else .accept

/-- Concrete instantiation at an arbitrary word width and a vertex's actual
private memory. The deterministic halt includes the final instruction. -/
theorem template_execute {g : ℕ} (base grammar src : ℕ) (h : Fin g → ℕ)
    (c : Config w 15 6) (hc : c.pc = template.entry)
    (hpriv : ∀ i : Fin g, c.privateMem (word w (src+i)) = word w (h i))
    (hsrc : src+g < 2^w) (hdst : base+grammar+g < 2^w) (m : Memory w) :
    let data := ![word w base, word w grammar, word w g, word w src]
    let T := template.instantiate w data
    ∃ es, execute T.program (7*g+9) c m [] = some ⟨es,none⟩ ∧
      es.length = 7*g+8 ∧ countProbes es = 2*g ∧ choiceBits es = [] ∧
      after m es = addHistogram base grammar h m := by
  let data := ![word w base, word w grammar, word w g, word w src]
  let T := template.instantiate w data
  have hl : Linked T loopPC (Function.Embedding.refl _) 14 := by intro i; fin_cases i <;> rfl
  have hentry (i : Fin 7) : T.code (entryPC i) =
      entryCode entryPC (Function.Embedding.refl _) id (loopPC 0) i := by fin_cases i <;> rfl
  obtain ⟨out,es,ho,_,_,hlen,hp,hb,hm,run⟩ := execute_flush hl entryPC id hentry c hc
    base grammar src rfl rfl rfl rfl h hpriv hsrc hdst m
  refine ⟨es,?_,hlen,hp,hb,hm⟩
  change execute T.program (7*g+9) c m [] = _
  have hs : T.program.step out = .finish none := by
    change (T.code out.pc).run T.publicData out = _
    rw [ho]
    rfl
  rw [show 7*g+9 = 1+7*g+8 by omega, run 1 [], execute, hs]
  simp

/-- Fold the effects of the per-vertex continuations in visit order. -/
def visit {V : Type*} {g : ℕ} (base grammar : ℕ) (h : V → Fin g → ℕ) (vs : List V) (m : Memory w) :=
  vs.foldl (fun acc v ↦ addHistogram base grammar (h v) acc) m

theorem visit_at {V : Type*} {g : ℕ} (base grammar : ℕ) (h : V → Fin g → ℕ) (vs : List V)
    (m : Memory w) (i : Fin g) :
    visit base grammar h vs m (base+grammar+i) =
      m (base+grammar+i) + word w ((vs.map fun v ↦ h v i).sum) := by
  induction vs generalizing m with
  | nil => simp [visit, word]
  | cons v vs ih =>
    change visit base grammar h vs (addHistogram base grammar (h v) m) _ = _
    rw [ih, addHistogram_at]
    simp [word, add_assoc]

theorem visit_outside {V : Type*} {g : ℕ} (base grammar : ℕ) (h : V → Fin g → ℕ) (vs : List V)
    (m : Memory w) (a : ℕ) (ha : a < base + grammar ∨ base + grammar + g ≤ a) :
    visit base grammar h vs m a = m a := by
  induction vs generalizing m with
  | nil => rfl
  | cons v vs ih =>
    change visit base grammar h vs (addHistogram base grammar (h v) m) a = _
    rw [ih, addHistogram_outside _ _ _ _ _ ha]

/-- The production nomination at every prefix address survives all vertex bursts. -/
theorem nomination_preserved {V : Type*} {g : ℕ} (base grammar : ℕ) (h : V → Fin g → ℕ)
    (vs : List V) (m : Memory w) (i : Fin grammar) :
    visit base grammar h vs m (base+i) = m (base+i) :=
  visit_outside _ _ _ _ _ _ (Or.inl (Nat.add_lt_add_left i.isLt base))

/-- Any prefix of the selected visit order has exact natural-valued counters.
Bounding the total by R² bounds every intermediate coordinate by the same
2r-bit capacity, independently of the order of the visits. -/
theorem prefix_fits {V : Type*} {g r' : ℕ} (base grammar : ℕ) (h : V → Fin g → ℕ)
    (first rest : List V) (m : Memory w) (i : Fin g) (hz : m (base + grammar + i) = 0)
    (hw : 2 * r' ≤ w) (bound : ((first ++ rest).map fun v ↦ h v i).sum < (2 ^ r') ^ 2) :
    (visit base grammar h first m (base+grammar+i)).val = (first.map fun v ↦ h v i).sum ∧
      (visit base grammar h first m (base+grammar+i)).val < 2^(2*r') := by
  rw [List.map_append, List.sum_append, ← pow_mul, Nat.mul_comm r' 2] at bound
  have hsum : (first.map fun v ↦ h v i).sum < 2^(2*r') := by omega
  have hfit := hsum.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hw)
  rw [visit_at, hz, zero_add, val_word hfit]
  exact ⟨rfl, hsum⟩

open NetworkKernel

/-- At a vertex the old stored word plus the current natural increment is
the next word's natural value. It is at most the total and fits in 2r bits. -/
theorem component_no_overflow {V : Type*} {g r' : ℕ} (base grammar : ℕ) (h : V → Fin g → ℕ)
    (first rest : List V) (v : V) (m : Memory w) (i : Fin g) (hz : m (base + grammar + i) = 0)
    (hw : 2 * r' ≤ w) (bound : ((first ++ v::rest).map fun u ↦ h u i).sum < (2 ^ r') ^ 2) :
    let old := visit base grammar h first m (base+grammar+i)
    let new := visit base grammar h (first++[v]) m (base+grammar+i)
    new.val = old.val + h v i ∧ new.val ≤ ((first ++ v::rest).map fun u ↦ h u i).sum ∧
      new.val < 2^(2*r') := by
  dsimp only
  have hpre := prefix_fits base grammar h first (v::rest) m i hz hw bound
  have hnext := prefix_fits base grammar h (first++[v]) rest m i hz hw
    (by simpa only [List.append_assoc,
    List.cons_append, List.nil_append] using bound)
  rw [hpre.1, hnext.1]
  refine ⟨?_, ?_, hnext.1 ▸ hnext.2⟩ <;> simp [List.map_append, List.sum_append]

/-- Lemma 10.1 initializes every gadget counter to zero when the suffix
starts beyond the prescribed header addresses. -/
theorem initial_suffix_zero {g : ℕ} (S base grammar : ℕ) (header : ℕ → Word w)
    (hseparate : S ≤ base + grammar) (i : Fin g) :
    RAMMemory.initialMemory S header (base+grammar+i) = 0 := by
  simp [RAMMemory.initialMemory, show ¬ base+grammar+i < S by omega]

section History

open LocalHistory

variable {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}

/-- Final-vertex private histograms in the actual descriptor's visit order.
A selector descends only into its selected term, whose witnesses already
include the local maps and all the children placed at that site. -/
noncomputable def vertexHistograms {N : Network} (H : History A N) (K : H.KernelWitnesses κ)
    (desc : Readers H K) (F : Factors A N) (W : ∀ v z, MonomialWitness κ (F v z))
    (p : (H.expandedWitness K F W).Choice) : List (Label → ℕ) := by
  induction H with
  | @stop N =>
    let q := History.stopChoice K F W p
    exact List.ofFn (fun i ↦ (W (desc.2.1.entries i)
      (WireTensor.edgeAssignment N.src N.dst q.1 (desc.2.1.entries i))).exponents (q.2
        (desc.2.1.entries i)))
  | branch s tail ih =>
    let q := History.branchChoice s tail K F W p
    exact ih q.1 (K.2 q.1) (desc.2.2.2.2 q.1) ((s.term q.1).push F)
      ((s.term q.1).pushWitness F W (K.1 q.1)) q.2

/-- Summing the completed private histograms gives the formal monomial
exponent of the selected occurrence, including syntactically nonzero
monomials whose evaluated scalar may vanish. -/
theorem vertexHistograms_sum {N : Network} (H : History A N) (K : H.KernelWitnesses κ)
    (desc : Readers H K) (F : Factors A N) (W : ∀ v z, MonomialWitness κ (F v z))
    (p : (H.expandedWitness K F W).Choice) (l : Label) :
    ((vertexHistograms H K desc F W p).map fun h ↦ h l).sum = (H.expandedWitness K F W).exponents
      p l := by
  induction H with
  | @stop N =>
    obtain ⟨⟨z,x⟩,rfl⟩ := (History.stopChoice K F W).symm.surjective p
    rw [vertexHistograms, List.map_ofFn, List.sum_ofFn, History.stopChoice_exponents]
    exact desc.2.1.entries.sum_comp (fun v ↦ (W v (WireTensor.edgeAssignment N.src N.dst z
      v)).exponents (x v) l)
  | branch s tail ih =>
    obtain ⟨⟨i,q⟩,rfl⟩ := (History.branchChoice s tail K F W).symm.surjective p
    rw [vertexHistograms, History.branchChoice_exponents]
    exact ih i _ _ _ _ q

/-- The physical suffix and the formal ν(e) agree for every selected
history. A bound on *total* degree gives exact readback of every coordinate
in the 2r-bit output convention. -/
theorem history_readback {N : Network} (H : History A N) (K : H.KernelWitnesses κ)
    (desc : Readers H K) (F : Factors A N) (W : ∀ v z, MonomialWitness κ (F v z))
    (p : (H.expandedWitness K F W).Choice) {g : ℕ} (labels : Fin g ≃ Label) (base grammar r' : ℕ)
    (m : Memory w) (hz : ∀ i : Fin g, m (base+grammar+i) = 0) (hw : 2*r' ≤ w)
    (bound : (∑ l, (H.expandedWitness K F W).exponents p l) < (2^r')^2) (i : Fin g) :
    (visit base grammar (fun (h : Label → ℕ) j ↦ h (labels j))
      (vertexHistograms H K desc F W p) m (base+grammar+i)).val =
        (H.expandedWitness K F W).exponents p (labels i) := by
  have hsum := vertexHistograms_sum H K desc F W p (labels i)
  have coord := Finset.single_le_sum (s := Finset.univ)
    (fun (l : Label) _ ↦ Nat.zero_le ((H.expandedWitness K F W).exponents p l)) (Finset.mem_univ
      (labels i))
  refine (prefix_fits base grammar (fun (h : Label → ℕ) j ↦ h (labels j))
    (vertexHistograms H K desc F W p) [] m i (hz i) hw ?_).1.trans hsum
  rw [List.append_nil, hsum]
  exact coord.trans_lt bound

/-- Readback in the live exponent routine's single contiguous array. Its
first coordinates are the already nominated µ words and the remaining
coordinates are exactly ν(e) for the chosen compression occurrence. -/
theorem live_array_readback {N : Network} (H : History A N) (K : H.KernelWitnesses κ)
    (desc : Readers H K) (F : Factors A N) (W : ∀ v z, MonomialWitness κ (F v z))
    (p : (H.expandedWitness K F W).Choice) {g grammar r' : ℕ} (labels : Fin g ≃ Label)
      (base : Word w)
    (fit : base.val + grammar ≤ 2 ^ w) (μ : Fin grammar → Word (2 * r')) (m : Memory w)
    (hz : ∀ i : Fin g, m (base.val+grammar+i) = 0) (hw : 2*r' ≤ w)
    (bound : (∑ l, (H.expandedWitness K F W).exponents p l) < (2^r')^2) (j : Fin (grammar+g)) :
    let initial := LiveNominations.stored base fit μ m
    let final := visit base.val grammar (fun (h : Label → ℕ) i ↦ h (labels i))
      (vertexHistograms H K desc F W p) initial
    (final (base.val+j)).val = Fin.addCases (fun i ↦ (μ i).val)
      (fun i ↦ (H.expandedWitness K F W).exponents p (labels i)) j := by
  dsimp only
  cases j using Fin.addCases with
  | left i =>
    rw [Fin.addCases_left]
    change (visit _ _ _ _ _ (base.val+i.val)).val = _
    rw [nomination_preserved, LiveNominations.stored_at, Fin.val_ofNat,
      Nat.mod_eq_of_lt ((μ i).isLt.trans_le (Nat.pow_le_pow_right (by decide) hw))]
  | right i =>
    rw [Fin.addCases_right]
    change (visit _ _ _ _ _ (base.val+(grammar+i.val))).val = _
    rw [← Nat.add_assoc]
    apply history_readback H K desc F W p labels base.val grammar r' _ _ hw bound i
    intro l
    rw [LiveNominations.stored_outside _ _ _ _ _ (Or.inr (by omega)), hz]

end History

end PairSimulation.Counters

end VPVNP
end Computability
end OAI
