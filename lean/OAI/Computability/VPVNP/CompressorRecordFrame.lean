import OAI.Computability.VPVNP.LiveStageLinkRun
import Mathlib.Data.ZMod.Defs

/-!
# Loading a descriptor frame into native registers

The compressor's component templates have finite parameter banks. At call
entry a fixed prelude reads the bank from consecutive external words. The
relocated body executes each original public-word instruction as a register
copy, so repeated accesses to a parameter inside a long private computation
require no additional probes. The bank is a snapshot taken before the body.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Frame

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {p r k w : ℕ}

/-- Program-counter count for the frame-loading prelude and relocated body, with four
instructions per parameter. -/
abbrev PCs (p k : ℕ) := k*4+p
/-- Register count for the framed body, its parameter cache, and the temporary frame-address
register. -/
abbrev Regs (r k : ℕ) := r+(k+1)

/-- Four prelude labels per frame word and one label for each original instruction. -/
def labels (p k : ℕ) : (Fin k × Fin 4) ⊕ Fin p ≃ Fin (PCs p k) :=
  (finProdFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv

/-- Program counter for a specified parameter and one of its four loading instructions. -/
def prePC (p : ℕ) (j : Fin k) (phase : Fin 4) := labels p k (.inl (j,phase))
/-- Relocated program counter of an original body instruction, following the frame-loading
prelude. -/
def bodyPC (k : ℕ) (i : Fin p) := labels p k (.inr i)

/-- Embed a body register into the leading bank of the framed machine. -/
def ordinary (k : ℕ) (i : Fin r) : Fin (Regs r k) := i.castAdd (k+1)
/-- Cache register holding the selected public parameter throughout the body execution. -/
def cacheReg (r : ℕ) (j : Fin k) : Fin (Regs r k) := j.castSucc.natAdd r
/-- Temporary register used to address external parameter words during frame loading. -/
def addressReg (r k : ℕ) : Fin (Regs r k) := (Fin.last k).natAdd r

/-- Public-word instructions are the only instructions whose operation
changes. Component destinations never address a cached parameter. -/
def bodyCode : Instr w p r k → Instr w (PCs p k) (Regs r k) 1
  | .constant a v j => .constant (ordinary k a) v (bodyPC k j)
  | .publicWord a i j => .copy (ordinary k a) (cacheReg r i) (bodyPC k j)
  | .stateWord a j => .stateWord (ordinary k a) (bodyPC k j)
  | .copy a b j => .copy (ordinary k a) (ordinary k b) (bodyPC k j)
  | .binary op a b c j => .binary op (ordinary k a) (ordinary k b) (ordinary k c) (bodyPC k j)
  | .loadPrivate a b j => .loadPrivate (ordinary k a) (ordinary k b) (bodyPC k j)
  | .storePrivate a b j => .storePrivate (ordinary k a) (ordinary k b) (bodyPC k j)
  | .jumpEq a b y n => .jumpEq (ordinary k a) (ordinary k b) (bodyPC k y) (bodyPC k n)
  | .jumpLt a b y n => .jumpLt (ordinary k a) (ordinary k b) (bodyPC k y) (bodyPC k n)
  | .choose y n => .choose (bodyPC k y) (bodyPC k n)
  | .readExternal a b j => .readExternal (ordinary k a) (ordinary k b) (bodyPC k j)
  | .writeExternal a b j => .writeExternal (ordinary k a) (ordinary k b) (bodyPC k j)
  | .returnState a => .returnState (ordinary k a)
  | .accept => .accept
  | .reject => .reject

/-- Reading a cached parameter costs the same private word work as the
original public-word access; all other body instructions keep their charge. -/
@[simp] theorem bodyCode_wordWork (op : Instr w p r k) : (bodyCode op).wordWork = op.wordWork := by
  cases op <;> rfl

variable (T : Template p r k)

/-- Enter the next parameter's loading sequence, or the body entry once the entire frame is
cached. -/
def nextPC (j : ℕ) : Fin (PCs p k) :=
  if hj : j < k then prePC p ⟨j,hj⟩ 0 else bodyPC k T.entry

private def literalWidth := max T.literalWidth (Nat.clog 2 k)

private def code : (Fin k × Fin 4) ⊕ Fin p → Instr (literalWidth T) (PCs p k) (Regs r k) 1
  | .inl (j,0) => .publicWord (addressReg r k) 0 (prePC p j 1)
  | .inl (j,1) => .constant (cacheReg r j) (Fin.ofNat _ j.val) (prePC p j 2)
  | .inl (j,2) => .binary .add (cacheReg r j) (addressReg r k) (cacheReg r j) (prePC p j 3)
  | .inl (j,3) => .readExternal (cacheReg r j) (cacheReg r j) (nextPC T (j.val+1))
  | .inr j => bodyCode ((T.code j).resize _)

/-- A single fixed compiled template whose sole public word is the
address of the descriptor frame. An empty bank needs no prelude. -/
def compile : Template (PCs p k) (Regs r k) 1 where
  literalWidth := literalWidth T
  entry := nextPC T 0
  code i := code T ((labels p k).symm i)

/-- Instantiate the compiled framed template with the external frame base as its public
operand. -/
def machine (base : Word w) := (compile T).instantiate w (fun _ ↦ base)

private theorem literal_fits (j : Fin k) : j.val < 2^literalWidth T :=
  j.isLt.trans_le ((Nat.le_pow_clog (by decide : 1 < 2) k).trans
    (Nat.pow_le_pow_right (by decide) (le_max_right ..)))

private theorem code_0 (base : Word w) (j : Fin k) :
    (machine T base).code (prePC p j 0) = .publicWord (addressReg r k) 0 (prePC p j 1) := by
  simp [machine, compile, Template.instantiate, prePC, code, Instr.resize]

private theorem code_1 (base : Word w) (j : Fin k) :
    (machine T base).code (prePC p j 1) = .constant (cacheReg r j) (j.val : Word w)
      (prePC p j 2) := by
  simp [machine, compile, Template.instantiate, prePC, code, Instr.resize, Nat.mod_eq_of_lt
    (literal_fits T j)]

private theorem code_2 (base : Word w) (j : Fin k) :
    (machine T base).code (prePC p j 2) =
      .binary .add (cacheReg r j) (addressReg r k) (cacheReg r j) (prePC p j 3) := by
  simp [machine, compile, Template.instantiate, prePC, code, Instr.resize]

private theorem code_3 (base : Word w) (j : Fin k) :
    (machine T base).code (prePC p j 3) =
      .readExternal (cacheReg r j) (cacheReg r j) (nextPC T (j.val+1)) := by
  simp [machine, compile, Template.instantiate, prePC, code, Instr.resize]

/-- The private dispatch charges of the four prelude instructions total
seventeen elementary word operations per parameter. -/
theorem load_wordWork (base : Word w) (j : Fin k) :
    ((machine T base).code (prePC p j 0)).wordWork +
    ((machine T base).code (prePC p j 1)).wordWork +
    ((machine T base).code (prePC p j 2)).wordWork +
    ((machine T base).code (prePC p j 3)).wordWork = 17 := by
  rw [code_0, code_1, code_2, code_3]
  rfl

theorem code_body (base : Word w) (j : Fin p) :
    (machine T base).code (bodyPC k j) = bodyCode ((T.code j).resize w) := by
  simp only [machine, compile, Template.instantiate, bodyPC, Equiv.symm_apply_apply, code]
  have h (v : Word T.literalWidth) : v.val < 2^literalWidth T :=
    v.isLt.trans_le (Nat.pow_le_pow_right (by decide) (le_max_left ..))
  generalize T.code j = op
  cases op <;> simp [Instr.resize, bodyCode, Nat.mod_eq_of_lt (h _)]

private def registers (small : Fin r → Word w) (cache : Fin k → Word w) (addr : Word w) :
    Fin (Regs r k) → Word w := Fin.append small (Fin.snoc cache addr)

private theorem update_left {m n : ℕ} {α : Type*} (f : Fin m → α) (g : Fin n → α) (i : Fin m)
    (v : α) :
    Function.update (Fin.append f g) (i.castAdd n) v = Fin.append (Function.update f i v) g := by
  funext t
  cases t using Fin.addCases with
  | left j => by_cases hj : j = i <;> simp [Function.update, hj]
  | right j =>
    have h : j.natAdd m ≠ i.castAdd n := fun e ↦ by have := congrArg Fin.val e; simp at this; omega
    simp [Function.update_of_ne h]

private theorem update_right {m n : ℕ} {α : Type*} (f : Fin m → α) (g : Fin n → α) (i : Fin n)
    (v : α) :
    Function.update (Fin.append f g) (i.natAdd m) v = Fin.append f (Function.update g i v) := by
  funext t
  cases t using Fin.addCases with
  | left j =>
    have h : j.castAdd n ≠ i.natAdd m := fun e ↦ by have := congrArg Fin.val e; simp at this; omega
    simp [Function.update_of_ne h]
  | right j => by_cases hj : j = i <;> simp [Function.update, hj]

private theorem update_cache (f : Fin r → Word w) (cache : Fin k → Word w) (addr : Word w)
    (i : Fin k) (v : Word w) :
    Function.update (registers f cache addr) (cacheReg r i) v = registers f
      (Function.update cache i v) addr := by
  unfold registers cacheReg
  rw [update_right]
  congr 1
  funext t
  cases t using Fin.lastCases with
  | last => simp [Function.update_of_ne (Fin.castSucc_ne_last i).symm]
  | cast j => by_cases h : j = i <;> simp [Function.update, h]

private theorem update_addr (f : Fin r → Word w) (cache : Fin k → Word w) (addr v : Word w) :
    Function.update (registers f cache addr) (addressReg r k) v = registers f cache v := by
  unfold registers addressReg
  rw [update_right]
  congr 1
  funext t
  cases t using Fin.lastCases with
  | last => simp
  | cast j => simp

private def embed (cache : Fin k → Word w) (addr : Word w) (c : Config w p r) : Config w (PCs p k)
    (Regs r k) :=
  ⟨bodyPC k c.pc, c.persistent, registers c.reg cache addr, c.privateMem⟩

private def mapAction {C D : Type*} (f : C → D) : CallAction w C → CallAction w D
  | .localStep c => .localStep (f c)
  | .branch g => .branch (f ∘ g)
  | .read a g => .read a (f ∘ g)
  | .write a v c => .write a v (f c)
  | .finish s => .finish s
  | .reject => .reject

private theorem body_step (base addr : Word w) (pub : Fin k → Word w) (c : Config w p r) :
    (machine T base).program.step (embed pub addr c) =
      mapAction (embed pub addr) ((T.instantiate w pub).program.step c) := by
  change ((machine T base).code (bodyPC k c.pc)).run _ _ = mapAction _
    (((T.code c.pc).resize w).run pub c)
  rw [code_body]
  generalize (T.code c.pc).resize w = op
  cases op <;> simp only [bodyCode, Instr.run, embed, mapAction, Config.put, Config.store,
    registers,
    ordinary, cacheReg, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, update_left,
      Function.comp_def]
  all_goals first | rfl | (split <;> rfl) | (congr 1; funext b; cases b <;> rfl)

/-- Within the relocated body, every finite-fuel execution is exactly the
original execution with its cached public data. This includes arbitrary
external writes (even to the frame), adaptive reads, and all choices. -/
theorem execute_body (base addr : Word w) (pub : Fin k → Word w) (fuel : ℕ) (c : Config w p r)
    (m : Memory w) (bs : List Bool) :
    execute (machine T base).program fuel (embed pub addr c) m bs =
      execute (T.instantiate w pub).program fuel c m bs := by
  induction fuel generalizing c m bs with
  | zero => rfl
  | succ fuel ih =>
    rw [execute, body_step, execute]
    cases hs : (T.instantiate w pub).program.step c <;> simp only [mapAction, Function.comp_apply]
    all_goals first | rfl | rw [ih] | (cases bs <;> simp [ih])

/-- The source machine's public bank is the external frame at call entry. -/
def data (base : Word w) (m : Memory w) : Fin k → Word w :=
  fun j ↦ m (base + (j.val : Word w)).val

theorem data_at (base : Word w) (m : Memory w) (fit : base.val + k ≤ 2 ^ w) (j : Fin k) :
    data base m j = m (base.val+j.val) := by
  have hj := (Nat.add_lt_add_left j.isLt base.val).trans_le fit
  have hv : ((j.val : Word w) : ℕ) = j.val := Nat.mod_eq_of_lt (by omega)
  have hsum : base.val + (j.val : Word w).val < 2^w := by simpa only [hv] using hj
  rw [data, Fin.val_add_eq_of_add_lt hsum, hv]

private def chunk (base : Word w) (m : Memory w) (j : ℕ) : List (Event w) :=
  let a := base + (j : Word w)
  [.tick,.tick,.tick,.read a (m a.val)]

/-- Chronological trace of the descriptor-frame loads starting at offset j. -/
def loadEvents (base : Word w) (m : Memory w) (j : ℕ) : ℕ → List (Event w)
  | 0 => []
  | n+1 => chunk base m j ++ loadEvents base m (j+1) n

/-- Each frame parameter adds one probe and three private ticks. The
continuation's report retains every branch bit and memory update. -/
theorem frame_cost (base : Word w) (m : Memory w) (j n : ℕ) (rep : Report w) :
    let out := LiveStageLink.prependLog (loadEvents base m j n) rep
    out.events.length = 4*n+rep.events.length ∧ out.probes = n+rep.probes ∧
      choiceBits out.events = choiceBits rep.events ∧ after m out.events = after m rep.events ∧
      out.result = rep.result := by
  induction n generalizing j with
  | zero => simp [LiveStageLink.prependLog, loadEvents]
  | succ n ih =>
    obtain ⟨hl,hp,hb,hm,hr⟩ := ih (j+1)
    dsimp only [LiveStageLink.prependLog] at *
    simp only [loadEvents, chunk, List.cons_append, List.nil_append, List.length_cons,
      Report.probes, countProbes, choiceBits] at *
    exact ⟨by omega, by omega, hb, hm, hr⟩

private def control (atPC : Fin (PCs p k)) (c : Config w p r) (bank : Fin k → Word w)
    (addr : Word w) :
    Config w (PCs p k) (Regs r k) := ⟨atPC,c.persistent,registers c.reg bank addr,c.privateMem⟩

private theorem exec_tick {P : Program w (Config w (PCs p k) (Regs r k))}
    {c c' : Config w (PCs p k) (Regs r k)} (hs : P.step c = .localStep c') (f : ℕ)
    (m : Memory w) (bs : List Bool) : execute P (f+1) c m bs =
      (execute P f c' m bs).map (Report.prepend .tick) := by simp only [execute, hs]

private theorem exec_read {P : Program w (Config w (PCs p k) (Regs r k))}
    {c : Config w (PCs p k) (Regs r k)} {a : Word w} {g : Word w → Config w (PCs p k) (Regs r k)}
    (hs : P.step c = .read a g) (f : ℕ) (m : Memory w) (bs : List Bool) :
    execute P (f+1) c m bs = (execute P f (g (m a.val)) m bs).map (Report.prepend (.read a
      (m a.val))) := by
  simp only [execute, hs]

private theorem execute_load (base addr : Word w) (m : Memory w) (bs : List Bool) (j : Fin k)
    (c : Config w p r) (bank : Fin k → Word w) (f : ℕ) :
    execute (machine T base).program (f+4) (control (nextPC T j.val) c bank addr) m bs =
      (execute (machine T base).program f (control (nextPC T (j.val+1)) c
        (Function.update bank j (data base m j)) base) m bs).map (LiveStageLink.prependLog
          (chunk base m j)) := by
  let L := (machine T base).program
  let a := base + (j.val : Word w)
  let c0 := control (nextPC T j.val) c bank addr
  let c1 := control (prePC p j 1) c bank base
  let c2 := control (prePC p j 2) c (Function.update bank j (j.val : Word w)) base
  let c3 := control (prePC p j 3) c (Function.update bank j a) base
  let next (v : Word w) := control (nextPC T (j.val+1)) c (Function.update bank j v) base
  have s0 : L.step c0 = .localStep c1 := by
    change ((machine T base).code (nextPC T j.val)).run _ c0 = _
    simp only [nextPC, j.isLt, ↓reduceDIte, code_0, Instr.run]
    change CallAction.localStep (c0.put _ (addressReg r k) base) = _
    simp [c0, c1, control, Config.put, update_addr]
  have s1 : L.step c1 = .localStep c2 := by
    change ((machine T base).code (prePC p j 1)).run _ c1 = _
    rw [code_1]
    simp [Instr.run, c1, c2, control, Config.put, update_cache]
  have s2 : L.step c2 = .localStep c3 := by
    change ((machine T base).code (prePC p j 2)).run _ c2 = _
    rw [code_2]
    have haddr : c2.reg (addressReg r k) = base := by simp only [c2, control, registers,
      addressReg, Fin.append_right, Fin.snoc_last]
    have hi : c2.reg (cacheReg r j) = (j.val : Word w) := by simp [c2, control, registers, cacheReg]
    change CallAction.localStep (c2.put _ (cacheReg r j) (c2.reg (addressReg r k) + c2.reg
      (cacheReg r j))) = _
    rw [haddr, hi]
    simp [c2, c3, control, Config.put, update_cache, Function.update_idem, a]
  have s3 : L.step c3 = .read a next := by
    change ((machine T base).code (prePC p j 3)).run _ c3 = _
    rw [code_3]
    have haddr : c3.reg (cacheReg r j) = a := by simp [c3, control, registers, cacheReg]
    change CallAction.read (c3.reg (cacheReg r j)) _ = _
    rw [haddr]
    congr 1
    funext v
    simp [c3, next, control, Config.put, update_cache, Function.update_idem]
  rw [exec_tick s0, exec_tick s1, exec_tick s2, exec_read s3]
  simp [Report.prepend, Option.map_map, Function.comp_def, chunk, next, a, data]
  rfl

private def partialBank (pub : Fin k → Word w) (j : ℕ) : Fin k → Word w :=
  fun i ↦ if i.val < j then pub i else 0

private theorem update_partial (pub : Fin k → Word w) (j : Fin k) :
    Function.update (partialBank pub j.val) j (pub j) = partialBank pub (j.val+1) := by
  funext i
  by_cases h : i = j
  · subst i; simp [partialBank]
  · have hv : i.val ≠ j.val := fun e ↦ h (Fin.ext e)
    simp [Function.update_of_ne h, partialBank, show i.val < j.val+1 ↔ i.val < j.val by omega]

private theorem execute_remaining (base addr : Word w) (m : Memory w) (bs : List Bool)
    (c : Config w p r) (hc : c.pc = T.entry) (f j n : ℕ) (hlen : j + n = k) :
    execute (machine T base).program (f+4*n)
        (control (nextPC T j) c (partialBank (data base m) j) addr) m bs =
      (execute (T.instantiate w (data base m)).program f c m bs).map
        (LiveStageLink.prependLog (loadEvents base m j n)) := by
  induction n generalizing j addr with
  | zero =>
    have hj : j = k := by simpa using hlen
    subst j
    have full : partialBank (data base m) k = (data base m : Fin k → Word w) := by
      funext i; simp [partialBank, i.isLt]
    simp only [Nat.mul_zero, Nat.add_zero, full, nextPC, lt_self_iff_false, ↓reduceDIte, loadEvents]
    rw [← hc]
    change execute _ f (embed (data base m) addr c) m bs = _
    rw [execute_body]
    cases execute (T.instantiate w (data base m)).program f c m bs <;> rfl
  | succ n ih =>
    let i : Fin k := ⟨j,by omega⟩
    rw [show f+4*(n+1) = (f+4*n)+4 by omega, execute_load T base addr m bs i,
      update_partial (data base m) i, ih base (j+1) (by omega)]
    simp [loadEvents, LiveStageLink.prependLog, Option.map_map, Function.comp_def, i]
    rfl

/-- Exact native execution from fresh call entry for every component fuel
and branch stream. The original persistent input is passed through the
prelude. Subsequent calls take a new snapshot of their current frame. -/
theorem execute_frame (base : Word w) (state : Word w) (f : ℕ) (m : Memory w) (bs : List Bool) :
    let P := (machine T base).program
    let Q := (T.instantiate w (data base m)).program
    execute P (f+4*k) (P.start state) m bs =
      (execute Q f (Q.start state) m bs).map (LiveStageLink.prependLog
        (loadEvents base m 0 k)) := by
  let Q := (T.instantiate w (data base m)).program
  have hs : (machine T base).program.start state =
      control (nextPC T 0) (Q.start state) (partialBank (data base m) 0) 0 := by
    change Config.mk _ _ (fun _ ↦ 0) _ = Config.mk _ _ (registers (fun _ ↦ 0) _ 0) _
    congr 1
    funext i
    cases i using Fin.addCases with
    | left i => simp [registers]
    | right i =>
      cases i using Fin.lastCases with
      | last => simp only [registers, Fin.append_right, Fin.snoc_last]
      | cast j => simp [registers, partialBank]
  dsimp only
  rw [hs, execute_remaining T base 0 m bs (Q.start state) rfl f 0 k (by omega)]

private theorem extend_fuel {C : Type*} {P : Program w C} {f : ℕ} {c : C} {es result}
    (h : Guessed P f c es result) (pad : ℕ) : Guessed P (f+pad) c es result := by
  induction h with
  | done hs => simpa [Nat.succ_add] using Guessed.done (f := _+pad) hs
  | step hs _ ih => simpa [Nat.succ_add] using Guessed.step hs ih
  | branch hs _ ih => simpa [Nat.succ_add] using Guessed.branch hs ih
  | read hs _ ih => simpa [Nat.succ_add] using Guessed.read hs ih
  | write hs _ ih => simpa [Nat.succ_add] using Guessed.write hs ih

/-- At every caller fuel cap, including a cap too small to finish the
prelude, the original component has exactly the remaining fuel. -/
theorem execute_cap (base : Word w) (state : Word w) (cap : ℕ) (m : Memory w) (bs : List Bool) :
    let P := (machine T base).program
    let Q := (T.instantiate w (data base m)).program
    execute P cap (P.start state) m bs =
      (execute Q (cap-4*k) (Q.start state) m bs).map (LiveStageLink.prependLog
        (loadEvents base m 0 k)) := by
  dsimp only
  by_cases hf : 4*k ≤ cap
  · simpa only [Nat.sub_add_cancel hf] using execute_frame T base state (cap-4*k) m bs
  · have he : cap-4*k = 0 := by omega
    rw [he]
    cases h : execute (machine T base).program cap ((machine T base).program.start state) m bs with
    | none => rfl
    | some rep =>
      obtain ⟨hg,hm,hb⟩ := execute_spec h
      have hg' := extend_fuel hg (4*k-cap)
      rw [show cap+(4*k-cap) = 0+4*k by omega] at hg'
      have h' := execute_iff.mpr ⟨hg',hm,hb⟩
      rw [execute_frame T base state 0 m bs] at h'
      contradiction

/-- The source execution for a sequence of calls fetches the public bank
from the current external memory at each boundary. Only the original
component's writes change the bank for later calls. -/
def segment (base : Word w) (cap : ℕ) :
    Option (Word w) → Memory w → List (List Bool) → Option (List (Report w))
  | _, _, [] => some []
  | none, _, _ :: _ => none
  | some st, m, bs :: rest => do
    let Q := (T.instantiate w (data base m)).program
    let rep ← execute Q (cap-4*k) (Q.start st) m bs
    let tail ← segment base cap rep.result (after m rep.events) rest
    return LiveStageLink.prependLog (loadEvents base m 0 k) rep :: tail

/-- Pathwise equality through successive calls, including frames overwritten
by earlier calls and streams that propose extra choices after a halt. -/
theorem runSegment_frame (base : Word w) (cap : ℕ) (st : Option (Word w))
    (m : Memory w) (bits : List (List Bool)) :
    runSegment (machine T base).program cap st m bits = segment T base cap st m bits := by
  induction bits generalizing st m with
  | nil => rfl
  | cons bs rest ih =>
    cases st with
    | none => rfl
    | some st =>
      rw [runSegment, segment, execute_cap T base st cap m bs]
      let Q := (T.instantiate w (data base m)).program
      cases h : execute Q (cap-4*k) (Q.start st) m bs with
      | none => rfl
      | some rep =>
        have cost := frame_cost base m 0 k rep
        dsimp only [Option.map_some, Option.bind_some]
        rw [cost.2.2.2.1, cost.2.2.2.2, ih]
        change (segment T base cap rep.result (after m rep.events) rest).map _ =
          (segment T base cap rep.result (after m rep.events) rest).bind _
        cases segment T base cap rep.result (after m rep.events) rest <;> rfl

end CompressorRecords.Frame

end VPVNP
end Computability
end OAI
