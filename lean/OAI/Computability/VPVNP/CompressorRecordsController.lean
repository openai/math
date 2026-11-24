import OAI.Computability.VPVNP.CompressorRecordFrame
import OAI.Computability.VPVNP.RAMRecords

/-!
# Native controller for the compressor's directory of stages

Each directory row contains a worker tag, initial and exclusive final cursors,
and a padded bank of public operands. The controller snapshots the row before
writing the active frame. Its five public words are the frame base, directory
base, ordinal cell, row-count cell, and dispatch-tag cell.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Controller

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Number of controller instruction addresses, including six load-and-store instructions for
each of the stop word and padded operand slots. -/
abbrev PCs (g : ℕ) := 21 + (g+1)*6
/-- Number of controller registers, including a snapshot register for the stop word and each
padded public operand. -/
abbrev Regs (g : ℕ) := 10 + (g+1)

private abbrev Label (g : ℕ) := Fin 21 ⊕ (Fin (g+1) × Fin 6)
private def labels (g : ℕ) : Label g ≃ Fin (PCs g) :=
  ((Equiv.refl _).sumCongr finProdFinEquiv).trans finSumFinEquiv

private def head (g : ℕ) (i : Fin 21) := labels g (.inl i)
private def slot {g : ℕ} (j : Fin (g+1)) (i : Fin 6) := labels g (.inr (j,i))
private def reg (g : ℕ) (i : Fin 10) : Fin (Regs g) := i.castAdd (g+1)
private def bank {g : ℕ} (j : Fin (g+1)) : Fin (Regs g) := j.natAdd 10
private def storePC (g i : ℕ) := if h : i < g+1 then slot ⟨i,h⟩ 3 else head g 17
private def loadPC (g i : ℕ) := if h : i < g+1 then slot ⟨i,h⟩ 0 else storePC g 0
private def width (g : ℕ) := Nat.clog 2 (g+4)

private def headCode (g : ℕ) : Fin 21 → Instr (width g) (PCs g) (Regs g) 5
  | 0 => .publicWord (reg g 0) 2 (head g 1)
  | 1 => .readExternal (reg g 1) (reg g 0) (head g 2)
  | 2 => .publicWord (reg g 2) 3 (head g 3)
  | 3 => .readExternal (reg g 2) (reg g 2) (head g 4)
  | 4 => .jumpLt (reg g 1) (reg g 2) (head g 5) (head g 19)
  | 5 => .publicWord (reg g 3) 1 (head g 6)
  | 6 => .constant (reg g 4) (Fin.ofNat _ (g+3)) (head g 7)
  | 7 => .binary .mul (reg g 4) (reg g 1) (reg g 4) (head g 8)
  | 8 => .binary .add (reg g 3) (reg g 3) (reg g 4) (head g 9)
  | 9 => .readExternal (reg g 5) (reg g 3) (head g 10)
  | 10 => .constant (reg g 4) 1 (head g 11)
  | 11 => .binary .add (reg g 3) (reg g 3) (reg g 4) (head g 12)
  | 12 => .readExternal (reg g 6) (reg g 3) (head g 13)
  | 13 => .binary .add (reg g 3) (reg g 3) (reg g 4) (head g 14)
  | 14 => .publicWord (reg g 7) 0 (head g 15)
  | 15 => .publicWord (reg g 8) 4 (head g 16)
  | 16 => .binary .add (reg g 1) (reg g 1) (reg g 4) (loadPC g 0)
  | 17 => .writeExternal (reg g 0) (reg g 1) (head g 18)
  | 18 => .writeExternal (reg g 8) (reg g 5) (head g 20)
  | 19 => .accept
  | _ => .returnState (reg g 6)

private def slotCode {g : ℕ} (j : Fin (g+1)) : Fin 6 → Instr (width g) (PCs g) (Regs g) 5
  | 0 => .constant (reg g 9) (Fin.ofNat _ j.val) (slot j 1)
  | 1 => .binary .add (reg g 9) (reg g 3) (reg g 9) (slot j 2)
  | 2 => .readExternal (bank j) (reg g 9) (loadPC g (j.val+1))
  | 3 => .constant (reg g 9) (Fin.ofNat _ j.val) (slot j 4)
  | 4 => .binary .add (reg g 9) (reg g 7) (reg g 9) (slot j 5)
  | 5 => .writeExternal (reg g 9) (bank j) (storePC g (j.val+1))

/-- The program size depends only on the largest arity among the fixed worker tables. -/
def table (g : ℕ) : Template (PCs g) (Regs g) 5 where
  literalWidth := width g
  entry := head g 0
  code pc := match (labels g).symm pc with
    | .inl i => headCode g i
    | .inr (j,i) => slotCode j i

/-- The directory controller instantiated at the live word width with its five public workspace
addresses. -/
abbrev machine (g : ℕ) (pub : Fin 5 → Word w) := (table g).instantiate w pub

/-- Modular address arithmetic of the native program. -/
def rowBase (g : ℕ) (pub : Fin 5 → Word w) (m : Memory w) : Word w :=
  pub 1 + m (pub 2).val * ((g+3 : ℕ) : Word w)

/-- Read a directory or frame field at a word offset from the given source address. -/
def field (src : Word w) (m : Memory w) (i : ℕ) : Word w := m (src + (i : Word w)).val

private def prefixEvents (pub : Fin 5 → Word w) (m : Memory w) : List (Event w) :=
  [.tick, .read (pub 2) (m (pub 2).val), .tick, .read (pub 3) (m (pub 3).val), .tick]

/-- The terminating controller report after reading the current ordinal and directory row
count. -/
def doneReport (pub : Fin 5 → Word w) (m : Memory w) : Report w := ⟨prefixEvents pub m, none⟩

private def readEvents (src : Word w) (m : Memory w) (i : ℕ) : ℕ → List (Event w)
  | 0 => []
  | n+1 => [.tick, .tick, .read (src+(i : Word w)) (field src m i)] ++ readEvents src m (i+1) n

private def writeEvents (dst : Word w) (v : ℕ → Word w) (i : ℕ) : ℕ → List (Event w)
  | 0 => []
  | n+1 => [.tick, .tick, .write (dst+(i : Word w)) (v i)] ++ writeEvents dst v (i+1) n

private def rowHeader (base : Word w) (pub : Fin 5 → Word w) (m : Memory w) : List (Event w) :=
  prefixEvents pub m ++ [.tick, .tick, .tick, .tick, .read base (m base.val),
    .tick, .tick, .read (base+1) (m (base+1).val), .tick, .tick, .tick, .tick]

/-- Full transcript including the snapshot of the stop word and all padded operands. -/
def rowReport (g : ℕ) (pub : Fin 5 → Word w) (m : Memory w) : Report w :=
  let base := rowBase g pub m
  let src := base + 2
  ⟨rowHeader base pub m ++ readEvents src m 0 (g+1) ++
    writeEvents (pub 0) (field src m) 0 (g+1) ++
    [.write (pub 2) (m (pub 2).val+1), .write (pub 4) (m base.val)],
    some (m (base+1).val)⟩

private theorem literal_fit (g i : ℕ) (hi : i < g+4) : i < 2^width g :=
  hi.trans_le (Nat.le_pow_clog (by decide : 1 < 2) _)

private theorem code_head (g : ℕ) (pub : Fin 5 → Word w) (i : Fin 21) :
    (machine g pub).code (head g i) = (headCode g i).resize w := by
  simp [machine, table, Template.instantiate, head]

private theorem code_slot {g : ℕ} (pub : Fin 5 → Word w) (j : Fin (g+1)) (i : Fin 6) :
    (machine g pub).code (slot j i) = (slotCode j i).resize w := by
  simp [machine, table, Template.instantiate, slot]

private theorem update_left {a b : ℕ} {α : Type*} (l : Fin a → α) (r : Fin b → α)
    (i : Fin a) (v : α) :
    Function.update (Fin.append l r) (i.castAdd b) v = Fin.append (Function.update l i v) r := by
  funext t
  cases t using Fin.addCases with
  | left j => by_cases h : j = i <;> simp [Function.update, h]
  | right j =>
    have h : j.natAdd a ≠ i.castAdd b := fun e ↦ by have := congrArg Fin.val e; simp at this; omega
    simp [Function.update_of_ne h]

private theorem update_right {a b : ℕ} {α : Type*} (l : Fin a → α) (r : Fin b → α)
    (i : Fin b) (v : α) :
    Function.update (Fin.append l r) (i.natAdd a) v = Fin.append l (Function.update r i v) := by
  funext t
  cases t using Fin.addCases with
  | left j =>
    have h : j.castAdd b ≠ i.natAdd a := fun e ↦ by have := congrArg Fin.val e; simp at this; omega
    simp [Function.update_of_ne h]
  | right j => by_cases h : j = i <;> simp [Function.update, h]

private def config {g : ℕ} (pc : Fin (PCs g)) (s : Word w) (lo : Fin 10 → Word w)
    (hi : Fin (g+1) → Word w) : Config w (PCs g) (Regs g) := ⟨pc,s,Fin.append lo hi,fun _ ↦ 0⟩

private theorem start_eq (g : ℕ) (pub : Fin 5 → Word w) (s : Word w) :
    (machine g pub).program.start s = config (head g 0) s (fun _ ↦ 0) (fun _ ↦ 0) := by
  change Config.mk _ _ (fun _ ↦ 0) _ = Config.mk _ _ _ _
  congr 1
  funext j
  cases j using Fin.addCases <;> simp

private theorem step_cfg {g : ℕ} (pub : Fin 5 → Word w) (pc : Fin (PCs g)) (s : Word w)
    (lo : Fin 10 → Word w) (hi : Fin (g+1) → Word w) :
    (machine g pub).program.step (config pc s lo hi) =
      ((machine g pub).code pc).run pub (config pc s lo hi) := rfl

private theorem cfg_put {g : ℕ} (pc next : Fin (PCs g)) (s : Word w)
    (lo : Fin 10 → Word w) (hi : Fin (g+1) → Word w) (r : Fin 10) (v : Word w) :
    (config pc s lo hi).put next (reg g r) v = config next s (Function.update lo r v) hi := by
  simp [Config.put, config, reg, update_left]

private theorem cfg_bank {g : ℕ} (pc next : Fin (PCs g)) (s : Word w)
    (lo : Fin 10 → Word w) (hi : Fin (g+1) → Word w) (j : Fin (g+1)) (v : Word w) :
    (config pc s lo hi).put next (bank j) v = config next s lo (Function.update hi j v) := by
  simp [Config.put, config, bank, update_right]

private theorem reg_cfg {g : ℕ} (pc : Fin (PCs g)) (s : Word w)
    (lo : Fin 10 → Word w) (hi : Fin (g+1) → Word w) (r : Fin 10) :
    (config pc s lo hi).reg (reg g r) = lo r := by simp [config, reg]

private theorem bank_cfg {g : ℕ} (pc : Fin (PCs g)) (s : Word w)
    (lo : Fin 10 → Word w) (hi : Fin (g+1) → Word w) (j : Fin (g+1)) :
    (config pc s lo hi).reg (bank j) = hi j := by simp [config, bank]

private theorem load_one {g : ℕ} (pub : Fin 5 → Word w) (j : Fin (g+1)) (s : Word w)
    (lo : Fin 10 → Word w) (hi : Fin (g+1) → Word w) (m : Memory w) (bs : List Bool) (f : ℕ) :
    let a := lo 3 + (j.val : Word w)
    execute (machine g pub).program (f+3) (config (loadPC g j.val) s lo hi) m bs =
      (execute (machine g pub).program f (config (loadPC g (j.val+1)) s
        (Function.update lo 9 a) (Function.update hi j (m a.val))) m bs).map
        (LiveStageLink.prependLog [.tick,.tick,.read a (m a.val)]) := by
  have lit := literal_fit g j.val (by have := j.isLt; omega)
  rw [show loadPC g j.val = slot j 0 by simp [loadPC, j.isLt]]
  simp (config := {decide := true}) [execute, step_cfg, code_slot, slotCode, Instr.resize, Instr.run,
    cfg_put, cfg_bank, reg_cfg, BinaryOp.eval, Nat.mod_eq_of_lt lit, Function.update_idem,
    Function.comp_def, Report.prepend]
  rfl

private theorem store_one {g : ℕ} (pub : Fin 5 → Word w) (j : Fin (g+1)) (s : Word w)
    (lo : Fin 10 → Word w) (hi : Fin (g+1) → Word w) (m : Memory w) (bs : List Bool) (f : ℕ) :
    let a := lo 7 + (j.val : Word w)
    execute (machine g pub).program (f+3) (config (storePC g j.val) s lo hi) m bs =
      (execute (machine g pub).program f (config (storePC g (j.val+1)) s
        (Function.update lo 9 a) hi) (writeMemory m a (hi j)) bs).map
        (LiveStageLink.prependLog [.tick,.tick,.write a (hi j)]) := by
  have lit := literal_fit g j.val (by have := j.isLt; omega)
  rw [show storePC g j.val = slot j 3 by simp [storePC, j.isLt]]
  simp (config := {decide := true}) [execute, step_cfg, code_slot, slotCode, Instr.resize, Instr.run,
    cfg_put, reg_cfg, bank_cfg, BinaryOp.eval, Nat.mod_eq_of_lt lit, Function.update_idem,
    Function.comp_def, Report.prepend]
  rfl

private theorem cfg_move {g : ℕ} (pc next : Fin (PCs g)) (s : Word w)
    (lo : Fin 10 → Word w) (hi : Fin (g+1) → Word w) :
    Config.mk next (config pc s lo hi).persistent (config pc s lo hi).reg
      (config pc s lo hi).privateMem = config next s lo hi := rfl

private def closing (lo : Fin 10 → Word w) : List (Event w) :=
  [.write (lo 0) (lo 1), .write (lo 8) (lo 5)]

private theorem store_tail (g : ℕ) (pub : Fin 5 → Word w) (s : Word w)
    (lo : Fin 10 → Word w) (hi : Fin (g+1) → Word w) (m : Memory w)
    (bs : List Bool) (f : ℕ) (v : ℕ → Word w) (hv : ∀ j, hi j = v j.val)
    (i n : ℕ) (hlen : i+n = g+1) :
    execute (machine g pub).program (f+3+3*n) (config (storePC g i) s lo hi) m bs =
      if bs = [] then some ⟨writeEvents (lo 7) v i n ++ closing lo, some (lo 6)⟩ else none := by
  induction n generalizing i lo m with
  | zero =>
    simp only [Nat.add_zero] at hlen
    subst i
    by_cases h : bs = [] <;>
      simp [storePC, execute, step_cfg, code_head, headCode, Instr.resize, Instr.run,
        reg_cfg, cfg_move, h, writeEvents, closing, Report.prepend]
  | succ n ih =>
    let j : Fin (g+1) := ⟨i, by omega⟩
    have eqf : f+3+3*(n+1) = (f+3+3*n)+3 := by omega
    rw [eqf, store_one pub j, ih _ _ (i+1) (by omega)]
    by_cases h : bs = [] <;> simp (config := {decide := true}) [h, hv, writeEvents, closing,
      LiveStageLink.prependLog, j]

private theorem load_tail (g : ℕ) (pub : Fin 5 → Word w) (s : Word w)
    (lo : Fin 10 → Word w) (hi : Fin (g+1) → Word w) (m : Memory w)
    (bs : List Bool) (f i n : ℕ) (hlen : i+n = g+1)
    (hv : ∀ j : Fin (g+1), j.val < i → hi j = field (lo 3) m j.val) :
    execute (machine g pub).program (f+3+3*(g+1)+3*n) (config (loadPC g i) s lo hi) m bs =
      if bs = [] then some ⟨readEvents (lo 3) m i n ++
        writeEvents (lo 7) (field (lo 3) m) 0 (g+1) ++ closing lo, some (lo 6)⟩ else none := by
  induction n generalizing i lo hi with
  | zero =>
    simp only [Nat.add_zero] at hlen
    subst i
    simp only [Nat.mul_zero, Nat.add_zero, loadPC, lt_self_iff_false, ↓reduceDIte, readEvents,
      List.nil_append]
    exact store_tail g pub s lo hi m bs f _ (fun j ↦ hv j j.isLt) 0 (g+1) (by omega)
  | succ n ih =>
    let j : Fin (g+1) := ⟨i, by omega⟩
    let a := lo 3 + (i : Word w)
    have hx : ∀ t : Fin (g+1), t.val < i+1 →
        Function.update hi j (m a.val) t = field (Function.update lo 9 a 3) m t.val := by
      intro t ht
      by_cases h : t = j
      · subst t; simp (config := {decide := true}) [j, a, field]
      · have hh : t.val ≠ i := fun e ↦ h (Fin.ext e)
        simp (config := {decide := true}) [Function.update_of_ne h, hv t (by omega)]
    have eqf : f+3+3*(g+1)+3*(n+1) = (f+3+3*(g+1)+3*n)+3 := by omega
    rw [eqf, load_one pub j, ih _ _ (i+1) (by omega) hx]
    by_cases h : bs = [] <;> simp (config := {decide := true}) [h, readEvents, field, closing,
      LiveStageLink.prependLog, j]

private def ready (g : ℕ) (pub : Fin 5 → Word w) (m : Memory w) : Fin 10 → Word w :=
  let base := rowBase g pub m
  ![pub 2, m (pub 2).val + 1, m (pub 3).val, base+2, 1, m base.val,
    m (base+1).val, pub 0, pub 4, 0]

set_option maxHeartbeats 600000 in
private theorem row_header_run (g : ℕ) (pub : Fin 5 → Word w) (s : Word w)
    (m : Memory w) (bs : List Bool) (f : ℕ) (active : m (pub 2).val < m (pub 3).val) :
    execute (machine g pub).program (f+17) ((machine g pub).program.start s) m bs =
      (execute (machine g pub).program f (config (loadPC g 0) s (ready g pub m) (fun _ ↦ 0)) m bs).map
        (LiveStageLink.prependLog (rowHeader (rowBase g pub m) pub m)) := by
  have stride : ((g : Word (width g)) + 3).val = g+3 := by
    rw [← show ((g+3 : ℕ) : Word (width g)) = (g : Word (width g))+3 by simp]
    exact Nat.mod_eq_of_lt (literal_fit g (g+3) (by omega))
  have one := Nat.mod_eq_of_lt (literal_fit g 1 (by omega))
  rw [start_eq]
  simp (config := {decide := true}) [execute, step_cfg, code_head, headCode, Instr.resize, Instr.run,
    stride, one,
    cfg_put, reg_cfg, cfg_move, active, BinaryOp.eval,
    Function.comp_def, Report.prepend]
  congr 1
  · funext z; simp [LiveStageLink.prependLog, rowHeader, prefixEvents, rowBase]
  · congr 2
    funext i
    fin_cases i <;> simp (config := {decide := true}) [ready, rowBase, add_assoc]
    exact one_add_one_eq_two

/-- The complete native directory-row call, at any sufficient cap and for any proposed stream. -/
theorem execute_row (g : ℕ) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (bs : List Bool) (fuel : ℕ) (active : m (pub 2).val < m (pub 3).val)
    (cap : 20+6*(g+1) ≤ fuel) :
    execute (machine g pub).program fuel ((machine g pub).program.start s) m bs =
      if bs = [] then some (rowReport g pub m) else none := by
  let pad := fuel - (20+6*(g+1))
  rw [show fuel = (pad+3+3*(g+1)+3*(g+1))+17 by dsimp [pad]; omega, row_header_run g pub s m bs _ active,
    load_tail g pub s (ready g pub m) (fun _ ↦ 0) m bs pad 0 (g+1) (by omega) (by simp)]
  by_cases h : bs = [] <;> simp [h, ready, rowReport, LiveStageLink.prependLog, closing,
    List.append_assoc]

/-- An exhausted directory accepts immediately after reading the ordinal and row count. -/
theorem execute_done (g : ℕ) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (bs : List Bool) (fuel : ℕ) (closed : m (pub 3).val ≤ m (pub 2).val) (cap : 6 ≤ fuel) :
    execute (machine g pub).program fuel ((machine g pub).program.start s) m bs =
      if bs = [] then some (doneReport pub m) else none := by
  obtain ⟨f,rfl⟩ : ∃ f, fuel = f+6 := ⟨fuel-6, by omega⟩
  rw [start_eq]
  by_cases h : bs = [] <;>
    simp (config := {decide := true}) [execute, step_cfg, code_head, headCode, Instr.resize, Instr.run,
      cfg_put, reg_cfg, cfg_move, not_lt_of_ge closed, h, doneReport, prefixEvents, Report.prepend]

private theorem probes_append (a b : List (Event w)) :
    countProbes (a++b) = countProbes a + countProbes b := by
  induction a with
  | nil => simp [countProbes]
  | cons e a ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

private theorem choices_append (a b : List (Event w)) :
    choiceBits (a++b) = choiceBits a ++ choiceBits b := by
  induction a with
  | nil => rfl
  | cons e a ih => cases e <;> simp [choiceBits, ih]

private theorem read_cost (src : Word w) (m : Memory w) (i n : ℕ) :
    (readEvents src m i n).length = 3*n ∧ countProbes (readEvents src m i n) = n ∧
      choiceBits (readEvents src m i n) = [] := by
  induction n generalizing i with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨hl,hp,hc⟩ := ih (i+1)
    simp [readEvents, countProbes, choiceBits, hl, hp, hc, Nat.mul_succ, Nat.add_comm]
    omega

private theorem write_cost (dst : Word w) (v : ℕ → Word w) (i n : ℕ) :
    (writeEvents dst v i n).length = 3*n ∧ countProbes (writeEvents dst v i n) = n ∧
      choiceBits (writeEvents dst v i n) = [] := by
  induction n generalizing i with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨hl,hp,hc⟩ := ih (i+1)
    simp [writeEvents, countProbes, choiceBits, hl, hp, hc, Nat.mul_succ, Nat.add_comm]
    omega

theorem rowReport_cost (g : ℕ) (pub : Fin 5 → Word w) (m : Memory w) :
    (rowReport g pub m).events.length = 19+6*(g+1) ∧
      countProbes (rowReport g pub m).events = 6+2*(g+1) ∧
      choiceBits (rowReport g pub m).events = [] := by
  let src := rowBase g pub m + 2
  obtain ⟨hl,hp,hc⟩ := read_cost src m 0 (g+1)
  obtain ⟨hl',hp',hc'⟩ := write_cost (pub 0) (field src m) 0 (g+1)
  simp only [rowReport, show rowBase g pub m + 2 = src by rfl, List.length_append, probes_append,
    choices_append, hl, hp, hc, hl', hp', hc']
  simp [rowHeader, prefixEvents, countProbes, choiceBits]
  omega

theorem doneReport_cost (pub : Fin 5 → Word w) (m : Memory w) :
    (doneReport pub m).events.length = 5 ∧ countProbes (doneReport pub m).events = 2 ∧
      choiceBits (doneReport pub m).events = [] := ⟨rfl,rfl,rfl⟩

private theorem after_append (m : Memory w) (a b : List (Event w)) :
    after m (a++b) = after (after m a) b := List.foldl_append

private theorem read_after (src : Word w) (m m' : Memory w) (i n : ℕ) :
    after m' (readEvents src m i n) = m' := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => exact ih (i+1)

/-- The memory after copying the selected row's exclusive stop and padded operands into the
active worker frame. -/
def frameMemory (g : ℕ) (pub : Fin 5 → Word w) (m : Memory w) : Memory w :=
  after m (writeEvents (pub 0) (field (rowBase g pub m + 2) m) 0 (g+1))

theorem after_done (pub : Fin 5 → Word w) (m : Memory w) : after m (doneReport pub m).events = m := rfl

theorem after_row (g : ℕ) (pub : Fin 5 → Word w) (m : Memory w) :
    after m (rowReport g pub m).events =
      writeMemory (writeMemory (frameMemory g pub m) (pub 2) (m (pub 2).val+1))
        (pub 4) (m (rowBase g pub m).val) := by
  simp only [rowReport, after_append, read_after]
  rfl

theorem after_row_tag (g : ℕ) (pub : Fin 5 → Word w) (m : Memory w) :
    after m (rowReport g pub m).events (pub 4).val = m (rowBase g pub m).val := by
  rw [after_row]; simp [writeMemory]

theorem after_row_ordinal (g : ℕ) (pub : Fin 5 → Word w) (m : Memory w)
    (h : pub 2 ≠ pub 4) :
    after m (rowReport g pub m).events (pub 2).val = m (pub 2).val + 1 := by
  rw [after_row]; simp [writeMemory, Fin.val_ne_of_ne h]

private theorem writes_outside (dst : Word w) (v : ℕ → Word w) (m : Memory w) (a i n : ℕ)
    (h : ∀ t, i ≤ t → t < i+n → a ≠ (dst+(t : Word w)).val) :
    after m (writeEvents dst v i n) a = m a := by
  induction n generalizing i m with
  | zero => rfl
  | succ n ih =>
    change after (writeMemory m (dst+(i : Word w)) (v i)) (writeEvents dst v (i+1) n) a = m a
    rw [ih _ (i+1) (fun t h₁ h₂ ↦ h t (by omega) (by omega))]
    simp [writeMemory, h i le_rfl (by omega)]

/-- A worker-data word, a future directory word, or the row count is preserved when
it lies outside the frame and the two mutable control cells. -/
theorem after_row_outside (g : ℕ) (pub : Fin 5 → Word w) (m : Memory w) (a : ℕ)
    (ho : a ≠ (pub 2).val) (ht : a ≠ (pub 4).val)
    (hf : ∀ i : Fin (g+1), a ≠ (pub 0 + (i.val : Word w)).val) :
    after m (rowReport g pub m).events a = m a := by
  rw [after_row]
  simp only [writeMemory, ht, ho, ↓reduceIte, frameMemory]
  exact writes_outside _ _ _ _ _ _ fun t _ h ↦ hf ⟨t, by omega⟩

private theorem writes_at (dst : Word w) (v : ℕ → Word w) (m : Memory w) (k i n : ℕ)
    (lo : i ≤ k) (hi : k < i+n) (fit : i+n ≤ 2^w) :
    after m (writeEvents dst v i n) (dst+(k : Word w)).val = v k := by
  induction n generalizing m i with
  | zero => omega
  | succ n ih =>
    change after (writeMemory m (dst+(i : Word w)) (v i)) (writeEvents dst v (i+1) n) _ = _
    by_cases eqn : k = i
    · subst k
      rw [writes_outside]
      · simp [writeMemory]
      · intro t h₁ h₂ he
        have hx : (i : Word w) = (t : Word w) := add_left_cancel (Fin.ext he)
        have hv := congrArg Fin.val hx
        simp only [Fin.val_natCast, Nat.mod_eq_of_lt (show i < 2^w by omega),
          Nat.mod_eq_of_lt (show t < 2^w by omega)] at hv
        omega
    · exact ih _ (i+1) (by omega) (by omega) (by omega)

/-- The first frame word is the exclusive stop. The remaining words are the
worker's padded parameter bank. All field values refer to the entry memory. -/
theorem after_row_frame (g : ℕ) (pub : Fin 5 → Word w) (m : Memory w) (i : Fin (g+1))
    (fit : g+1 ≤ 2^w) (ho : pub 0 + (i.val : Word w) ≠ pub 2)
    (ht : pub 0 + (i.val : Word w) ≠ pub 4) :
    after m (rowReport g pub m).events (pub 0 + (i.val : Word w)).val =
      field (rowBase g pub m + 2) m i.val := by
  rw [after_row]
  simp only [writeMemory, Fin.val_ne_of_ne ho, Fin.val_ne_of_ne ht, ↓reduceIte, frameMemory]
  exact writes_at _ _ _ _ 0 (g+1) (by omega) (by have := i.isLt; omega) (by omega)

/-- A directory fitting in the physical address space uses the ordinary row-major index. -/
theorem rowBase_val (g : ℕ) (pub : Fin 5 → Word w) (m : Memory w)
    (fit : (pub 1).val + (m (pub 2).val).val * (g+3) < 2^w) :
    (rowBase g pub m).val = (pub 1).val + (m (pub 2).val).val * (g+3) := by
  simp only [rowBase, Fin.val_add, Fin.val_mul, Fin.val_natCast, Nat.mul_mod_mod,
    Nat.add_mod_mod, Nat.mod_eq_of_lt fit]

/-- When a row is present, advancing its ordinal never wraps around. -/
theorem after_row_ordinal_val (g : ℕ) (pub : Fin 5 → Word w) (m : Memory w)
    (h : pub 2 ≠ pub 4) (active : m (pub 2).val < m (pub 3).val) :
    (after m (rowReport g pub m).events (pub 2).val).val = (m (pub 2).val).val+1 := by
  have ht := (m (pub 3).val).isLt
  have hl := Fin.lt_def.mp active
  rw [after_row_ordinal g pub m h, Fin.val_add, Fin.val_one',
    Nat.mod_eq_of_lt (show 1 < 2^w by omega), Nat.mod_eq_of_lt (by omega)]

private theorem guessed_pad {C : Type*} {P : Program w C} {f c es out}
    (h : Guessed P f c es out) (pad : ℕ) : Guessed P (f+pad) c es out := by
  induction h with
  | done hs => simpa [Nat.succ_add] using Guessed.done (f := _+pad) hs
  | step hs _ ih => simpa [Nat.succ_add] using Guessed.step hs ih
  | branch hs _ ih => simpa [Nat.succ_add] using Guessed.branch hs ih
  | read hs _ ih => simpa [Nat.succ_add] using Guessed.read hs ih
  | write hs _ ih => simpa [Nat.succ_add] using Guessed.write hs ih

private theorem exact_cap {C : Type*} {P : Program w C} {c : C} {m : Memory w}
    {bs : List Bool} {rep : Report w} {ticks : ℕ} (hl : rep.events.length = ticks)
    (hs : ∀ f, ticks < f → execute P f c m bs = if bs = [] then some rep else none) (fuel : ℕ) :
    execute P fuel c m bs = if bs = [] ∧ ticks < fuel then some rep else none := by
  by_cases hf : ticks < fuel
  · simpa [hf] using hs fuel hf
  simp only [hf, and_false, ↓reduceIte]
  cases he : execute P fuel c m bs with
  | none => rfl
  | some t =>
    obtain ⟨hg,hm,hb⟩ := execute_spec he
    have big := execute_iff.mpr ⟨guessed_pad hg (ticks+1), hm, hb⟩
    rw [hs _ (by omega)] at big
    split at big
    · have eqn : rep = t := Option.some.inj big
      subst t
      have := hg.length_lt
      omega
    · contradiction

/-- For every cap, the controller succeeds exactly when the complete
deterministic transcript and its terminal instruction fit in that cap. -/
theorem execute_cap (g : ℕ) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (bs : List Bool) (fuel : ℕ) :
    let rep := if m (pub 2).val < m (pub 3).val then rowReport g pub m else doneReport pub m
    execute (machine g pub).program fuel ((machine g pub).program.start s) m bs =
      if bs = [] ∧ rep.events.length < fuel then some rep else none := by
  dsimp only
  split
  · rename_i active
    apply exact_cap rfl
    intro f hf
    exact execute_row g pub s m bs f active (by rw [(rowReport_cost ..).1] at hf; omega)
  · rename_i h
    apply exact_cap rfl
    intro f hf
    exact execute_done g pub s m bs f (le_of_not_gt h) (by rw [(doneReport_cost ..).1] at hf; omega)

end CompressorRecords.Controller

end VPVNP
end Computability
end OAI
