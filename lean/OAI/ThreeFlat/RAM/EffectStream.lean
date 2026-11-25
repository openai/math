import OAI.ThreeFlat.RAM.Weighted
import Mathlib.Data.Fin.Embedding

namespace OAI
/-! # Replaying a chronological stream of external RAM writes

Each two-word record contains a destination address and a value. The six-label
native loop applies the records in order. Destinations may repeat.
-/

namespace ThreeFlat.RAM.EffectStream

open Computability.VPVNP.BurstRAM PrivateRAM

variable {F : Type*} {w p r k : ℕ}

abbrev Record (w : ℕ) := Word w × Word w

def events (updates : List (Record w)) : List (Event w) :=
  updates.map fun av => Event.write av.1 av.2

/-- Consecutive words store each record's address followed by its value. -/
def Loaded (m : Memory w) (src : ℕ) : List (Record w) → Prop
  | [] => True
  | (a,v)::xs => m src = a ∧ m (src+1) = v ∧ Loaded m (src+2) xs

theorem loaded_iff (m : Memory w) (src : ℕ) (updates : List (Record w)) :
    Loaded m src updates ↔ ∀ i : Fin updates.length,
      m (src+2*i.val) = (updates.get i).1 ∧ m (src+2*i.val+1) = (updates.get i).2 := by
  induction updates generalizing src with
  | nil => simp [Loaded]
  | cons av xs ih =>
    obtain ⟨a,v⟩ := av
    constructor
    · rintro ⟨ha,hv,ht⟩
      refine Fin.cases (by simpa using And.intro ha hv) (fun i => ?_)
      simpa [Fin.val_succ, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using (ih (src+2)).1 ht i
    · intro h
      have atHead := h 0
      simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, List.get_cons_zero] at atHead
      refine ⟨atHead.1, atHead.2, (ih (src+2)).2 (fun i => ?_)⟩
      simpa [Fin.val_succ, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using h i.succ

theorem loaded_of_agree {old new : Memory w} {src : ℕ} {xs : List (Record w)} (h : Loaded old src xs)
    (region : ∀ a, src ≤ a → a < src+2*xs.length → new a = old a) : Loaded new src xs := by
  rw [loaded_iff] at h ⊢
  intro i
  have hi := i.isLt
  rw [region (src+2*i.val) (by omega) (by omega), region (src+2*i.val+1) (by omega) (by omega)]
  exact h i

/-- All destination addresses lie outside the input records. -/
def Safe (src : ℕ) (updates : List (Record w)) : Prop :=
  ∀ av ∈ updates, av.1.val < src ∨ src + 2*updates.length ≤ av.1.val

/-- The registers hold the source cursor and stop, the address and value
buffers, and the fixed word one. -/
def block (pc : Fin 6 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p) : Fin 6 → Instr w p r k
  | 0 => .jumpLt (reg 0) (reg 1) (pc 1) exit
  | 1 => .readExternal (reg 2) (reg 0) (pc 2)
  | 2 => .binary .add (reg 0) (reg 0) (reg 4) (pc 3)
  | 3 => .readExternal (reg 3) (reg 0) (pc 4)
  | 4 => .writeExternal (reg 2) (reg 3) (pc 5)
  | 5 => .binary .add (reg 0) (reg 0) (reg 4) (pc 0)

def next (reg : Fin 5 ↪ Fin r) (pc : Fin 6 → Fin p) (c : Config w p r) (a v : Word w) : Config w p r :=
  (((c.put (pc 2) (reg 2) a).put (pc 3) (reg 0) (c.reg (reg 0)+1)).put
    (pc 4) (reg 3) v).put (pc 0) (reg 0) (c.reg (reg 0)+1+1)

def endConfig (reg : Fin 5 ↪ Fin r) (pc : Fin 6 → Fin p) (exit : Fin p) :
    List (Record w) → Config w p r → Config w p r
  | [], c => {c with pc := exit}
  | (a,v)::xs, c => endConfig reg pc exit xs (next reg pc c a v)

@[simp] theorem endConfig_pc (reg : Fin 5 ↪ Fin r) (pc : Fin 6 → Fin p) (exit : Fin p)
    (xs : List (Record w)) (c : Config w p r) : (endConfig reg pc exit xs c).pc = exit := by
  induction xs generalizing c with
  | nil => rfl
  | cons av xs ih => exact ih _

theorem endConfig_reg (reg : Fin 5 ↪ Fin r) (pc : Fin 6 → Fin p) (exit : Fin p)
    (xs : List (Record w)) (c : Config w p r) (i : Fin r) (h0 : i ≠ reg 0)
    (h2 : i ≠ reg 2) (h3 : i ≠ reg 3) : (endConfig reg pc exit xs c).reg i = c.reg i := by
  induction xs generalizing c with
  | nil => rfl
  | cons av xs ih =>
    obtain ⟨a,v⟩ := av
    rw [endConfig, ih]
    simp [next, Config.put, Function.update_of_ne, h0, h2, h3]

private theorem mass_one [Semiring F] (field : FieldCode F w) (M : Machine w p r k)
    (pc : Fin 6 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p)
    (installed : ∀ i, M.code (pc i) = block pc reg exit i) (fuel : ℕ)
    (c : Config w p r) (m : Memory w) (entry : c.pc = pc 0)
    (active : c.reg (reg 0) < c.reg (reg 1)) (unit : c.reg (reg 4) = 1)
    (a v : Word w) (ha : m (c.reg (reg 0)).val = a) (hv : m (c.reg (reg 0)+1).val = v) :
    mass field M.program (fuel+6) c m =
      mass field M.program fuel (next reg pc c a v) (writeMemory m a v) := by
  simp (config := { decide := true }) [mass, Machine.program, entry, installed, block, Instr.run,
    active, BinaryOp.eval, unit, Config.put, Function.update, next, ha, hv]

/-- Apply the write stream to any continuation, preserving the full chronological
effect even when a later record overwrites an earlier destination. -/
theorem mass_block [Semiring F] (field : FieldCode F w) (M : Machine w p r k)
    (pc : Fin 6 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p)
    (installed : ∀ i, M.code (pc i) = block pc reg exit i) (src : ℕ) (updates : List (Record w))
    (fuel : ℕ) (c : Config w p r) (m : Memory w) (entry : c.pc = pc 0)
    (cursor : (c.reg (reg 0)).val = src) (stop : (c.reg (reg 1)).val = src+2*updates.length)
    (unit : c.reg (reg 4) = 1) (input : Loaded m src updates) (safe : Safe src updates) :
    mass field M.program (fuel+1+6*updates.length) c m =
      mass field M.program fuel (endConfig reg pc exit updates c) (after m (events updates)) := by
  induction updates generalizing src c m with
  | nil =>
    have eq : c.reg (reg 0) = c.reg (reg 1) := Fin.ext (by simpa [cursor] using stop.symm)
    simp [events, after, endConfig, mass, Machine.program, entry, installed, block, Instr.run, eq]
  | cons av xs ih =>
    obtain ⟨a,v⟩ := av
    obtain ⟨loadedAddr, loadedVal, tailLoaded⟩ := input
    simp only [List.length_cons, Nat.mul_succ] at stop
    have top := (c.reg (reg 1)).isLt
    have active : c.reg (reg 0) < c.reg (reg 1) := by change _ < (c.reg (reg 1)).val; omega
    have inc : (c.reg (reg 0)+1).val = src+1 := by
      rw [Fin.val_add_one_of_lt', cursor]
      change (c.reg (reg 0)).val + 1 < 2^w
      omega
    have inc2 : (c.reg (reg 0)+1+1).val = src+2 := by
      rw [Fin.val_add_one_of_lt', inc]
      change (c.reg (reg 0)+1).val + 1 < 2^w
      omega
    let c' := next reg pc c a v
    let m' := writeMemory m a v
    have cur' : (c'.reg (reg 0)).val = src+2 := by
      simpa (config := { decide := true }) [c', next, Config.put, Function.update] using inc2
    have stop' : (c'.reg (reg 1)).val = (src+2)+2*xs.length := by
      simpa (config := { decide := true }) [c', next, Config.put, Function.update, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using stop
    have unit' : c'.reg (reg 4) = 1 := by
      simpa (config := { decide := true }) [c', next, Config.put, Function.update] using unit
    have away := safe (a,v) (.head _)
    simp only [List.length_cons, Nat.mul_succ] at away
    have tailOk : Loaded m' (src+2) xs := loaded_of_agree tailLoaded (by
      intro b lo hi
      have ne : b ≠ a.val := by omega
      simp [m', writeMemory, ne])
    have tailSafe : Safe (src+2) xs := by
      intro av hav
      have h := safe av (.tail _ hav)
      simp only [List.length_cons, Nat.mul_succ] at h
      omega
    have tailMass := ih (src+2) c' m' rfl cur' stop' unit' tailOk tailSafe
    rw [show fuel+1+6*((a,v)::xs).length = (fuel+1+6*xs.length)+6 by simp [Nat.mul_add, Nat.add_assoc],
      mass_one field M pc reg exit installed _ c m entry active unit a v
        (by rw [cursor]; exact loadedAddr) (by rw [inc]; exact loadedVal)]
    exact tailMass

def label (n : ℕ) (i : Fin 6) : Fin (6+n) := i.castAdd n
def callerLabel (n : ℕ) (i : Fin n) : Fin (6+n) := i.natAdd 6

/-- An actual six-label interpreter prefix followed by the caller's instruction bank. -/
def machine (n : ℕ) (reg : Fin 5 ↪ Fin r) (exit : Fin (6+n))
    (caller : Fin n → Instr w (6+n) r k) (data : Fin k → Word w) : Machine w (6+n) r k where
  entry := label n 0
  code := Fin.addCases (block (label n) reg exit) caller
  publicData := data

@[simp] theorem machine_label (n : ℕ) (reg : Fin 5 ↪ Fin r) (exit : Fin (6+n))
    (caller : Fin n → Instr w (6+n) r k) (data : Fin k → Word w) (i : Fin 6) :
    (machine n reg exit caller data).code (label n i) = block (label n) reg exit i := by
  simp [machine, label]

@[simp] theorem machine_caller (n : ℕ) (reg : Fin 5 ↪ Fin r) (exit : Fin (6+n))
    (caller : Fin n → Instr w (6+n) r k) (data : Fin k → Word w) (i : Fin n) :
    (machine n reg exit caller data).code (callerLabel n i) = caller i := by
  simp [machine, callerLabel]

theorem mass_machine [Semiring F] (field : FieldCode F w) (n : ℕ) (reg : Fin 5 ↪ Fin r)
    (exit : Fin (6+n)) (caller : Fin n → Instr w (6+n) r k) (data : Fin k → Word w)
    (src : ℕ) (updates : List (Record w)) (fuel : ℕ) (c : Config w (6+n) r) (m : Memory w)
    (entry : c.pc = label n 0) (cursor : (c.reg (reg 0)).val = src)
    (stop : (c.reg (reg 1)).val = src+2*updates.length) (unit : c.reg (reg 4) = 1)
    (input : Loaded m src updates) (safe : Safe src updates) :
    let M := machine n reg exit caller data
    mass field M.program (fuel+1+6*updates.length) c m =
      mass field M.program fuel (endConfig reg (label n) exit updates c) (after m (events updates)) :=
  mass_block field _ (label n) reg exit (machine_label n reg exit caller data) src updates fuel c m
    entry cursor stop unit input safe

end ThreeFlat.RAM.EffectStream

end OAI
