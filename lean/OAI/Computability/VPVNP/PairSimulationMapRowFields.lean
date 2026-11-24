import OAI.Computability.VPVNP.PairSimulationMapStream
import OAI.Computability.VPVNP.PairSimulationFieldRead

/-!
# Preparing the registers of a fixed motif row

Every endpoint has its own base address, exclusive end and output register.
Both endpoints of a group use the same current offset. Four instructions
initialize the padded field reader from these resident registers and a fixed
width port. The resulting loop preserves the register fields already read.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapRowFields

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedInputRAM MotifEntry
open scoped Fin.CommRing

variable {I A : Type*} {w p r k : ℕ}

/-- Fixed register allocation for row extraction, including both endpoint directions. -/
inductive Slot (I A : Type*) where
  | query (i : I)
  | base (i : I)
  | dataEnd (i : I)
  | offset (g : A)
  | cursor | start | one | tmp | label
  deriving DecidableEq, Fintype

/-- Inject the endpoint data and query slots, shared group offsets, and working registers for
one row into the machine's physical registers. -/
abbrev Registers (I A : Type*) (r : ℕ) := Slot I A ↪ Fin r

/-- The padded reader writes the field's query register directly. -/
def readerRegs (reg : Registers I A r) (i : I) : Fin 6 ↪ Fin r :=
  (⟨![Slot.query i, .cursor, .start, .dataEnd i, .one, .tmp], by
    intro l m h
    fin_cases l <;> fin_cases m <;> first | rfl | cases h⟩ :
      Fin 6 ↪ Slot I A).trans reg

/-- Absolute field start, fixed width, exclusive high cursor and zero accumulator. -/
def setup (reg : Registers I A r) (group : I → A) (width : A → Fin k)
    (pc : Fin 4 → Fin p) (reader : Fin 7 → Fin p) (i : I) : Fin 4 → Instr w p r k :=
  ![.binary .add (reg .start) (reg (.base i)) (reg (.offset (group i))) (pc 1),
    .publicWord (reg .tmp) (width (group i)) (pc 2),
    .binary .add (reg .cursor) (reg .start) (reg .tmp) (pc 3),
    .constant (reg (.query i)) 0 (reader 0)]

theorem resize_setup (reg : Registers I A r) (group : I → A) (width : A → Fin k)
    (pc : Fin 4 → Fin p) (reader : Fin 7 → Fin p) (i : I) (a : Fin 4) :
    (setup (w := 1) reg group width pc reader i a).resize w =
      setup reg group width pc reader i a := by fin_cases a <;> rfl

/-- Resident bit slices and current group offsets for one iteration. A zero-length
slice represents an absent port and yields zero at any offset. -/
structure Slices (I A : Type*) where
  /-- Number of resident bits for each endpoint slice. An absent endpoint has length zero. -/
  len : I → ℕ
  /-- The bit at each in-range position of an endpoint's resident slice. -/
  bits : (i : I) → Fin (len i) → Bool
  /-- Private start address of each endpoint's resident bit slice. -/
  base : I → ℕ
  /-- Current bit offset shared by the endpoints of each demand or supply group. -/
  offset : A → ℕ

variable (reg : Registers I A r) (group : I → A) (port : A → Fin k)
  (width : A → ℕ) (x : Slices I A)

/-- Layout and cursors are resident before the scan and survive it intact. -/
structure Resident (c : Config w p r) : Prop where
  one : c.reg (reg .one) = 1
  base : ∀ i, c.reg (reg (.base i)) = (x.base i : Word w)
  dataEnd : ∀ i, c.reg (reg (.dataEnd i)) = ((x.base i + x.len i : ℕ) : Word w)
  offset : ∀ a, c.reg (reg (.offset a)) = (x.offset a : Word w)
  data : ∀ i (j : Fin (x.len i)), c.privateMem ((x.base i + j.val : ℕ) : Word w) =
    encodeBit w (x.bits i j)

/-- Full end and high cursor fit also for padded reads and malformed final totals. -/
structure Fits (w : ℕ) : Prop where
  width_le : ∀ a, width a ≤ w
  high : ∀ i, x.base i + x.offset (group i) + width (group i) < 2 ^ w
  dataEnd : ∀ i, x.base i + x.len i < 2 ^ w

/-- Frame on every register outside the scratch words and the current output fields. -/
def Frame (fs : List I) (c d : Config w p r) : Prop :=
  ∀ q, q ≠ reg .start → q ≠ reg .cursor → q ≠ reg .tmp →
    (∀ i ∈ fs, q ≠ reg (.query i)) → d.reg q = c.reg q

theorem resident_frame {fs : List I} {c d : Config w p r}
    (hr : Resident reg x c) (hf : Frame reg fs c d) (hm : d.privateMem = c.privateMem) :
    Resident reg x d := by
  constructor
  · rw [hf, hr.one] <;> simp
  · intro i
    rw [hf, hr.base] <;> simp
  · intro i
    rw [hf, hr.dataEnd] <;> simp
  · intro a
    rw [hf, hr.offset] <;> simp
  · intro i j
    rw [hm, hr.data]

/-- The natural digit stored in the word-sized query register. -/
def digit (i : I) : Word w :=
  (readField (x.bits i) (x.offset (group i)) (width (group i)) : Word w)

/-- The four setup instructions and the padded field loop for one endpoint. -/
theorem oneField (M : Machine w p r k) (i : I) (pc : Fin 4 → Fin p)
    (reader : Fin 7 → Fin p) (done : Fin p)
    (hl : ∀ l, M.code (pc l) = setup reg group port pc reader i l)
    (read : FieldRead.Linked M reader (readerRegs reg i) done)
    (hp : ∀ a, M.publicData (port a) = (width a : Word w)) (fit : Fits group width x w)
    (c : Config w p r) (hc : c.pc = pc 0) (hr : Resident reg x c) :
    ∃ d, Prefix M c (List.replicate (6 * width (group i) + 5) .tick) d ∧ d.pc = done ∧
      d.reg (reg (.query i)) = digit group width x i ∧ Frame reg [i] c d ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  let off := x.base i + x.offset (group i)
  let n := width (group i)
  let c₁ := c.put (pc 1) (reg .start) (off : Word w)
  let c₂ := c₁.put (pc 2) (reg .tmp) (n : Word w)
  let c₃ := c₂.put (pc 3) (reg .cursor) ((off + n : ℕ) : Word w)
  let c₄ := c₃.put (reader 0) (reg (.query i)) 0
  have step (l : Fin 4) (d : Config w p r) (h : d.pc = pc l) :
      M.program.step d = (setup reg group port pc reader i l).run M.publicData d := by
    simp [Machine.program, h, hl l]
  have h₀ : M.program.step c = .localStep c₁ := by
    rw [step 0 c hc]
    change CallAction.localStep (c.put _ _ (c.reg (reg (.base i)) + c.reg (reg (.offset _)))) = _
    simp [c₁, off, hr.base, hr.offset]
  have h₁ : M.program.step c₁ = .localStep c₂ := by
    rw [step 1 c₁ rfl]
    change CallAction.localStep (c₁.put _ _ (M.publicData _)) = _
    rw [hp]
  have h₂ : M.program.step c₂ = .localStep c₃ := by
    rw [step 2 c₂ rfl]
    change CallAction.localStep (c₂.put _ _ (c₂.reg (reg .start) + c₂.reg (reg .tmp))) = _
    simp [c₃, c₂, c₁, Config.put]
  have h₃ : M.program.step c₃ = .localStep c₄ := step 3 c₃ rfl
  obtain ⟨d, run, hd, hdigit, _, frame, hm, hper⟩ :=
    FieldRead.native_read read (x.bits i) (x.base i) (x.offset (group i)) n c₄ rfl
      (fit.width_le _) (fit.high i) (fit.dataEnd i)
      (by change c₄.reg (reg (.query i)) = 0; simp [c₄])
      (by change c₄.reg (reg .cursor) = _; simp [c₄, c₃, Config.put, off])
      (by change c₄.reg (reg .start) = _; simp [c₄, c₃, c₂, c₁, Config.put, off])
      (by change c₄.reg (reg (.dataEnd i)) = _; simp [c₄, c₃, c₂, c₁, Config.put, hr.dataEnd])
      (by change c₄.reg (reg .one) = _; simp [c₄, c₃, c₂, c₁, Config.put, hr.one]) (hr.data i)
  rw [meteredField_spec] at run
  refine ⟨d, ?_, hd, ?_, ?_, hm, hper⟩
  · have pre := Prefix.tick h₀ (.tick h₁ (.tick h₂ (.tick h₃ run)))
    convert pre using 1
    simp [n, List.replicate_succ]
  · apply Fin.ext
    rw [digit, Fin.val_natCast, Nat.mod_eq_of_lt]
    · exact hdigit
    · exact (readField_lt ..).trans_le (Nat.pow_le_pow_right (by decide) (fit.width_le _))
  · intro q hs hc ht hq
    have hqi := hq i (by simp)
    have keep := frame q hqi hc ht
    exact keep.trans (by simp [c₄, c₃, c₂, c₁, Config.put, hqi, hc, ht, hs])


/-- Each field's four setup rows and seven reader rows occupy fixed program counters. -/
structure Sites (I : Type*) (p : ℕ) where
  /-- Four program counters per endpoint for setting up its padded field read. -/
  setupPC : I → Fin 4 → Fin p
  /-- Seven program counters per endpoint for the padded reader that writes the query digit. -/
  readerPC : I → Fin 7 → Fin p

/-- Enter the setup block of the first field in the list, transferring directly to `stop` when
the list is empty. -/
def Sites.first (sites : Sites I p) (stop : Fin p) : List I → Fin p
  | [] => stop
  | i :: _ => sites.setupPC i 0

/-- Instruction-level links, with each field reader going straight to the next setup. -/
def Linked (M : Machine w p r k) (sites : Sites I p) (stop : Fin p) : List I → Prop
  | [] => True
  | i :: rest =>
    (∀ l, M.code (sites.setupPC i l) =
      setup reg group port (sites.setupPC i) (sites.readerPC i) i l) ∧
    FieldRead.Linked M (sites.readerPC i) (readerRegs reg i) (sites.first stop rest) ∧
    Linked M sites stop rest

/-- Every path for a selected base motif pays for exactly its fixed endpoint widths. -/
def steps (fs : List I) : ℕ := (fs.map fun i ↦ 6 * width (group i) + 5).sum

/-- All queried digits are simultaneously available at the lookup entry. Private bits,
resident geometry and every register outside the stated frame are preserved. -/
theorem native (M : Machine w p r k) (sites : Sites I p) (stop : Fin p) (fs : List I)
    (hl : Linked reg group port M sites stop fs)
    (hp : ∀ a, M.publicData (port a) = (width a : Word w))
    (fit : Fits group width x w) (c : Config w p r) (hc : c.pc = sites.first stop fs)
    (hr : Resident reg x c) :
    ∃ d, Prefix M c (List.replicate (steps group width fs) .tick) d ∧ d.pc = stop ∧
      (∀ i ∈ fs, d.reg (reg (.query i)) = digit group width x i) ∧
      Frame reg fs c d ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  classical
  induction fs generalizing c with
  | nil => exact ⟨c, .nil _, hc, by simp, fun _ _ _ _ _ ↦ rfl, rfl, rfl⟩
  | cons i rest ih =>
    obtain ⟨mid, pre, pc, val, frame, mem, per⟩ := oneField reg group port width x M i
      (sites.setupPC i) (sites.readerPC i) _ hl.1 hl.2.1 hp fit c hc hr
    obtain ⟨d, tail, hd, vals, frame', mem', per'⟩ :=
      ih hl.2.2 mid pc (resident_frame reg x hr frame mem)
    refine ⟨d, ?_, hd, ?_, ?_, mem'.trans mem, per'.trans per⟩
    · simpa only [steps, List.map_cons, List.sum_cons, List.replicate_add] using pre.append tail
    · intro j hj
      by_cases h : j ∈ rest
      · exact vals j h
      · have hj' : j = i := (List.mem_cons.mp hj).resolve_right h
        subst j
        apply (frame' _ (by simp) (by simp) (by simp) ?_).trans val
        intro k hk he
        exact h ((Slot.query.inj (reg.injective he)) ▸ hk)
    · intro q hs hc ht hq
      exact (frame' q hs hc ht fun i h ↦ hq i (List.mem_cons_of_mem _ h)).trans
        (frame q hs hc ht fun j h ↦ hq j (List.mem_cons.mpr (.inl (List.mem_singleton.mp h))))

end PairSimulation.MapRowFields

end VPVNP
end Computability
end OAI
