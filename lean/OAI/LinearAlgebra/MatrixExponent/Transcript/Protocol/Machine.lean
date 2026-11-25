import OAI.LinearAlgebra.MatrixExponent.Transcript.RAM.Calls
import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector
import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats

section
/-!
# From bit instructions on registers to a static bit graph

For each register, the compiler tracks the wire of its latest
assignment. Register contents and the addresses computed from them
remain input-dependent.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol

open Coloring RAM

abbrev BitRef (X : Type) (d : ℕ) := X ⊕ (Bool ⊕ Fin d)

/-- A single-bit assignment and memory access. -/
structure BitGate (X : Type) (w d : ℕ) where
  dst : Option (Fin d)
  address : slots (word w) → BitRef X d
  args : Fin 4 → BitRef X d
  op : (Fin 4 → Bool) → Bool → Bool × Bool

structure Config (w d : ℕ) where
  reg : Fin d → Bool
  mem : B w → Bool

variable {X : Type} {w d j : ℕ}

namespace BitGate

variable (g : BitGate X w d) (x : X → Bool) (s : Config w d)

def read (b : BitRef X d) : Bool := Sum.elim x (Sum.elim id s.reg) b

def addr : B w := Control.decode w (read x s ∘ g.address)

def result : Bool × Bool := g.op (read x s ∘ g.args) (s.mem (g.addr x s))

def step : Config w d where
  reg b := if g.dst = some b then (g.result x s).2 else s.reg b
  mem := Function.update s.mem (g.addr x s) (g.result x s).1

end BitGate

/-- Zero-initialized memory with a fixed initial register file. -/
structure Series (X : Type) (w d : ℕ) where
  initial : Fin d → Bool
  gate : ℕ → BitGate X w d

namespace Series

variable (C : Series X w d) (x : X → Bool)

def state : ℕ → Config w d
  | 0 => ⟨C.initial, fun _ => false⟩
  | n + 1 => (C.gate n).step x (state n)

def wires (j : ℕ) : ℕ → Fin d → Source X j
  | 0, b => .inr (.inl (C.initial b))
  | n + 1, b => if h : n < 2 ^ j ∧ (C.gate n).dst = some b then
      .inr (.inr ⟨n, h.1⟩) else wires j n b

private theorem wires_ready (i : B j) (n : ℕ) (hn : n ≤ i.val) (b : Fin d) :
    Available i (C.wires j n b) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [wires]
    split
    · change n < i.val
      omega
    · exact ih (by omega)

def source (i : B j) : BitRef X d → Source X j :=
  Sum.elim Sum.inl (Sum.elim (fun v => .inr (.inl v)) (C.wires j i.val))

private theorem ready (i : B j) (b : BitRef X d) : Available i (C.source i b) := by
  rcases b with b|b|b
  · trivial
  · trivial
  · exact C.wires_ready i i.val le_rfl b

def program (j : ℕ) : Program X j w 4 where
  address i := C.source i ∘ (C.gate i.val).address
  args i := C.source i ∘ (C.gate i.val).args
  instruction i := (C.gate i.val).op
  address_ready i _ := C.ready i _
  args_ready i _ := C.ready i _

private def memory (j n : ℕ) :=
  cells ((C.program j).tape x ((C.program j).run x)) n

private def Agrees (j n : ℕ) : Prop :=
  (∀ b, (C.program j).eval x (C.wires j n b) = (C.state x n).reg b) ∧
  C.memory x j n = (C.state x n).mem

private theorem row (i : B j) (h : C.Agrees x j i.val) :
    (C.program j).addr x ((C.program j).run x) i = (C.gate i.val).addr x (C.state x i.val) ∧
    ((C.program j).run x i 1, (C.program j).run x i 2) =
      (C.gate i.val).result x (C.state x i.val) := by
  let P := C.program j
  have hs (b : BitRef X d) : P.eval x (C.source i b) = BitGate.read x (C.state x i.val) b := by
    rcases b with b|b|b
    · rfl
    · rfl
    · exact h.1 b
  have ha : P.addr x (P.run x) i = (C.gate i.val).addr x (C.state x i.val) :=
    congrArg (Control.decode w) (funext (fun b => hs ((C.gate i.val).address b)))
  have hb : signal x (P.run x) ∘ P.args i = BitGate.read x (C.state x i.val) ∘
      (C.gate i.val).args := funext (fun b => hs _)
  have hm := (P.run_obeys x).1 i
  change P.run x i 0 = C.memory x j i.val (P.addr x (P.run x) i) at hm
  refine ⟨ha, ?_⟩
  change (P.run x i 1, P.run x i 2) = _
  rw [(P.run_obeys x).2 i, hb, hm, h.2, ha]
  rfl

private theorem agrees (n : ℕ) (hn : n ≤ 2 ^ j) : C.Agrees x j n := by
  induction n with
  | zero => exact ⟨fun _ => rfl, rfl⟩
  | succ n ih =>
    have hl : n < 2 ^ j := by omega
    have h := ih hl.le
    obtain ⟨ha, hg⟩ := C.row x ⟨n, hl⟩ h
    constructor
    · intro b
      simp only [wires, state, BitGate.step]
      by_cases he : (C.gate n).dst = some b
      · rw [dite_eq_left ⟨hl, he⟩, ite_eq_left he]
        exact congrArg Prod.snd hg
      · rw [dite_eq_right (fun h => he h.2), ite_eq_right he]
        exact h.1 b
    · have hv : (C.program j).run x ⟨n, hl⟩ 1 = ((C.gate n).result x (C.state x n)).1 :=
        congrArg Prod.fst hg
      rw [memory, cells, dite_eq_left hl]
      change Function.update (C.memory x j n) ((C.program j).addr x ((C.program j).run x) ⟨n, hl⟩)
        ((C.program j).run x ⟨n, hl⟩ 1) = _
      rw [h.2, ha, hv]
      rfl

theorem eval_wire (i : B j) :
    (C.program j).eval x (.inr (.inr i)) = ((C.gate i.val).result x (C.state x i.val)).2 :=
  congrArg Prod.snd (C.row x i (C.agrees x i.val i.isLt.le)).2

end Series
end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

/-! # Matching private inputs with static names -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Private

open Coloring

abbrev format (D : Format) (H : ℕ) := Format.pair .bit (.pair (.addr H) D)

abbrev Pins (S : Type) (P H : ℕ) (D : Format) :=
  (Fin P × D.pins) ⊕ (S × (format D H).pins)

/-- Each static input has one active reader and every active reader gets the named input. -/
def good {S : Type} {P H : ℕ} {D : Format} (f : Fin P → D.obj)
    (g : S → (format D H).obj) : Prop :=
  (∀ p : Fin P, ∃! s : S, (g s).1 = true ∧ (g s).2.1.val = p.val) ∧
    ∀ s : S, (g s).1 = true → ∃ p : Fin P, (g s).2.1.val = p.val ∧ (g s).2.2 = f p

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Private
end

section
/-! # Size of a bit-RAM schedule padded to a power of two -/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol

/-- Read and write the external bits one at a time and run a block of
`g` gates per controller step. An empty schedule gets one padding row. -/
def clock (i o k g : ℕ) := Nat.clog 2 (i + 2 ^ k * g + o)

theorem clock_ge (i o k g : ℕ) : i + 2 ^ k * g + o ≤ 2 ^ clock i o k g :=
  Nat.le_pow_clog (by decide) _

theorem clock_time (i o k g : ℕ) : 2 ^ clock i o k g ≤ 2 * (i + 2 ^ k + o) * (1 + g) := by
  have h : i + 2 ^ k * g + o ≤ (i + 2 ^ k + o) * (1 + g) := by
    simp only [mul_add, add_mul, mul_one]
    have : 0 < (2 : ℕ) ^ k := by positivity
    omega
  rw [mul_assoc]
  exact (Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 h)).trans
    (pow_clog_le_twice (by positivity))

theorem clock_bits (i o k g w : ℕ) (hi : i ≤ 2 ^ w) (ho : o ≤ 2 ^ w) :
    clock i o k g ≤ 2 + w + k + g := by
  apply Nat.clog_le_of_le_pow
  have hw : (2 : ℕ) ^ w ≤ 2 ^ (w + k + g) := Nat.pow_le_pow_right (by decide) (by omega)
  have hm : 2 ^ k * g ≤ 2 ^ (w + k + g) := by
    rw [pow_add]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by omega)) Nat.lt_two_pow_self.le
  rw [show 2 + w + k + g = 2 + (w + k + g) by omega, pow_add]
  omega

/-- The trivalent verification expense includes the fixed overhead even
when the external ports or the gate block are empty. -/
theorem clock_expense (i o k g w : ℕ) (hi : i ≤ 2 ^ w) (ho : o ≤ 2 ^ w) :
    RAM.Program.expense (clock i o k g) w 4 ≤ (i + 2 ^ k + o) * (100 + w + k + g) ^ 210 := by
  let V := i + 2 ^ k + o
  let K := 100 + w + k + g
  let j := clock i o k g
  have hK : 100 ≤ K := by unfold K; omega
  have hV : 0 < V := by unfold V; positivity
  have hj : j ≤ 2 + w + k + g := clock_bits i o k g w hi ho
  have ht : 2 ^ j ≤ V * K ^ 2 := calc
    _ ≤ 2 * V * (1 + g) := clock_time i o k g
    _ = V * (2 * (1 + g)) := by ac_rfl
    _ ≤ V * K ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by unfold K; omega))
  have hb : 100 + j + w ≤ K ^ 2 := calc
    _ ≤ 2 * K := by unfold K; omega
    _ ≤ K ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ (by omega)
  have hpow : (100 + j + w) ^ 100 ≤ K ^ 200 := by
    have h := Nat.pow_le_pow_left hb 100
    rw [← pow_mul] at h
    exact h
  have hlarge : 4103 ≤ K ^ 2 :=
    (show 4103 ≤ 100 ^ 2 by decide).trans (Nat.pow_le_pow_left hK _)
  have hg : 3 + 4 * (100 + j + w) ^ 100 + 32 * 2 ^ (4 + 3) ≤ K ^ 202 := calc
    _ ≤ 4103 * K ^ 200 := by
      have h : 0 < K ^ 200 := pow_pos (by omega) _
      omega
    _ ≤ K ^ 2 * K ^ 200 := Nat.mul_le_mul_right _ hlarge
    _ = _ := by rw [← pow_add]
  change 2 ^ j * _ + 130 ≤ V * K ^ 210
  calc
    _ ≤ V * K ^ 2 * K ^ 202 + 130 := Nat.add_le_add_right (Nat.mul_le_mul ht hg) _
    _ = V * K ^ 204 + 130 := by rw [mul_assoc, ← pow_add]
    _ ≤ V * K ^ 204 * 131 := by
      have h : 0 < V * K ^ 204 := Nat.mul_pos hV (pow_pos (by omega) _)
      omega
    _ ≤ V * K ^ 204 * K ^ 6 := Nat.mul_le_mul_left _
      ((show 131 ≤ K ^ 2 by omega).trans (Nat.pow_le_pow_right (by omega) (by decide)))
    _ = _ := by rw [mul_assoc, ← pow_add]

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

section
/-!
# A finite adaptive controller

One cycle runs a fixed circuit of single-bit register assignments.
Besides two ordinary inputs, a gate can access and update one memory
bit. Addresses are wired from current registers or constants. The
register word can hold a program counter, branch tests and scratch
bits. Setting the designated halt bit freezes both registers and memory.

Before the cycles, input bits are written in a fixed enumeration.
Afterwards, one gate reads each designated output cell.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol

open Coloring

variable {X Y : Type} {w d : ℕ}

/-- Each assignment may reuse the output of any earlier assignment
by reading its destination register. -/
structure Command (w d : ℕ) where
  dst : Fin d
  address : slots (word w) → Bool ⊕ Fin d
  left : Bool ⊕ Fin d
  right : Bool ⊕ Fin d
  op : Bool → Bool → Bool → Bool × Bool

namespace Command

def gate (c : Command w d) (halt : Fin d) : BitGate X w d where
  dst := some c.dst
  address := Sum.inr ∘ c.address
  args := ![.inr c.left, .inr c.right, .inr (.inr c.dst), .inr (.inr halt)]
  op a b := if a 3 then (b, a 2) else c.op (a 0) (a 1) b

def apply (c : Command w d) (halt : Fin d) (s : Config w d) : Config w d :=
  if s.reg halt then s else
  let rd := Sum.elim id s.reg
  let a := Control.decode w (rd ∘ c.address)
  let v := c.op (rd c.left) (rd c.right) (s.mem a)
  ⟨Function.update s.reg c.dst v.2, Function.update s.mem a v.1⟩

theorem gate_step (c : Command w d) (halt : Fin d) (s : Config w d) (x : X → Bool) :
    (c.gate halt).step x s = c.apply halt s := by
  let a := Control.decode w (Sum.elim id s.reg ∘ c.address)
  let v := c.op (Sum.elim id s.reg c.left) (Sum.elim id s.reg c.right) (s.mem a)
  let u := if s.reg halt then (s.mem a, s.reg c.dst) else v
  change Config.mk (fun b => if some c.dst = some b then u.2 else s.reg b)
    (Function.update s.mem a u.1) =
    if s.reg halt then s else Config.mk (Function.update s.reg c.dst v.2)
      (Function.update s.mem a v.1)
  have hr : (fun b => if some c.dst = some b then u.2 else s.reg b) =
      Function.update s.reg c.dst u.2 := by
    funext b
    by_cases h : b = c.dst
    · subst b; simp
    · simp [h, Ne.symm h]
  rw [hr]
  by_cases h : s.reg halt = true <;> simp [u, h]

end Command

structure Controller (X Y : Type) (w : ℕ) where
  registers : ℕ
  initial : Fin registers → Bool
  halt : Fin registers
  size : ℕ
  circuit : Fin size → Command w registers
  input : X → B w
  output : Y → B w

namespace Controller

variable [Fintype X] [Fintype Y] (M : Controller X Y w)

def time (k : ℕ) := clock (Fintype.card X) (Fintype.card Y) k M.size

abbrev State := Config w M.registers

private def access (a : B w) (z : Option X) : BitGate X w d where
  dst := none
  address p := .inr (.inl ((Control.decode w).symm a p))
  args _ := z.elim (.inr (.inl false)) Sum.inl
  op pins old := (if z.isSome then pins 0 else old, old)

omit [Fintype X] in
private theorem access_addr (a : B w) (z : Option X) (x : X → Bool) (s : Config w d) :
    (access a z).addr x s = a :=
  (Control.decode w).apply_symm_apply a

omit [Fintype X] in
private theorem access_read (a : B w) (x : X → Bool) (s : Config w d) :
    (access a none).step x s = s ∧ ((access a none).result x s).2 = s.mem a := by
  simp only [BitGate.step, BitGate.result, access_addr]
  simp [access]

omit [Fintype X] in
private theorem access_write (a : B w) (z : X) (x : X → Bool) (s : Config w d) :
    (access a (some z)).step x s = ⟨s.reg, Function.update s.mem a (x z)⟩ := by
  simp only [BitGate.step, BitGate.result, access_addr]
  rfl

/-- If input addresses coincide the last write wins. -/
noncomputable def load (x : X → Bool) : ℕ → M.State
  | 0 => ⟨M.initial, fun _ => false⟩
  | n + 1 => if h : n < Fintype.card X then
      let z := (Fintype.equivFin X).symm ⟨n, h⟩
      let s := load x n
      ⟨s.reg, Function.update s.mem (M.input z) (x z)⟩
    else load x n

def partialCycle (s : M.State) : ℕ → M.State
  | 0 => s
  | n + 1 => if h : n < M.size then (M.circuit ⟨n, h⟩).apply M.halt (partialCycle s n)
    else partialCycle s n

def cycle (s : M.State) : M.State := M.partialCycle s M.size

omit [Fintype X] [Fintype Y] in
theorem halted (s : M.State) (hs : s.reg M.halt = true) : M.cycle s = s := by
  suffices ∀ n, M.partialCycle s n = s from this M.size
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [partialCycle, ih, Command.apply, hs]

noncomputable def run (x : X → Bool) : ℕ → M.State
  | 0 => M.load x (Fintype.card X)
  | n + 1 => M.cycle (run x n)

omit [Fintype Y] in
theorem loaded (hi : Function.Injective M.input) (x : X → Bool) (z : X) :
    (M.run x 0).mem (M.input z) = x z := by
  let e := Fintype.equivFin X
  suffices ∀ n ≤ Fintype.card X, (e z).val < n → (M.load x n).mem (M.input z) = x z from
    this _ le_rfl (e z).isLt
  intro n hn hz
  induction n with
  | zero => omega
  | succ n ih =>
    have hl : n < Fintype.card X := by omega
    rw [load, dite_eq_left hl]
    let a := e.symm ⟨n, hl⟩
    change Function.update (M.load x n).mem (M.input a) (x a) (M.input z) = x z
    by_cases h : z = a
    · rw [h, Function.update_self]
    · rw [Function.update_of_ne (hi.ne h)]
      have hv : (e z).val ≠ n := by
        intro he
        exact h (e.injective ((Fin.ext he).trans (e.apply_symm_apply _).symm))
      exact ih hl.le (by omega)

omit [Fintype Y] in
theorem uninitialized (a : B w) (ha : ∀ z, M.input z ≠ a) (x : X → Bool) :
    (M.run x 0).mem a = false := by
  suffices ∀ n ≤ Fintype.card X, (M.load x n).mem a = false from this _ le_rfl
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    have hl : n < Fintype.card X := by omega
    simp only [load, dite_eq_left hl, Function.update_of_ne (ha _).symm, ih hl.le]

omit [Fintype Y] in
theorem stays_halted (x : X → Bool) {t u : ℕ} (hle : t ≤ u)
    (hs : (M.run x t).reg M.halt = true) : M.run x u = M.run x t := by
  induction u, hle using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [run, ih, M.halted _ hs]

noncomputable def value (k : ℕ) (x : X → Bool) (y : Y) : Bool :=
  (M.run x (2 ^ k)).mem (M.output y)

private def start (t : ℕ) := Fintype.card X + t * M.size

noncomputable def series (k : ℕ) : Series X w M.registers where
  initial := M.initial
  gate n :=
    if h : n < Fintype.card X then
      let z := (Fintype.equivFin X).symm ⟨n, h⟩
      access (M.input z) (some z)
    else if h' : n < M.start (2 ^ k) ∧ 0 < M.size then
      (M.circuit ⟨(n - Fintype.card X) % M.size, Nat.mod_lt _ h'.2⟩).gate M.halt
    else if ho : n - M.start (2 ^ k) < Fintype.card Y then
      let y := (Fintype.equivFin Y).symm ⟨n - M.start (2 ^ k), ho⟩
      access (M.output y) none
    else access 0 none

noncomputable def program (k : ℕ) : RAM.Program X (M.time k) w 4 :=
  (M.series k).program (M.time k)

private noncomputable def position (k : ℕ) (y : Y) : B (M.time k) :=
  ⟨M.start (2 ^ k) + ((Fintype.equivFin Y) y).val,
    lt_of_lt_of_le (Nat.add_lt_add_left ((Fintype.equivFin Y) y).isLt _)
      (clock_ge _ _ _ _)⟩

noncomputable def tap (k : ℕ) (y : Y) : RAM.Source X (M.time k) :=
  .inr (.inr (M.position k y))

variable (k : ℕ) (x : X → Bool)

private theorem state_load (n : ℕ) (hn : n ≤ Fintype.card X) :
    (M.series k).state x n = M.load x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hl : n < Fintype.card X := by omega
    rw [Series.state, ih hl.le, load, dite_eq_left hl]
    simp only [series, dite_eq_left hl, access_write]

omit [Fintype Y] in
private theorem start_next (t : ℕ) : M.start (t + 1) = M.start t + M.size := by
  simp [start, Nat.add_mul, Nat.add_assoc]

private theorem gate_cycle (t n : ℕ) (ht : t < 2 ^ k) (hn : n < M.size) :
    (M.series k).gate (M.start t + n) = (M.circuit ⟨n, hn⟩).gate M.halt := by
  have ha : ¬M.start t + n < Fintype.card X := by unfold start; omega
  have hb : M.start t + n < M.start (2 ^ k) ∧ 0 < M.size := by
    have h := Nat.add_le_add_left (Nat.mul_le_mul_right M.size ht) (Fintype.card X)
    change M.start (t + 1) ≤ M.start (2 ^ k) at h
    rw [start_next] at h
    omega
  have hv : (M.start t + n - Fintype.card X) % M.size = n := by
    rw [start, Nat.add_assoc, Nat.add_sub_cancel_left]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hn]
  simp only [series, dite_eq_right ha, dite_eq_left hb, hv]

private theorem state_cycle (t n : ℕ) (ht : t < 2 ^ k) (hn : n ≤ M.size) :
    (M.series k).state x (M.start t + n) =
      M.partialCycle ((M.series k).state x (M.start t)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hl : n < M.size := by omega
    rw [← Nat.add_assoc, Series.state, gate_cycle _ _ _ _ ht hl, Command.gate_step,
      ih hl.le, partialCycle, dite_eq_left hl]

private theorem state_run (t : ℕ) (ht : t ≤ 2 ^ k) :
    (M.series k).state x (M.start t) = M.run x t := by
  induction t with
  | zero => simpa [start, run] using M.state_load k x _ le_rfl
  | succ t ih =>
    have hl : t < 2 ^ k := by omega
    rw [start_next, state_cycle _ _ _ _ _ hl le_rfl, ih hl.le, run, cycle]

private theorem gate_output (n : ℕ) (hn : n < Fintype.card Y) :
    (M.series k).gate (M.start (2 ^ k) + n) =
      access (M.output ((Fintype.equivFin Y).symm ⟨n, hn⟩)) none := by
  have ha : ¬M.start (2 ^ k) + n < Fintype.card X := by unfold start; omega
  have hb : ¬(M.start (2 ^ k) + n < M.start (2 ^ k) ∧ 0 < M.size) := by omega
  simp only [series, dite_eq_right ha, dite_eq_right hb, Nat.add_sub_cancel_left, dite_eq_left hn]

private theorem state_output (n : ℕ) (hn : n ≤ Fintype.card Y) :
    (M.series k).state x (M.start (2 ^ k) + n) = M.run x (2 ^ k) := by
  induction n with
  | zero => exact M.state_run k x _ le_rfl
  | succ n ih =>
    have hl : n < Fintype.card Y := by omega
    rw [← Nat.add_assoc, Series.state, gate_output _ _ _ hl, (access_read _ _ _).1, ih hl.le]

/-- Every tap sees the designated cell after exactly the specified number of cycles. -/
theorem correct (y : Y) : (M.program k).eval x (M.tap k y) = M.value k x y := by
  rw [program, tap, Series.eval_wire]
  let p := (Fintype.equivFin Y) y
  change (((M.series k).gate (M.start (2 ^ k) + p.val)).result x
    ((M.series k).state x (M.start (2 ^ k) + p.val))).2 = _
  rw [gate_output _ _ _ p.isLt, state_output _ _ _ _ p.isLt.le, (access_read _ _ _).2]
  change (M.run x (2 ^ k)).mem (M.output ((Fintype.equivFin Y).symm p)) = _
  simp [p, value]

theorem time_bound : 2 ^ M.time k ≤ 2 * (Fintype.card X + 2 ^ k + Fintype.card Y) * (1 + M.size) :=
  clock_time _ _ _ _

theorem width_bound (hi : Fintype.card X ≤ 2 ^ w) (ho : Fintype.card Y ≤ 2 ^ w) :
    M.time k ≤ 2 + w + k + M.size :=
  clock_bits _ _ _ _ _ hi ho

theorem expense (hi : Fintype.card X ≤ 2 ^ w) (ho : Fintype.card Y ≤ 2 ^ w) :
    RAM.Program.expense (M.time k) w 4 ≤
      (Fintype.card X + 2 ^ k + Fintype.card Y) * (100 + w + k + M.size) ^ 210 :=
  clock_expense _ _ _ _ _ hi ho

end Controller
end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

/-! # A local charge class and its dictionary seats -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol

open Coloring Install
open scoped Classical

abbrev Output (t U : ℕ) := Unit ⊕ Σ s : RAM.Calls t U, (RAM.token s.1.val).pins

variable {F X : Type} [Field F] {t U : ℕ}

def localValue (W : List Bool → F) (f : (X → Bool) → Output t U → Bool) (x : X → Bool) : F :=
  if f x (.inl ()) then ∏ s : RAM.Calls t U, RAM.tokenValue U W s.1.val
    ((RAM.token s.1.val).code.symm (fun j => f x (.inr ⟨s, j⟩))) else 0

/-- The mask identifies bits private to the processor. On an unused
seat these have a unique extension, while shared bits remain free. -/
def activeValue (W : List Bool → F) (f : (X → Bool) → Output t U → Bool)
    (on : X) (mask : X → Bool) (x : X → Bool) : F :=
  if x on then localValue W f x else if ∀ i, mask i = true → x i = false then 1 else 0

private theorem token_width (b : ℕ) : (RAM.token b).width ≤ 4 * 2 ^ b := by
  simp only [RAM.token, Format.width_pair, Format.width_vec]
  rw [Format.width_bit, Format.width_addr]
  have := Nat.lt_two_pow_self (n := b)
  omega

theorem card_output (t U : ℕ) : Fintype.card (Output t U) ≤ 1 + 8 * (RAM.ceiling U + 1) * t := by
  rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_sigma]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ s : RAM.Calls t U, 4 * capacity s := Finset.sum_le_sum fun s _ => token_width s.1.val
    _ = 4 * ∑ s : RAM.Calls t U, capacity s := by rw [Finset.mul_sum]
    _ ≤ 4 * ((RAM.ceiling U + 1) * (2 * t)) := Nat.mul_le_mul_left _ (sum_capacity _ _ _)
    _ = _ := by ring

variable (U : ℕ) (W : List Bool → F)

def enabledToken (b : ℕ) (x : Option (RAM.token b).pins → Bool) : F :=
  if x none then RAM.tokenValue U W b ((RAM.token b).code.symm (x ∘ some)) else 1

private def sites (b : ℕ) : Option (RAM.token b).pins ≃ slots (word ((RAM.token b).width + 1)) :=
  Fintype.equivOfCardEq (by simp [Format.width]; omega)

/-- One label per capacity, independent of the processor, its mask and its time budget. -/
def label (b : ℕ) : Table F :=
  ⟨word ((RAM.token b).width + 1), .unit, fun x _ =>
    enabledToken U W b (bits (word ((RAM.token b).width + 1)) x ∘ sites b)⟩

def labels : Set (Table F) := label U W '' Set.Iic (RAM.ceiling U)

theorem label_cost {b : ℕ} (hb : b ≤ RAM.ceiling U) :
    WideWeight F (10 * (U + 1)) (labels U W) (enabledToken U W b) (6 * 2 ^ b) := by
  have h₁ : 2 ^ b ≤ 2 * (U + 1) :=
    (Nat.pow_le_pow_right (by decide) hb).trans (pow_clog_le_twice (by omega))
  have hw := token_width b
  let a := word ((RAM.token b).width + 1)
  let f := fun (x : Val a) (_ : Val .unit) => enabledToken U W b (bits a x ∘ sites b)
  have hn : Wide F (10 * (U + 1)) (labels U W) a .unit f (1 + wd a) := by
    apply Wide.table
    · simp only [a, wd_word, wd, add_zero]
      omega
    · exact .inr ⟨b, hb, rfl⟩
  intro c e
  refine ⟨1 + wd a, ?_, ?_⟩
  · rw [show wd a = (RAM.token b).width + 1 from wd_word _]
    have := Nat.two_pow_pos b
    omega
  · simpa [f, Function.comp_def] using hn.pre (rewire_reindex ((sites b).symm.trans e))

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end
