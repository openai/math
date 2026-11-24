import OAI.Computability.VPVNP.PairSimulationLeafStartup
import OAI.Computability.VPVNP.PairSimulationPrivateFields
import OAI.Computability.VPVNP.PairSimulationStackMemory
import OAI.Computability.VPVNP.LiveHeaderBits

/-!
# Native private writes for the virtual validator's scalar stack fields

A six-row loop writes one private word per stack cell, in increasing address
order. For a binary word the loop counts down the bit position. For a unary
tally it writes the low bit of the unchanged input word on each iteration.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafScalarLoad

open BurstRAM PrivateRAM PrimedInputRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- Select either the successive bits of a binary word or repeated copies of its low bit for a
unary tally. -/
inductive Mode where | binary | tally deriving DecidableEq

/-- Read bit index `i` of the source word in binary mode, or bit zero in tally mode. -/
def bit (mode : Mode) (value : Word w) (i : ℕ) : Bool :=
  value.val.testBit (if mode = .tally then 0 else i)

/-- Order in private memory, starting at the port base. -/
def payload (mode : Mode) (value : Word w) : ℕ → List Bool
  | 0 => []
  | len+1 => bit mode value len :: payload mode value len

@[simp] theorem payload_length (mode : Mode) (value : Word w) (len : ℕ) :
    (payload mode value len).length = len := by induction len <;> simp_all [payload]

private theorem payload_get (mode : Mode) (value : Word w) (len : ℕ)
    (i : ℕ) (hi : i < len) :
    (payload mode value len)[i]'(by simpa using hi) = bit mode value (len-1-i) := by
  induction len generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [payload]
    | succ i =>
      simp only [payload, List.getElem_cons_succ]
      exact (ih i (by omega)).trans (by congr 1; omega)

theorem payload_word {a : ℕ} (v : Word a) (value : Word w) (h : value.val = v.val) :
    payload .binary value a = (wordBits v).reverse := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  rw [payload_get .binary value a i (by simpa using hi), List.getElem_reverse]
  simp only [wordBits, List.length_ofFn, List.getElem_ofFn, bit, reduceCtorEq, ↓reduceIte, h]
  exact LiveHeader.testBit_wordBits v ⟨a-1-i,by simp at hi; omega⟩

theorem payload_tally (len : ℕ) (hw : 0 < w) :
    payload .tally (1 : Word w) len = List.replicate len true := by
  induction len with
  | zero => rfl
  | succ n ih => simp [payload, bit, ih, hw, List.replicate_succ]

/-- Registers hold destination, remaining length, value, zero, one and scratch. -/
def instruction (mode : Mode) (pc : Fin 6 → Fin p) (reg : Fin 6 ↪ Fin r) (done : Fin p) :
    Fin 6 → Instr w p r k :=
  ![.jumpEq (reg 1) (reg 3) done (pc 1),
    .binary .sub (reg 1) (reg 1) (reg 4) (pc 2),
    .binary .shiftRight (reg 5) (reg 2) (reg (if mode = .tally then 3 else 1)) (pc 3),
    .binary .bitAnd (reg 5) (reg 5) (reg 4) (pc 4),
    .storePrivate (reg 0) (reg 5) (pc 5), .binary .add (reg 0) (reg 0) (reg 4) (pc 0)]

theorem resize_instruction (mode : Mode) (pc : Fin 6 → Fin p) (reg : Fin 6 ↪ Fin r)
    (done : Fin p) (i : Fin 6) : (instruction (w := 1) (k := k) mode pc reg done i).resize w =
      instruction mode pc reg done i := by fin_cases i <;> rfl

/-- The six host instructions at the designated labels implement the scalar write loop for the
chosen mode and continuation. -/
def Linked (M : Machine w p r k) (mode : Mode) (pc : Fin 6 → Fin p) (reg : Fin 6 ↪ Fin r) (done : Fin p) :=
  ∀ i, M.code (pc i) = instruction mode pc reg done i

variable {mode : Mode} {M : Machine w p r k} {pc : Fin 6 → Fin p} {reg : Fin 6 ↪ Fin r} {done : Fin p}

/-- The scalar loop exits at its continuation with all bits stored starting at `dst`, the
destination advanced and the remaining count zero. Only its destination, count and
temporary registers can change. -/
structure Result (reg : Fin 6 ↪ Fin r) (done : Fin p) (c out : Config w p r) (dst : ℕ) (xs : List Bool) : Prop where
  pc : out.pc = done
  destination : out.reg (reg 0) = ((dst+xs.length : ℕ) : Word w)
  remaining : out.reg (reg 1) = 0
  frame : ∀ i, i ≠ reg 0 → i ≠ reg 1 → i ≠ reg 5 → out.reg i = c.reg i
  memory : out.privateMem = PrivateFields.storeBits dst xs c.privateMem
  persistent : out.persistent = c.persistent

private theorem step_at (hl : Linked M mode pc reg done) (i : Fin 6) (c : Config w p r) (h : c.pc = pc i) :
    M.program.step c = (instruction mode pc reg done i).run M.publicData c := by
  change (M.code c.pc).run _ _ = _
  rw [h,hl i]

private theorem iteration (hl : Linked M mode pc reg done) (hw : 0 < w) (c : Config w p r)
    (hc : c.pc = pc 0) (n : ℕ) (fit : n+1 < 2^w) (hlen : c.reg (reg 1) = ((n+1 : ℕ) : Word w))
    (hz : c.reg (reg 3) = 0) (ho : c.reg (reg 4) = 1) :
    ∃ next, Prefix M c (List.replicate 6 .tick) next ∧ next.pc = pc 0 ∧
      next.reg (reg 0) = c.reg (reg 0)+1 ∧ next.reg (reg 1) = (n : Word w) ∧
      (∀ i, i ≠ reg 0 → i ≠ reg 1 → i ≠ reg 5 → next.reg i = c.reg i) ∧
      next.privateMem = Function.update c.privateMem (c.reg (reg 0)) (encodeBit w (bit mode (c.reg (reg 2)) n)) ∧
      next.persistent = c.persistent := by
  let c₁ := {c with pc := pc 1}
  let c₂ := c₁.put (pc 2) (reg 1) (n : Word w)
  let shift := (if mode = .tally then 0 else n : ℕ)
  let shifted :=  BinaryOp.shiftRight.eval (c.reg (reg 2)) (shift : Word w)
  let c₃ := c₂.put (pc 3) (reg 5) shifted
  let b := encodeBit w (bit mode (c.reg (reg 2)) n)
  let c₄ := c₃.put (pc 4) (reg 5) b
  let c₅ := c₄.store (pc 5) (c.reg (reg 0)) b
  let next := c₅.put (pc 0) (reg 0) (c.reg (reg 0)+1)
  have ne : c.reg (reg 1) ≠ c.reg (reg 3) := by
    rw [hlen,hz]
    intro he
    have eq := congrArg Fin.val he
    change (n+1) % (2^w) = 0 at eq
    rw [Nat.mod_eq_of_lt fit] at eq
    omega
  have hshift : shift < 2^w := by dsimp [shift]; split <;> omega
  have hbit : BinaryOp.bitAnd.eval shifted 1 = b := by
    rw [show BinaryOp.bitAnd.eval shifted 1 = _ from Opcodes.readBit_word hw (c.reg (reg 2)) (shift : Word w)]
    simp only [Fin.val_natCast, Nat.mod_eq_of_lt hshift, b, bit, shift]
  have s₀ : M.program.step c = .localStep c₁ := by rw [step_at hl 0 c hc]; simp [instruction, Instr.run, ne, c₁]
  have s₁ : M.program.step c₁ = .localStep c₂ := by
    rw [step_at hl 1 c₁ rfl]; simp [instruction, Instr.run, c₁, c₂, BinaryOp.eval, hlen,ho]
  have s₂ : M.program.step c₂ = .localStep c₃ := by
    rw [step_at hl 2 c₂ rfl]
    cases mode <;> simp [instruction, Instr.run, c₁,c₂,c₃,Config.put,shift,shifted,hz]
  have s₃ : M.program.step c₃ = .localStep c₄ := by
    rw [step_at hl 3 c₃ rfl]
    simp [instruction,Instr.run,c₁,c₂,c₃,c₄,Config.put,ho,hbit]
  have s₄ : M.program.step c₄ = .localStep c₅ := by
    rw [step_at hl 4 c₄ rfl]; simp [instruction,Instr.run,c₁,c₂,c₃,c₄,c₅,Config.put]
  have s₅ : M.program.step c₅ = .localStep next := by
    rw [step_at hl 5 c₅ rfl]; simp [instruction,Instr.run,c₁,c₂,c₃,c₄,c₅,next,Config.put,Config.store,BinaryOp.eval,ho]
  refine ⟨next,.tick s₀ (.tick s₁ (.tick s₂ (.tick s₃ (.tick s₄ (.tick s₅ (.nil _)))))), rfl,?_,?_,?_,rfl,rfl⟩
  · simp [next,Config.put]
  · simp [next,c₅,c₄,c₃,c₂,Config.store,Config.put]
  · intro i h₀ h₁ h₅
    simp [next,c₅,c₄,c₃,c₂,c₁,Config.put,Config.store,Function.update_of_ne h₀,
      Function.update_of_ne h₁, Function.update_of_ne h₅]

/-- All writes are private. One terminal test and six native transitions
per cell suffice on every input value. -/
theorem load_prefix (hl : Linked M mode pc reg done) (hw : 0 < w) (n dst : ℕ) (value : Word w)
    (c : Config w p r) (hc : c.pc = pc 0) (hd : c.reg (reg 0) = (dst : Word w))
    (hlen : c.reg (reg 1) = (n : Word w)) (hv : c.reg (reg 2) = value)
    (hz : c.reg (reg 3) = 0) (ho : c.reg (reg 4) = 1) (fit : dst+n < 2^w) :
    ∃ out, Prefix M c (List.replicate (6*n+1) .tick) out ∧ Result reg done c out dst (payload mode value n) := by
  induction n generalizing c dst with
  | zero =>
    let out := {c with pc := done}
    have eq : c.reg (reg 1) = c.reg (reg 3) := hlen.trans hz.symm
    have step : M.program.step c = .localStep out := by
      rw [step_at hl 0 c hc]; simp [instruction,Instr.run,eq,out]
    exact ⟨out,.tick step (.nil _),rfl,hd,hlen,fun _ _ _ _ => rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨next,head,hn,hdst,hlen',frame,mem,hp⟩ := iteration hl hw c hc n (by omega) hlen hz ho
    have keep (j : Fin 6) (h₀ : j ≠ 0) (h₁ : j ≠ 1) (h₅ : j ≠ 5) :=
      frame (reg j) (reg.injective.ne h₀) (reg.injective.ne h₁) (reg.injective.ne h₅)
    obtain ⟨out, tail, res⟩ := ih (dst+1) next hn (by simp [hdst,hd]) hlen'
      ((keep 2 (by decide) (by decide) (by decide)).trans hv)
      ((keep 3 (by decide) (by decide) (by decide)).trans hz)
      ((keep 4 (by decide) (by decide) (by decide)).trans ho) (by omega)
    have run := head.append tail
    rw [← List.replicate_add, show 6+(6*n+1) = 6*(n+1)+1 by omega] at run
    refine ⟨out,run,res.pc,?_,res.remaining,fun i h₀ h₁ h₅ => (res.frame i h₀ h₁ h₅).trans (frame i h₀ h₁ h₅),
      ?_,res.persistent.trans hp⟩
    · simpa [Nat.add_assoc,Nat.add_comm 1] using res.destination
    · rw [res.memory,mem,hd,hv,payload,PrivateFields.storeBits]
      rfl

end PairSimulation.LeafScalarLoad

end VPVNP
end Computability
end OAI
