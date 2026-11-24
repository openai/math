import Mathlib.Tactic.Linarith
import OAI.Computability.VPVNP.CursorFieldOffsets
import OAI.Computability.VPVNP.PrimedCounterGuessWord

/-!
# Initial private registers for copying the virtual validator's incident vector

The 24 straight-line instructions compute the rectangular arc stride, the
triangular sorting-layer count, the four source bases, and the exclusive
end of the incident stack. Each arithmetic row is width independent.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafIncidentGeometry

open BurstRAM PrivateRAM PrimedCounter.GuessWord RAMLayout CursorRouting
open scoped Fin.CommRing

variable {W p r k D H w : ℕ}

/-- An incident-geometry assignment's right-hand side, drawn from a five-bit literal, a
register copy, or a binary operation on two registers. -/
inductive Operand where
  | literal (n : Fin 32) | copy (i : Fin 30) | binary (op : BinaryOp) (i j : Fin 30)

/-- One incident-geometry assignment pairing a destination in the thirty-register bank with its
right-hand side. -/
abbrev Line := Fin 30 × Operand

/-- The straight-line assignments that derive payload widths, the four argument-buffer bases,
and the incident stack endpoint from the raw geometry. -/
def rows : List Line :=
  [(3,.literal 1),(16,.literal 0),(12,.binary .sub 11 3),(14,.binary .shiftLeft 3 11),
   (5,.literal 8),(5,.binary .mul 5 21),(25,.literal 20),(25,.binary .mul 25 20),(25,.binary .mul 25 21),
   (28,.binary .add 11 3),(28,.binary .mul 28 11),(29,.literal 2),(28,.binary .div 28 29),
   (28,.binary .mul 28 25),(26,.binary .mul 11 5),(26,.binary .add 26 28),(27,.binary .add 28 5),
   (27,.binary .add 27 27),(7,.copy 22),(8,.binary .add 7 26),(9,.binary .add 8 26),
   (10,.binary .add 9 26),(24,.binary .add 23 27),(2,.copy 24)]

/-- Index of an instruction in the 24-row incident-geometry calculation. -/
abbrev Stage := Fin 24

/-- The program counter for the next geometry row, or the caller's continuation after the last
assignment. -/
def target (pc : Stage → Fin p) (done : Fin p) (i : Fin (rows.length+1)) :=
  if h : i.val < rows.length then pc ⟨i.val,h⟩ else done

/-- Compile a geometry assignment into a native constant, copy, or binary instruction with the
specified continuation. -/
def emit (reg : Fin 30 ↪ Fin r) (dst : Fin p) (l : Line) : Instr W p r k :=
  match l.2 with
  | .literal n => .constant (reg l.1) (n.val : Word W) dst
  | .copy i => .copy (reg l.1) (reg i) dst
  | .binary op i j => .binary op (reg l.1) (reg i) (reg j) dst

/-- The native instruction for a given geometry row, using the linked registers and the next
row's program counter. -/
def instruction (pc : Stage → Fin p) (reg : Fin 30 ↪ Fin r) (done : Fin p) (i : Stage) : Instr W p r k :=
  emit reg (target pc done i.succ) rows[i]

theorem resize_instruction (pc : Stage → Fin p) (reg : Fin 30 ↪ Fin r) (done : Fin p) (i : Stage) :
    (instruction (W := 5) (k := k) pc reg done i).resize W = instruction pc reg done i := by
  unfold instruction emit
  generalize rows[i] = l
  rcases l with ⟨dst,rhs⟩
  cases rhs with
  | literal v =>
    change Instr.constant _ (Fin.ofNat (2^W) (v.val % 32)) _ = .constant _ (v.val : Word W) _
    rw [Nat.mod_eq_of_lt v.isLt]; rfl
  | copy _ => rfl
  | binary _ _ _ => rfl

/-- The machine contains the compiled geometry instruction at every assigned row and uses the
specified continuation for the last one. -/
def Linked (M : Machine W p r k) (pc : Stage → Fin p) (reg : Fin 30 ↪ Fin r) (done : Fin p) :=
  ∀ i, M.code (pc i) = instruction pc reg done i

/-- Evaluate a geometry assignment's right-hand side on the current thirty-register word bank. -/
def Operand.eval (bank : Fin 30 → Word W) : Operand → Word W
  | .literal n => (n.val : Word W)
  | .copy i => bank i
  | .binary op i j => op.eval (bank i) (bank j)

private def assign (reg : Fin 30 ↪ Fin r) (bank : Fin r → Word W) (l : Line) :=
  Function.update bank (reg l.1) (l.2.eval (bank ∘ reg))

private theorem sequence (M : Machine W p r k) (reg : Fin 30 ↪ Fin r) (ls : List Line)
    (pc : Fin (ls.length+1) → Fin p) (hl : ∀ i : Fin ls.length, M.code (pc i.castSucc) = emit reg (pc i.succ) ls[i])
    (c : Config W p r) (hc : c.pc = pc 0) :
    Prefix M c (List.replicate ls.length .tick)
      {c with pc := pc (Fin.last ls.length),reg := ls.foldl (assign reg) c.reg} := by
  induction ls generalizing c with
  | nil =>
    change Prefix M c [] {c with pc := pc (Fin.last 0)}
    rw [show Fin.last 0 = 0 from rfl,← hc]; exact .nil c
  | cons l ls ih =>
    let mid := c.put (pc (Fin.succ 0)) (reg l.1) (l.2.eval (c.reg ∘ reg))
    have s : M.program.step c = .localStep mid := by
      change (M.code c.pc).run _ _ = _
      have row := hl 0
      change M.code (pc 0) = emit reg (pc (Fin.succ 0)) l at row
      rw [hc,row]; rcases l with ⟨dst,rhs⟩; cases rhs <;> rfl
    exact .tick s (ih (fun i => pc i.succ) (fun i => hl i.succ) mid rfl)

private theorem assign_at (reg : Fin 30 ↪ Fin r) (ls : List Line) (bank : Fin r → Word W) :
    ls.foldl (assign reg) bank ∘ reg =
      ls.foldl (fun b l => Function.update b l.1 (l.2.eval b)) (bank ∘ reg) := by
  induction ls generalizing bank with
  | nil => rfl
  | cons l ls ih =>
    rw [List.foldl_cons,List.foldl_cons,ih]; congr 1
    funext i
    by_cases h : i = l.1 <;> simp [h,assign]

private theorem assign_frame (reg : Fin 30 ↪ Fin r) (ls : List Line) (bank : Fin r → Word W) (i : Fin r)
    (outside : ∀ l ∈ ls, i ≠ reg l.1) : ls.foldl (assign reg) bank i = bank i := by
  induction ls generalizing bank with
  | nil => rfl
  | cons l ls ih =>
    rw [List.foldl_cons,ih _ (fun j hj => outside j (List.mem_cons_of_mem l hj)),assign,
      Function.update_of_ne (outside l (List.mem_cons_self ..))]

/-- The six input registers hold the dimension, site, bucket size, word width, argument base,
and stack base for the incident copy. -/
structure Ready (D H w site nodeBase stackBase : ℕ) (bank : Fin 30 → Word W) : Prop where
  dim : bank 11 = (D : Word W)
  site : bank 13 = (site : Word W)
  bucket : bank 20 = (H : Word W)
  width : bank 21 = (w : Word W)
  arena : bank 22 = (nodeBase : Word W)
  base : bank 23 = (stackBase : Word W)

/-- The geometry registers hold the derived counts, payload widths, four buffer bases, and
destination stack endpoint needed for the incident copy. -/
structure Prepared (D H w nodeBase stackBase : ℕ) (bank : Fin 30 → Word W) : Prop where
  one : bank 3 = 1
  zero : bank 16 = 0
  last : bank 12 = ((D-1 : ℕ) : Word W)
  count : bank 14 = ((2^D : ℕ) : Word W)
  successor : bank 5 = ((8*w : ℕ) : Word W)
  block : bank 25 = ((blockBits H w : ℕ) : Word W)
  arc : bank 26 = ((ramPayloadWidth D H w : ℕ) : Word W)
  size : bank 27 = ((RAMLayout.width D H w : ℕ) : Word W)
  base₀ : bank 7 = (nodeBase : Word W)
  base₁ : bank 8 = ((nodeBase+ramPayloadWidth D H w : ℕ) : Word W)
  base₂ : bank 9 = ((nodeBase+2*ramPayloadWidth D H w : ℕ) : Word W)
  base₃ : bank 10 = ((nodeBase+3*ramPayloadWidth D H w : ℕ) : Word W)
  top : bank 24 = ((stackBase+RAMLayout.width D H w : ℕ) : Word W)
  cursor : bank 2 = ((stackBase+RAMLayout.width D H w : ℕ) : Word W)

private theorem triangular_fit (D : ℕ) : D*(D+1)<2^(D+1) := by
  induction D with
  | zero => decide
  | succ d ih =>
    rcases d with _|d
    · decide
    · rcases d with _|d
      · decide
      · rw [pow_succ]
        have h : d+2+2 ≤ 2*(d+2) := by omega
        nlinarith

private theorem layers (D : ℕ) (hD : D < W) (hW : 2 ≤ W) :
    BinaryOp.div.eval (((D : Word W)+1)*(D : Word W)) 2 = ((layerCount D : ℕ) : Word W) := by
  have hfit := (triangular_fit D).trans_le (Nat.pow_le_pow_right (by decide : 0<2) hD)
  have hm : ((D : Word W)+1)*(D : Word W) = (((D+1)*D : ℕ) : Word W) := by push_cast; rfl
  have h2 : 2 < 2^W := (by decide : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) hW)
  have hval : (2 : Word W).val = 2 := Nat.mod_eq_of_lt h2
  have hnum : (((D+1)*D : ℕ) : Word W).val = (D+1)*D := Nat.mod_eq_of_lt (by simpa [Nat.mul_comm] using hfit)
  simp only [BinaryOp.eval,hm,hval,hnum,layerCount,Nat.choose_two_right,Nat.add_one_sub_one]
  rfl

private theorem site_count (D : ℕ) (hd : D<W) :
    BinaryOp.shiftLeft.eval (1 : Word W) (D : Word W) = ((2^D : ℕ) : Word W) := by
  have hf : D < 2^W := hd.trans (Nat.lt_two_pow_self (n := W))
  have hv : (D : Word W).val = D := Nat.mod_eq_of_lt hf
  have one : (1 : Word W).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega : W ≠ 0))
  simp only [BinaryOp.eval,hv,ite_eq_left hd,one,Nat.shiftLeft_eq,Nat.one_mul,Fin.ofNat_eq_cast]

private theorem eval_add (u v : Word W) : BinaryOp.add.eval u v = u+v := rfl
private theorem eval_mul (u v : Word W) : BinaryOp.mul.eval u v = u*v := rfl
private theorem eval_sub (u v : Word W) : BinaryOp.sub.eval u v = u-v := rfl

private theorem result (bank : Fin 30 → Word W) {site nodeBase stackBase : ℕ}
    (h : Ready D H w site nodeBase stackBase bank) (hD : 1≤D) (hW : D<W) :
    Prepared D H w nodeBase stackBase (rows.foldl (fun b l => Function.update b l.1 (l.2.eval b)) bank) := by
  have hl := layers D hW (by omega)
  have hc := site_count D hW
  have sub : ((D-1 : ℕ) : Word W) = (D : Word W)-1 := by rw [Nat.cast_sub hD,Nat.cast_one]
  constructor <;>
    simp (config := {decide := true}) [rows,Operand.eval,Function.update,eval_add,eval_mul,eval_sub,
      h.dim,h.width,h.bucket,h.arena,h.base,hl,hc,sub,blockBits,ramPayloadWidth,RAMLayout.width] <;> ring

/-- Exact deterministic prefix from the six caller-supplied geometry registers. -/
theorem run (M : Machine W p r k) (pc : Stage → Fin p) (reg : Fin 30 ↪ Fin r) (done : Fin p)
    (link : Linked M pc reg done) (c : Config W p r) (hc : c.pc = pc 0)
    {site nodeBase stackBase : ℕ} (ready : Ready D H w site nodeBase stackBase (c.reg ∘ reg))
    (hD : 1 ≤ D) (hW : D < W) :
    ∃ out, Prefix M c (List.replicate rows.length .tick) out ∧ out.pc = done ∧
      Prepared D H w nodeBase stackBase (out.reg ∘ reg) ∧ out.privateMem = c.privateMem ∧
      out.persistent = c.persistent ∧ ∀ i, (∀ l ∈ rows, i ≠ reg l.1) → out.reg i = c.reg i := by
  have h := sequence M reg rows (target pc done) (fun i => by
    have stepPC : target pc done i.castSucc = pc i := by
      simp [target,i.isLt]; congr 1
    rw [stepPC]; exact link i) c
    (by simpa [target, rows] using hc)
  let out : Config W p r := {c with pc := done,reg := rows.foldl (assign reg) c.reg}
  have endPC : target pc done (Fin.last rows.length) = done := by simp [target]
  rw [endPC] at h
  refine ⟨out,h,rfl,?_,rfl,rfl,assign_frame reg rows c.reg⟩
  change Prepared _ _ _ _ _ (rows.foldl (assign reg) c.reg ∘ reg)
  rw [assign_at]
  exact result _ ready hD hW

end PairSimulation.LeafIncidentGeometry

end VPVNP
end Computability
end OAI
