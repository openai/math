import OAI.Computability.VPVNP.RAMUniform
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log

/-!
# Linking finite native burst-RAM stages

Each call reads a stage tag at a designated public address. It then runs the
selected finite instruction table with fresh private memory and the original
persistent word. A continuing return stays in that stage. An accepting exit
can finish the entire program or store the next stage tag and return zero for
its first call. The tables have distinct program-counter spaces and share their
ordinary register and public-word spaces. Three extra registers hold the tag
address, its value, and a comparison or transfer literal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveStageLink

open BurstRAM BurstRAM.PrivateRAM

variable {d r k w : ℕ} {pcs : Fin d → ℕ}

/-- Two startup instructions, a tag scan, relocated component code, and three
post-accept instructions per possible transfer. -/
abbrev Label (pcs : Fin d → ℕ) := Fin 2 ⊕ (Fin (d + 1) ⊕ (Fin d ⊕
  (((i : Fin d) × Fin (pcs i)) ⊕ (Fin d × Fin 3))))

/-- Number of linked program counters for bootstrap, tag scan, tag comparisons, component
bodies, and three handoff positions per stage. -/
def codeSize (pcs : Fin d → ℕ) := 2 + ((d + 1) + (d + ((∑ i, pcs i) + d * 3)))

/-- A concrete numbering for the linked program, independent of the runtime word width. -/
def labelEquiv (pcs : Fin d → ℕ) : Label pcs ≃ Fin (codeSize pcs) :=
  let body := ((finSigmaFinEquiv (n := pcs)).sumCongr finProdFinEquiv).trans finSumFinEquiv
  let compare := ((Equiv.refl (Fin d)).sumCongr body).trans finSumFinEquiv
  let scan := ((Equiv.refl (Fin (d + 1))).sumCongr compare).trans finSumFinEquiv
  ((Equiv.refl (Fin 2)).sumCongr scan).trans finSumFinEquiv

/-- Linked program counter for one of the two bootstrap instructions. -/
def boot (pcs : Fin d → ℕ) (j : Fin 2) := labelEquiv pcs (.inl j)
/-- Linked program counter for a tag-scan position, including the terminal scan position after
all stages. -/
def scan (pcs : Fin d → ℕ) (j : Fin (d + 1)) := labelEquiv pcs (.inr (.inl j))
/-- Linked program counter for the tag comparison with the specified stage. -/
def compareTag (pcs : Fin d → ℕ) (j : Fin d) := labelEquiv pcs (.inr (.inr (.inl j)))
/-- Embed a stage-local instruction address in the linked program's disjoint component-body
region. -/
def bodyPC (pcs : Fin d → ℕ) (s : Fin d) (j : Fin (pcs s)) := labelEquiv pcs (.inr (.inr (.inr (.inl ⟨s,j⟩))))
/-- Linked program counter for one of a stage's three handoff instructions. -/
def handoff (pcs : Fin d → ℕ) (s : Fin d) (j : Fin 3) := labelEquiv pcs (.inr (.inr (.inr (.inr (s,j)))))

/-- Component register numbers occupy the low end of the common file. -/
def reg (j : Fin r) : Fin (r + 3) := Fin.castAdd 3 j

/-- First extra register after the component bank, holding the address of the outer tag cell. -/
def addrReg (r : ℕ) : Fin (r + 3) := ⟨r, by omega⟩
/-- Second extra register, holding the tag value read from external memory. -/
def tagReg (r : ℕ) : Fin (r + 3) := ⟨r + 1, by omega⟩
/-- Third extra register, used for the comparison or transfer literal. -/
def tmpReg (r : ℕ) : Fin (r + 3) := ⟨r + 2, by omega⟩

/-- Relocate each operand and jump target while preserving the ordinary
opcode. A transfer replaces only the accepting halt of its component. -/
def bodyInstr (s : Fin d) (next : Option (Fin d)) : Instr w (pcs s) r k → Instr w (codeSize pcs) (r+3) (k+1)
  | .constant a val j => .constant (reg a) val (bodyPC pcs s j)
  | .publicWord a x j => .publicWord (reg a) x.castSucc (bodyPC pcs s j)
  | .stateWord a j => .stateWord (reg a) (bodyPC pcs s j)
  | .copy a b j => .copy (reg a) (reg b) (bodyPC pcs s j)
  | .binary op a b c j => .binary op (reg a) (reg b) (reg c) (bodyPC pcs s j)
  | .loadPrivate a b j => .loadPrivate (reg a) (reg b) (bodyPC pcs s j)
  | .storePrivate a b j => .storePrivate (reg a) (reg b) (bodyPC pcs s j)
  | .jumpEq a b yes no => .jumpEq (reg a) (reg b) (bodyPC pcs s yes) (bodyPC pcs s no)
  | .jumpLt a b yes no => .jumpLt (reg a) (reg b) (bodyPC pcs s yes) (bodyPC pcs s no)
  | .choose yes no => .choose (bodyPC pcs s yes) (bodyPC pcs s no)
  | .readExternal a b j => .readExternal (reg a) (reg b) (bodyPC pcs s j)
  | .writeExternal a b j => .writeExternal (reg a) (reg b) (bodyPC pcs s j)
  | .returnState a => .returnState (reg a)
  | .reject => .reject
  | .accept => match next with
    | none => .accept
    | some t => .constant (tmpReg r) (Fin.ofNat _ t.val) (handoff pcs s 0)

variable (T : (s : Fin d) → Template (pcs s) r k) (next : Fin d → Option (Fin d))

/-- The literal width accommodates every component constant and every stage tag. -/
def literalWidth := max (Finset.univ.sup fun s => (T s).literalWidth) (Nat.clog 2 d)

/-- Encode a stage ordinal as a RAM word at the specified width. -/
def tagWord (w : ℕ) (s : Fin d) : Word w := Fin.ofNat _ s.val

private def instruction : Label pcs → Instr (literalWidth T) (codeSize pcs) (r+3) (k+1)
  | .inl 0 => .publicWord (addrReg r) (Fin.last k) (boot pcs 1)
  | .inl 1 => .readExternal (tagReg r) (addrReg r) (scan pcs 0)
  | .inr (.inl i) => if h : i.val < d then
      .constant (tmpReg r) (tagWord _ ⟨i.val,h⟩) (compareTag pcs ⟨i.val,h⟩) else .reject
  | .inr (.inr (.inl s)) => .jumpEq (tagReg r) (tmpReg r) (bodyPC pcs s (T s).entry) (scan pcs s.succ)
  | .inr (.inr (.inr (.inl ⟨s,j⟩))) => bodyInstr s (next s) (((T s).code j).resize _)
  | .inr (.inr (.inr (.inr (s,0)))) => .writeExternal (addrReg r) (tmpReg r) (handoff pcs s 1)
  | .inr (.inr (.inr (.inr (s,1)))) => .constant (tmpReg r) 0 (handoff pcs s 2)
  | .inr (.inr (.inr (.inr (_,2)))) => .returnState (tmpReg r)

/-- Combine the stage tables and successor map into a native template with three extra
registers and one extra public tag-address operand. -/
def linked : Template (codeSize pcs) (r+3) (k+1) where
  literalWidth := literalWidth T
  entry := boot pcs 0
  code j := instruction T next ((labelEquiv pcs).symm j)

/-- Extend the ordinary public words with the reserved external tag address. -/
def publicData (pub : Fin k → Word w) (addr : Word w) : Fin (k+1) → Word w := Fin.snoc pub addr

/-- Instantiate the linked template with the component public words and the tag-cell address. -/
def machine (pub : Fin k → Word w) (addr : Word w) := (linked T next).instantiate w (publicData pub addr)

private theorem tag_fits (s : Fin d) : s.val < 2 ^ literalWidth T := by
  exact s.isLt.trans_le ((Nat.le_pow_clog (by decide : 1 < 2) d).trans
    (Nat.pow_le_pow_right (by decide) (le_max_right _ _)))

variable (pub : Fin k → Word w) (addr : Word w)

@[simp] theorem code_boot0 : (machine T next pub addr).code (boot pcs 0) =
    .publicWord (addrReg r) (Fin.last k) (boot pcs 1) := by
  simp [machine, linked, Template.instantiate, boot, instruction, Instr.resize]

@[simp] theorem code_boot1 : (machine T next pub addr).code (boot pcs 1) =
    .readExternal (tagReg r) (addrReg r) (scan pcs 0) := by
  simp [machine, linked, Template.instantiate, boot, instruction, Instr.resize]

@[simp] theorem code_scan (s : Fin d) : (machine T next pub addr).code (scan pcs s.castSucc) =
    .constant (tmpReg r) (tagWord w s) (compareTag pcs s) := by
  simp [machine, linked, Template.instantiate, scan, instruction, s.isLt, Instr.resize, tagWord, Nat.mod_eq_of_lt (tag_fits T s)]

@[simp] theorem code_scan_end : (machine T next pub addr).code (scan pcs (Fin.last d)) = .reject := by
  simp [machine, linked, Template.instantiate, scan, instruction, Instr.resize]

@[simp] theorem code_compareTag (s : Fin d) : (machine T next pub addr).code (compareTag pcs s) =
    .jumpEq (tagReg r) (tmpReg r) (bodyPC pcs s (T s).entry) (scan pcs s.succ) := by
  simp [machine, linked, Template.instantiate, compareTag, instruction, Instr.resize]

@[simp] theorem code_handoff0 (s : Fin d) : (machine T next pub addr).code (handoff pcs s 0) =
    .writeExternal (addrReg r) (tmpReg r) (handoff pcs s 1) := by
  simp [machine, linked, Template.instantiate, handoff, instruction, Instr.resize]

@[simp] theorem code_handoff1 (s : Fin d) : (machine T next pub addr).code (handoff pcs s 1) =
    .constant (tmpReg r) 0 (handoff pcs s 2) := by
  simp [machine, linked, Template.instantiate, handoff, instruction, Instr.resize]

@[simp] theorem code_handoff2 (s : Fin d) : (machine T next pub addr).code (handoff pcs s 2) =
    .returnState (tmpReg r) := by simp [machine, linked, Template.instantiate, handoff, instruction, Instr.resize]

@[simp] theorem code_body (s : Fin d) (j : Fin (pcs s)) :
    (machine T next pub addr).code (bodyPC pcs s j) = bodyInstr s (next s) ((T s).instantiate w pub |>.code j) := by
  have h : (T s).literalWidth ≤ literalWidth T :=
    (Finset.le_sup (f := fun t => (T t).literalWidth) (Finset.mem_univ s)).trans (le_max_left _ _)
  simp only [machine, linked, Template.instantiate, bodyPC, Equiv.symm_apply_apply, instruction]
  generalize (T s).code j = i
  have hc (v : Word (T s).literalWidth) : v.val < 2 ^ literalWidth T :=
    v.isLt.trans_le (Nat.pow_le_pow_right (by decide) h)
  cases i <;> cases next s <;> simp [bodyInstr, Instr.resize, bodyPC, Nat.mod_eq_of_lt (hc _),
    Nat.mod_eq_of_lt (tag_fits T _)]

end LiveStageLink

end VPVNP
end Computability
end OAI
