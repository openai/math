import OAI.Computability.VPVNP.PrimedCounterAdminExec
import OAI.Computability.VPVNP.PrimedInputRAMOnce
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic.Ring

/-!
# Computing the middle-group operand frames

The length word at frame offset 22 specifies how many bits of the reserved
prefix belong to the evaluator. Its value is checked against the capacity.
The computed destination for runtime fields follows the actual prefix on
the tape, while the order table begins beyond the reserved prefix in the
distributed advice. Quotient and remainder round the number of packed
words up without adding the full word width to the prefix length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorAdviceFrames

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

/-- A native advice-frame initializer flow with 32 registers and eleven public operands. -/
abbrev FrameCode := Flow 32 11
/-- The eleven public words supplied to the midpoint advice-frame initializer. -/
abbrev FramePub (w : ℕ) := Fin 11 → Word w
variable {w : ℕ}

private abbrev Ops := List (Op 32 11)

private def install (rs : Regs w 32) (vs : List (Fin 32 × Word w)) :=
  vs.foldl (fun r kv => Function.update r kv.1 kv.2) rs

/-- The address at frame offset 22 that stores the actual evaluator prefix length. -/
def lengthAddress (pub : FramePub w) : Word w := pub 3 + 22
/-- Read the evaluator prefix's actual bit length from its reserved frame cell. -/
def actualLength (pub : FramePub w) (m : Memory w) := m (lengthAddress pub).val

/-- Number of packed prefix words, computed from the checked exact length. -/
def prefixRows (pub : FramePub w) (m : Memory w) : Word w :=
  let a := actualLength pub m
  let q := BinaryOp.div.eval a (pub 2)
  if BinaryOp.mod.eval a (pub 2) = 0 then q else q + 1

/-- The first runtime field address on the tape after the input data and actual evaluator
prefix. -/
def runtimeBase (pub : FramePub w) (m : Memory w) : Word w :=
  pub 6 + 1 + pub 5 + actualLength pub m

/-- The total word count of the runtime skeleton computed from the two public dimensions. -/
def skeletonSize (pub : FramePub w) : Word w := 2 * pub 8 + 6 * pub 7 + 4

/-- The first exponent-scatter destination after the leading runtime fields. -/
def scatterBase (pub : FramePub w) (m : Memory w) : Word w :=
  runtimeBase pub m + 2 * pub 7 + 2

/-- Public operands are advice base, prefix capacity, width, frame base,
packed prefix base, radius, old-state base, exponent width, exponent bank
length, incoming exponent base and permutation map base. -/
private def loadOps : Ops :=
  [.constant 0 0, .constant 1 1, .constant 2 2, .constant 3 3,
   .publicWord 4 3, .publicWord 5 1, .publicWord 6 2, .publicWord 7 0, .publicWord 8 4,
   .publicWord 9 5, .publicWord 10 6, .publicWord 11 7, .publicWord 12 8,
   .publicWord 13 9, .publicWord 14 10,
   .binary .mul 22 3 3, .binary .add 22 22 2, .binary .add 22 22 22, .binary .add 22 4 22,
   .read 15 22, .copy 22 4]

private def load : FrameCode := lines loadOps (by decide)

private def loaded (pub : FramePub w) (rs : Regs w 32) (m : Memory w) :=
  install rs [(0,0),(1,1),(2,2),(3,3),(4,pub 3),(5,pub 1),(6,pub 2),(7,pub 0),(8,pub 4),
    (9,pub 5),(10,pub 6),(11,pub 7),(12,pub 8),(13,pub 9),(14,pub 10),(22,3*3),
    (22,3*3+2),(22,(3*3+2)+(3*3+2)),(22,lengthAddress pub),(15,actualLength pub m),(22,pub 3)]

private def loadEvents (pub : FramePub w) (m : Memory w) : List (Event w) :=
  List.replicate 19 .tick ++ [.read (lengthAddress pub) (actualLength pub m),.tick]

private theorem load_iff (pub : FramePub w) (st : Word w) (rs : Regs w 32) (m : Memory w) (es out m') :
    Flow.Exec pub st load rs m es out m' ↔ es = loadEvents pub m ∧ out = loaded pub rs m ∧ m' = m := by
  rw [load, PrimedCounter.Admin.exec_lines_iff_trace]
  have h22 : (3*3+2 : Word w) + (3*3+2) = 22 := by ring
  have ht : trace pub st loadOps rs m = some (loadEvents pub m,loaded pub rs m,m) := by
    unfold loadEvents loaded actualLength lengthAddress
    rw [← h22]
    rfl
  rw [ht]; simp [eq_comm]

private def computeOps : Ops :=
  [.binary .add 16 7 6, .binary .div 17 15 6, .binary .mod 18 15 6,
   .binary .add 19 10 1, .binary .add 19 19 9, .binary .add 19 19 15,
   .binary .add 23 11 11, .binary .add 24 23 23, .binary .add 20 23 24,
   .binary .add 24 12 12, .binary .add 20 20 24, .binary .add 24 2 2,
   .binary .add 20 20 24, .binary .add 21 19 23, .binary .add 21 21 2]

private def compute : FrameCode := lines computeOps (by decide)

private def computed (pub : FramePub w) (rs : Regs w 32) (m : Memory w) :=
  let a := actualLength pub m
  let z := pub 7
  let twoZ := z+z
  let fourZ := twoZ+twoZ
  let sixZ := twoZ+fourZ
  let twoTZ := pub 8 + pub 8
  install (loaded pub rs m)
    [(16,pub 0+pub 2),(17,BinaryOp.div.eval a (pub 2)),(18,BinaryOp.mod.eval a (pub 2)),
     (19,pub 6+1),(19,pub 6+1+pub 5),(19,runtimeBase pub m),
     (23,twoZ),(24,fourZ),(20,sixZ),(24,twoTZ),(20,sixZ+twoTZ),(24,2+2),
     (20,skeletonSize pub),(21,runtimeBase pub m+twoZ),(21,scatterBase pub m)]

private theorem compute_iff (pub : FramePub w) (st : Word w) (rs : Regs w 32) (m : Memory w) (es out m') :
    Flow.Exec pub st compute (loaded pub rs m) m es out m' ↔
      es = List.replicate 15 .tick ∧ out = computed pub rs m ∧ m' = m := by
  rw [compute, PrimedCounter.Admin.exec_lines_iff_trace]
  have hsize : skeletonSize pub =
      (pub 7 + pub 7 + ((pub 7 + pub 7) + (pub 7 + pub 7))) + (pub 8 + pub 8) + (2+2) := by
    unfold skeletonSize; ring
  have hbase : scatterBase pub m = runtimeBase pub m + (pub 7+pub 7) + 2 := by
    unfold scatterBase; ring
  have ht : trace pub st computeOps (loaded pub rs m) m =
      some (List.replicate 15 .tick,computed pub rs m,m) := by
    unfold computed
    rw [hsize,hbase]
    rfl
  rw [ht]; simp [eq_comm]

private def reject : FrameCode := .line (.guardLt 0 0)
private def roundUp : FrameCode := .ifEq 18 0 (.line (.copy 17 17)) (.line (.binary .add 17 17 1))

/-- Read and validate the actual prefix length and field width, then compute destinations and
the rounded-up prefix row count. -/
def setup : FrameCode :=
  .seq load (.ifLt 5 15 reject (.seq (.line (.guardLt 0 6)) (.seq compute roundUp)))

/-- The bank of computed operands before publication. -/
def ready (pub : FramePub w) (rs : Regs w 32) (m : Memory w) : Regs w 32 :=
  Function.update (computed pub rs m) 17 (prefixRows pub m)

/-- The initializer's load events followed by the local ticks used to compute the four frames'
operands. -/
def setupEvents (pub : FramePub w) (m : Memory w) : List (Event w) :=
  loadEvents pub m ++ List.replicate 19 .tick

private theorem round_iff (pub : FramePub w) (st : Word w) (rs : Regs w 32) (m : Memory w)
    (es out m') :
    Flow.Exec pub st roundUp (computed pub rs m) m es out m' ↔
      es = [.tick,.tick] ∧ out = ready pub rs m ∧ m' = m := by
  let r := computed pub rs m
  let q := BinaryOp.div.eval (actualLength pub m) (pub 2)
  let rem := BinaryOp.mod.eval (actualLength pub m) (pub 2)
  have hrem : r 18 = rem := rfl
  have hq : r 17 = q := rfl
  have h0 : r 0 = 0 := rfl
  have h1 : r 1 = 1 := rfl
  have hz : (r 18 = r 0) = (rem = 0) := by rw [hrem,h0]
  constructor
  · intro h
    cases h with
    | ifEqYes hh hb =>
      cases hb with
      | line he =>
        have hn : rem = 0 := hz ▸ hh
        simpa [Op.effect, ready, prefixRows, hn, ← hq, ← hrem, r, rem, q, eq_comm] using he
    | ifEqNo hh hb =>
      cases hb with
      | line he =>
        have hn : rem ≠ 0 := fun h => hh (hz.symm ▸ h)
        have hr : ready pub rs m = Function.update r 17 (r 17 + r 1) := by
          change Function.update r 17 (if rem = 0 then q else q+1) = _
          rw [ite_eq_right hn, h1, hq]
        rw [hr]
        simpa [Op.effect, BinaryOp.eval, r, eq_comm] using he
  · rintro ⟨rfl,rfl,rfl⟩
    by_cases hn : rem = 0
    · apply Flow.Exec.ifEqYes (hz.symm ▸ hn)
      apply Flow.Exec.line
      simp only [Op.effect, ready, prefixRows, show BinaryOp.mod.eval (actualLength pub _) (pub 2) = 0 from hn,
        ite_true]
      rfl
    · apply Flow.Exec.ifEqNo (fun h => hn (hz ▸ h))
      apply Flow.Exec.line
      simp only [Op.effect, ready, prefixRows, show BinaryOp.mod.eval (actualLength pub _) (pub 2) ≠ 0 from hn,
        ite_false]
      rfl

theorem setup_iff (pub : FramePub w) (st : Word w) (rs : Regs w 32) (m : Memory w) (es out m') :
    Flow.Exec pub st setup rs m es out m' ↔
      actualLength pub m ≤ pub 1 ∧ 0 < pub 2 ∧
      es = setupEvents pub m ∧ out = ready pub rs m ∧ m' = m := by
  constructor
  · intro h
    cases h with
    | seq hl h =>
      obtain ⟨rfl,rfl,rfl⟩ := (load_iff pub st rs m _ _ _).mp hl
      cases h with
      | ifLtYes _ hbad =>
        cases hbad with | line he => simp [Op.effect] at he
      | ifLtNo hn h =>
        cases h with
        | seq hg h =>
          cases hg with
          | line he =>
            change (if 0 < pub 2 then some _ else none) = _ at he
            split at he
            · rename_i hp
              obtain ⟨rfl,rfl,rfl⟩ := by simpa using he
              cases h with
              | seq hc hr =>
                obtain ⟨rfl,rfl,rfl⟩ := (compute_iff pub st rs _ _ _ _).mp hc
                obtain ⟨rfl,rfl,rfl⟩ := (round_iff pub st rs _ _ _ _).mp hr
                exact ⟨le_of_not_gt hn,hp,rfl,rfl,rfl⟩
            · contradiction
  · rintro ⟨hcap,hpos,rfl,rfl,rfl⟩
    exact .seq ((load_iff pub st rs _ _ _ _).mpr ⟨rfl,rfl,rfl⟩)
      (.ifLtNo (not_lt_of_ge hcap) (.seq (.line (by simp [Op.effect, show loaded pub rs _ 0 = 0 from rfl,
        show loaded pub rs _ 6 = pub 2 from rfl, hpos]))
        (.seq ((compute_iff pub st rs _ _ _ _).mpr ⟨rfl,rfl,rfl⟩)
          ((round_iff pub st rs _ _ _ _).mpr ⟨rfl,rfl,rfl⟩))))


/-- The validated length is read at the ordinary reserved address. -/
theorem actualLength_at (pub : FramePub w) (m : Memory w) (hfit : (pub 3).val+22 < 2^w) :
    actualLength pub m = m ((pub 3).val+22) := by
  have hv : (22 : Word w).val = 22 := Nat.mod_eq_of_lt (show (22 : ℕ) < 2^w by omega)
  rw [actualLength, lengthAddress, Fin.val_add_eq_of_add_lt (by rw [hv]; exact hfit), hv]

private theorem ceilDiv_remainder (a b : ℕ) (hb : 0 < b) :
    a ⌈/⌉ b = a / b + (if a % b = 0 then 0 else 1) := by
  have hm := Nat.mod_lt a hb
  have hd := Nat.div_add_mod a b
  rw [Nat.ceilDiv_eq_add_pred_div, show a+b-1 = b*(a/b)+(a%b+b-1) by omega, Nat.mul_add_div hb]
  by_cases h : a%b = 0
  · simp [h, Nat.div_eq_of_lt (show b-1 < b by omega)]
  · rw [ite_eq_right h]
    congr 1
    apply Nat.div_eq_of_lt_le <;> omega

/-- Exact natural word count in the prefix packer's fifth operand. -/
theorem prefixRows_val (pub : FramePub w) (m : Memory w) (hw : 0 < (pub 2).val) :
    (prefixRows pub m).val = (actualLength pub m).val ⌈/⌉ (pub 2).val := by
  let a := actualLength pub m
  let b := pub 2
  have hr : (BinaryOp.mod.eval a b).val = a.val % b.val :=
    Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt a.isLt)
  have hq : (BinaryOp.div.eval a b).val = a.val / b.val :=
    Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt a.isLt)
  change 0 < b.val at hw
  change (if BinaryOp.mod.eval a b = 0 then BinaryOp.div.eval a b else BinaryOp.div.eval a b + 1).val = a.val ⌈/⌉ b.val
  rw [ceilDiv_remainder _ _ hw]
  by_cases h : a.val % b.val = 0
  · have he : BinaryOp.mod.eval a b = 0 := Fin.ext (hr.trans h)
    simp only [ite_eq_left he, hq, h, ite_true, Nat.add_zero]
  · have he : BinaryOp.mod.eval a b ≠ 0 := fun e => h (hr.symm.trans (congrArg Fin.val e))
    have ha : 0 < a.val := by
      by_contra! hh
      exact h (by rw [show a.val = 0 by omega, Nat.zero_mod])
    have hb : 1 < b.val := by
      by_contra! hh
      exact h (by rw [show b.val = 1 by omega, Nat.mod_one])
    have hv : (1 : Word w).val = 1 := Nat.mod_eq_of_lt (show (1 : ℕ) < 2^w from hb.trans b.isLt)
    have hsum : (BinaryOp.div.eval a b).val + (1 : Word w).val < 2^w := by
      rw [hq,hv]; have := Nat.div_lt_self ha hb; have := a.isLt; omega
    simp only [ite_eq_right he, Fin.val_add_eq_of_add_lt hsum, hq, hv, ite_eq_right h]

/-- The initializer's register calculations depend on the read length alone. -/
theorem ready_congr_length (pub : FramePub w) (rs : Regs w 32) (m u : Memory w)
    (h : actualLength pub m = actualLength pub u) : ready pub rs m = ready pub rs u := by
  simp only [ready, computed, loaded, runtimeBase, scatterBase, prefixRows, h]

end LiveEvaluatorAdviceFrames

end VPVNP
end Computability
end OAI
