import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Native scans writing the three operand columns of a mark-gate interpreter -/

namespace Hierarchy.ProtocolRAM.GateColumns

open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr
open ProbeStage.Native
open scoped Fin.CommRing

/-- Public gate operand recipe. A tile selector addresses a word in an earlier, live bank. -/
inductive Operand
  | literal (address : ℕ)
  | tile (offset : ℕ)
deriving DecidableEq

def Operand.mode : Operand → ℕ
  | .literal _ => 0
  | .tile _ => 1

def Operand.argument : Operand → ℕ
  | .literal n | .tile n => n

def Operand.value {w : ℕ} (source : Bank) (work : ℕ) (m : Memory w) : Operand → Word w
  | .literal n => n
  | .tile a => (work+4 : ℕ) + m (source.base+a)

/-- Six uniform shape columns hold a mode and argument for every one of the
three mark-gate operands. The memory holding these columns contains no tile IDs. -/
structure Directory where
  base : ℕ
  bits : ℕ

def Directory.stride (D : Directory) := 2^D.bits
def Directory.bank (D : Directory) (c : ℕ) : Bank := ⟨D.base+c*D.stride,D.bits⟩

def term (source : Bank) (D : Directory) (work : ℕ) (c : Fin 3) : Expr :=
  let mode := Expr.lookup (D.bank (2*c.val)) .row
  let arg := Expr.lookup (D.bank (2*c.val+1)) .row
  .branch .eq mode (.lit 0) arg (.op .add (.lit (work+4)) (.lookup source arg))

def inputs (source : Bank) (D : Directory) (work : ℕ) : List Expr :=
  [term source D work 0,term source D work 1,term source D work 2]

def passes (source : Bank) (D : Directory) (work n base : ℕ) :=
  columns n base (inputs source D work)

/-- Truth of six shape words in the actual pre-scan RAM. -/
def Mounted {w n : ℕ} (D : Directory) (spec : Fin n → Fin 3 → Operand) (m : Memory w) : Prop :=
  ∀ (i : Fin n) (c : Fin 3),
    (D.bank (2*c.val)).read m (i.val : Word w) = ((spec i c).mode : Word w) ∧
    (D.bank (2*c.val+1)).read m (i.val : Word w) = ((spec i c).argument : Word w)

theorem eval_term {w n : ℕ} (source : Bank) (D : Directory) (work : ℕ)
    (spec : Fin n → Fin 3 → Operand) (m : Memory w) (mounted : Mounted D spec m) (width : 0 < w)
    (inside : ∀ i c a, spec i c = .tile a → a < source.size)
    (fits : source.size < 2^w) (i : Fin n) (c : Fin 3) :
    (term source D work c).eval m (i.val : Word w) = (spec i c).value source work m := by
  obtain ⟨mode,arg⟩ := mounted i c
  cases heq : spec i c with
  | literal a =>
    simp [heq,Operand.mode,Operand.argument] at mode arg
    simp [term,Expr.eval,mode,arg,Comparison.test,Operand.value]
  | tile a =>
    have b := inside i c a heq
    have ne : (1 : Word w) ≠ 0 := by
      have hpow : 1 < 2^w := Nat.one_lt_two_pow width.ne'
      intro h
      have hv := congrArg Fin.val h
      simp [Nat.mod_eq_of_lt hpow] at hv
    simp [heq,Operand.mode,Operand.argument] at mode arg
    simp only [term,Expr.eval,mode,arg,Comparison.test,Nat.cast_zero,beq_iff_eq,ne,ite_false,
      RowOp.opcode,BinaryOp.eval,Operand.value]
    simp [Bank.read,Fin.val_cast_of_lt (b.trans fits),Nat.mod_eq_of_lt b]

theorem term_fits (source : Bank) (D : Directory) (work : ℕ) (c : Fin 3) {w base : ℕ}
    (hs : source.Fits w base) (hd : ∀ j, j<6 → (D.bank j).Fits w base) :
    (term source D work c).Fits w base := by
  have cb := c.isLt
  exact ⟨⟨hd _ (by omega),trivial⟩,trivial,⟨hd _ (by omega),trivial⟩,
    trivial,hs,hd _ (by omega),trivial⟩

private theorem input_get (source : Bank) (D : Directory) (work : ℕ) (c : Fin 3) :
    (inputs source D work)[c.val]'(by simp [inputs]) = term source D work c := by
  fin_cases c <;> rfl

/-- Output cells contain their prescribed literals or the marked-workspace address
obtained by reading a runtime tile ID. Every operand reads the original bank. -/
theorem read {w n : ℕ} (source : Bank) (D : Directory) (work base : ℕ)
    (spec : Fin n → Fin 3 → Operand) (m : Memory w) (mounted : Mounted D spec m)
    (width : 0 < w) (hs : source.Fits w base) (hd : ∀ j, j<6 → (D.bank j).Fits w base)
    (inside : ∀ i c a, spec i c = .tile a → a < source.size) (i : Fin n) (c : Fin 3) :
    result (passes source D work n base) m (base+c.val*n+i.val) = (spec i c).value source work m := by
  have readers (e : Expr) (he : e ∈ inputs source D work) : e.Fits w base := by
    simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl <;> exact term_fits _ _ _ _ hs hd
  have h := columns_read (inputs source D work) m (src := base) (base := base) le_rfl readers
    c.val (by simp [inputs]) i
  rw [input_get] at h
  exact h.trans (eval_term source D work spec m mounted width inside hs.2.1 i c)

theorem run {w n : ℕ} (source : Bank) (D : Directory) (work base : ℕ) (m : Memory w)
    (hs : source.Fits w base) (hd : ∀ j, j<6 → (D.bank j).Fits w base) (room : base+3*n<2^w) :
    (program w (passes source D work n base)).Exec m (result (passes source D work n base) m)
      (clock (passes source D work n base)) := by
  apply program_exec
  apply columns_safe (src := base) _ le_rfl _ (by simpa [inputs] using room)
  intro e he
  simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl <;> exact term_fits _ _ _ _ hs hd

theorem cheap (w n : ℕ) (source : Bank) (D : Directory) (work base : ℕ) :
    CheapCode (program w (passes source D work n base)) := by
  generalize passes source D work n base = ps
  exact @program_cheap w ps

/-- For every table length and every word width the entire compiler has the same
instruction, register and public-slot counts. All addresses occur as immediate words. -/
theorem code_size (w n : ℕ) (source : Bank) (D : Directory) (work base : ℕ) :
    let A := program w (passes source D work n base)
    A.labels = 301 ∧ A.registers = 107 ∧ A.slots = 0 := by
  simpa [passes,inputs,columns,term,Expr.work] using program_size w (passes source D work n base)

theorem ticks (n : ℕ) (source : Bank) (D : Directory) (work base : ℕ) :
    clock (passes source D work n base) ≤ 16 + 3*n*64 := by
  have h := columns_clock n base 30 (inputs source D work) (by
    intro e he
    simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl <;> simp [term,Expr.work])
  simp only [inputs,List.length_cons,List.length_nil] at h
  unfold passes inputs
  omega

theorem frame {w : ℕ} (n : ℕ) (source : Bank) (D : Directory) (work base : ℕ)
    (m : Memory w) (a : ℕ) (outside : a<base ∨ base+3*n≤a) :
    result (passes source D work n base) m a = m a := by
  exact columns_frame (inputs source D work) m (by simpa [inputs] using outside)

end Hierarchy.ProtocolRAM.GateColumns

end OAI
