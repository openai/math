import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Physical state pages for the ordinary date's aligned operand pointers -/

namespace Hierarchy.DescentOperandStateBanks
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- Each previous-state operand supplies a kind, a local peer, an alias/cable/port
number, a within-word chunk, and the first, stride and count of its aligned range. -/
abbrev Field := Fin 7

abbrev Pages (operands : ℕ) := Fin (7*operands)

def page {operands : ℕ} (field : Field) (operand : Fin operands) : Pages operands :=
  finProdFinEquiv (field,operand)

def pageSize (hosts groups lanes : ℕ) := hosts*chunks groups lanes

def bankBase {pages : ℕ} (origin words : ℕ) (index : Fin pages) := origin+index.val*words

def address {pages : ℕ} (origin words : ℕ) (index : Fin pages) (i : Fin words) :=
  bankBase origin words index+i.val

theorem address_lt {pages words : ℕ} (origin : ℕ) (index : Fin pages) (i : Fin words) :
    address origin words index i < origin+pages*words := by
  have next := Nat.mul_le_mul_right words index.isLt
  rw [Nat.succ_mul] at next
  have inside := i.isLt
  dsimp [address,bankBase]
  omega

theorem address_injective {pages words : ℕ} (origin : ℕ) :
    Function.Injective (fun a : Fin pages × Fin words => address origin words a.1 a.2) := by
  intro a b eqn
  apply finProdFinEquiv.injective
  apply Fin.ext
  have cancel : a.1.val*words+a.2.val=b.1.val*words+b.2.val := by
    dsimp [address,bankBase] at eqn
    omega
  simpa [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using cancel

/-- The runtime writes only the active rectangle of each field. A single trailing
mask guard supplies the power-of-two window of the final bounded read. -/
def column (origin words j : ℕ) : Bank := ⟨origin+j*words,Nat.clog 2 words⟩
def guard (origin pages words : ℕ) := origin+pages*words+2^Nat.clog 2 words

def wordAt (origin words j : ℕ) : Expr := .lookup (column origin words j) .row

theorem read_word {w words : ℕ} (origin j : ℕ) (r : Fin words) (m : Memory w)
    (small : words ≤ 2^w) :
    (wordAt origin words j).eval m (r.val : Word w) = m (origin+j*words+r.val) := by
  have inside := r.isLt.trans_le (Nat.le_pow_clog (by decide : 1<2) words)
  simp only [wordAt,Expr.eval,Bank.read,column,Bank.size,Fin.val_cast_of_lt (r.isLt.trans_le small),
    Nat.mod_eq_of_lt inside]

theorem read_fits {w src dst words pages : ℕ} (j : Fin pages)
    (low : guard src pages words ≤ dst) (fit : dst < 2^w) : (wordAt src words j.val).Fits w dst := by
  have reach := Nat.mul_le_mul_right words (Nat.le_of_lt j.isLt)
  change (0<2^Nat.clog 2 words ∧ 2^Nat.clog 2 words<2^w ∧ src+j.val*words+2^Nat.clog 2 words≤dst) ∧ True
  dsimp only [guard] at low
  exact ⟨⟨Nat.two_pow_pos _,by omega,by omega⟩,trivial⟩

def transfers (src dst words pages : ℕ) :=
  DescentPackedFlowBatch.passes dst words words (wordAt src words) 0 pages

/-- The next physical shelf owns its actual words at exactly the same
field/operand/row offsets. All earlier donor inputs and all later regions survive. -/
theorem move {w : ℕ} (src dst words pages : ℕ) (m : Memory w)
    (separate : guard src pages words ≤ dst) (room : dst+pages*words < 2^w)
    (small : words ≤ 2^w) :
    let ps:=transfers src dst words pages
    let endMem:=result ps m
    (program w ps).Exec m endMem (clock ps) ∧
    (∀j : Fin pages,∀i : Fin words,endMem (address dst words j i)=m (address src words j i)) ∧
    (∀a,a<dst ∨ dst+pages*words≤a → endMem a=m a) ∧
    clock ps≤4+pages*(4+18*words) ∧ CheapCode (program w ps) := by
  intro ps endMem
  have fits (j : ℕ) (h : j<pages) := read_fits (w:=w) (⟨j,h⟩ : Fin pages) separate (by omega : dst<2^w)
  obtain ⟨issued,values,lower⟩ := DescentPackedFlowBatch.execute dst words words pages (wordAt src words) m fits room le_rfl
  refine ⟨issued,fun j i=>(values j i).trans (read_word src j.val i m small),?_,?_,?_⟩
  · intro a ha
    rcases ha with lo|hi
    · exact lower a lo
    · exact DescentPackedFlowBatch.above dst words words _ m 0 pages a le_rfl (by simpa using hi)
  · simpa only [ps,transfers,Nat.mul_comm words 18] using
      DescentPackedFlowBatch.tariff dst words words pages (wordAt src words) 7 (fun _ _=>le_rfl)
  · exact program_cheap _ _

end
end Hierarchy.DescentOperandStateBanks

end OAI
