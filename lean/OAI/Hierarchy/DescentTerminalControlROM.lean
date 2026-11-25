import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentNativeBankLookup

namespace OAI
/-! # Literal input pages of the primitive header control directory -/
namespace Hierarchy.DescentTerminalControlROM
open DescentDyadicSpan DescentIssuedTerminalId Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
structure Shape where
  vertices : ℕ
  rowsPerBin : ℕ
  pageBits : ℕ

namespace Shape
variable (s : Shape)
def limit : ℕ := max (max (s.vertices+1) (s.rowsPerBin+1)) (max s.pageBits (2^s.pageBits))
def pitch : ℕ := span s.limit
def base (origin : ℕ) (f : Fin 4) := origin+1+f.val*s.pitch
def bank (origin : ℕ) (f : Fin 4) : Bank := ⟨s.base origin f,Nat.clog 2 s.limit⟩
def zero (origin : ℕ) : Bank := ⟨origin,0⟩
def size := 1+4*s.pitch
def weight (f : Fin 4) : ℕ := ![(s.rowsPerBin+1)*(s.pageBits*(2^s.pageBits*2^s.pageBits)),
  s.pageBits*(2^s.pageBits*2^s.pageBits),2^s.pageBits*2^s.pageBits,2^s.pageBits] f
def literal (x : ℕ) := if x=0 then 0 else (((x-1)%s.pitch)*
  s.weight ⟨((x-1)/s.pitch)%4,Nat.mod_lt _ (by decide)⟩)

theorem cell (f : Fin 4) {j : ℕ} (bounded : j < s.pitch) :
    s.literal (1+f.val*s.pitch+j)=j*s.weight f := by
  have live : 1+f.val*s.pitch+j≠0 := by omega
  have data : 1+f.val*s.pitch+j-1=s.pitch*f.val+j := by rw [Nat.mul_comm s.pitch];omega
  have hi : 0 < s.pitch := span_pos s.limit
  have q : (s.pitch*f.val+j)/s.pitch=f.val := by rw [Nat.mul_add_div hi,Nat.div_eq_of_lt bounded,Nat.add_zero]
  have r : (s.pitch*f.val+j)%s.pitch=j := by rw [Nat.mul_add_mod,Nat.mod_eq_of_lt bounded]
  simp only [literal,ite_eq_right live,data,q,r,Nat.mod_eq_of_lt f.isLt]

theorem field_limit (f : Fin 4) :
    (![s.vertices+1,s.rowsPerBin+1,s.pageBits,2^s.pageBits] f) ≤ s.pitch := by
  apply le_trans _ (span_ge s.limit)
  fin_cases f <;> simp [limit]

/-- The literal writer installs all four weighted lookups and the zero cell in one pass. -/
theorem run {w : ℕ} (origin : ℕ) (m : Memory w) (space : origin+s.size<2^w) :
    let out:=DescentStaticWordColumn.image origin s.literal m s.size
    let code:=DescentStaticWordColumn.program w origin s.literal s.size
    code.Exec m out (4+10*s.size) ∧ CheapCode code ∧
      (∀i : Word w,(zero origin).read out i=0) ∧
      (∀(f : Fin 4) (j : ℕ),j< (![s.vertices+1,s.rowsPerBin+1,s.pageBits,2^s.pageBits] f) →
        (s.bank origin f).read out (j:Word w)=((j*s.weight f:ℕ):Word w)) ∧
      ∀x,x<origin ∨ origin+s.size≤x → out x=m x := by
  have pos:=span_pos s.limit
  have wide : s.pitch<2^w := by unfold size at space;omega
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ space,DescentStaticWordColumn.cheap w origin s.literal s.size,?_,?_,
    fun x hx=>DescentStaticWordColumn.frame _ _ _ _ x hx⟩
  · intro i
    have eqn:=DescentStaticWordColumn.read origin s.size s.literal m (j:=0) (by simp [size])
    simpa [zero,Bank.read,Bank.size,literal,Nat.mod_one] using eqn
  · intro f j hj
    have low:=hj.trans_le (s.field_limit f)
    have reach : 1+f.val*s.pitch+j < s.size := by
      unfold size
      have limit : (f.val+1)*s.pitch≤4*s.pitch := Nat.mul_le_mul_right _ f.isLt
      rw [Nat.succ_mul] at limit
      omega
    have eqn:=DescentStaticWordColumn.read origin s.size s.literal m reach
    change DescentStaticWordColumn.image origin s.literal m s.size
      (s.base origin f+(j:Word w).val % s.pitch)=_
    rw [Fin.val_cast_of_lt (low.trans wide),Nat.mod_eq_of_lt low]
    rw [s.cell f low] at eqn
    simpa only [base,Nat.add_assoc] using eqn

end Shape
end
end Hierarchy.DescentTerminalControlROM

end OAI
