import OAI.Hierarchy.DescentSIMDLookup
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Literal finite shift-free dictionary and last-batch masks for a packed map -/
namespace Hierarchy.DescentSIMDLookup.Book
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {a b w : ℕ} (f : Cell a→Cell b) (H J M : ℕ)
local notation "rows" => H*chunks J M
local notation "page" => 2^(a*M)

def words (a H J M : ℕ) := 2^(a*M)+H*chunks J M
def banks (base a H J M : ℕ) (source : Bank) : Banks :=
  ⟨source,⟨base,a*M⟩,⟨base+2^(a*M),Nat.clog 2 (H*chunks J M)⟩⟩
local notation "data" => Cell (a*M)⊕Fin rows

def value : data→ℕ
  | .inl key=>(table f key).val
  | .inr j=>maskWord b M J ((row H J M).symm j).2.val

def literal (i : ℕ) :=
  if hi:i<words a H J M then value f H J M (finSumFinEquiv.symm ⟨i,hi⟩) else 0

def install (w base : ℕ) := DescentStaticWordColumn.program w base (literal f H J M) (words a H J M)
def image (base : ℕ) (m : Memory w) := DescentStaticWordColumn.image base (literal f H J M) m (words a H J M)

theorem ordinal (base : ℕ) (source : Bank) (i : data) :
    fixedAddr (banks base a H J M source) i=base+(finSumFinEquiv i).val := by
  cases i <;> simp [banks,fixedAddr]; omega

theorem mount (base : ℕ) (src : Bank) (m : Memory w) (space : base+words a H J M<2^w) :
    (install f H J M w base).Exec m (image f H J M base m) (4+10*words a H J M) ∧
    (∀i : data,image f H J M base m (fixedAddr (banks base a H J M src) i)=fixedWord f i) ∧
    (∀x,x<base ∨ base+words a H J M≤x→image f H J M base m x=m x) ∧ CheapCode (install f H J M w base) := by
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ space,?_,DescentStaticWordColumn.frame _ _ _ _,DescentStaticWordColumn.cheap w base (literal f H J M) (words a H J M)⟩
  intro i
  rw [ordinal]
  have atCell:=DescentStaticWordColumn.read base (words a H J M) (literal f H J M) m (finSumFinEquiv i).isLt
  have correct : (value f H J M i:Word w)=fixedWord f i := by cases i <;> rfl
  have small : (finSumFinEquiv i).val<words a H J M := (finSumFinEquiv i).isLt
  have real : literal f H J M (finSumFinEquiv i).val=value f H J M i:=by
    rw [literal,dite_eq_left small]
    exact congrArg (value f H J M) (finSumFinEquiv.symm_apply_apply i)
  rw [real] at atCell
  exact atCell.trans correct

theorem retain (base : ℕ) (source : Bank) (m new : Memory w)
    (fixed : ∀i : data,m (fixedAddr (banks base a H J M source) i)=fixedWord f i)
    (keep : ∀x,x<base+words a H J M→new x=m x) :
    ∀i : data,new (fixedAddr (banks base a H J M source) i)=fixedWord f i := by
  intro i
  exact (keep _ (by rw [ordinal];exact Nat.add_lt_add_left (finSumFinEquiv i).isLt _)).trans (fixed i)

theorem table_area (payload unit : ℕ) (enough : a≤unit) :
    words a H J (lanes payload unit)≤2^(payload/2)+H*chunks J (lanes payload unit) := by
  apply Nat.add_le_add_right
  apply Nat.pow_le_pow_right (by decide)
  exact (Nat.mul_le_mul_right _ enough).trans (by simpa [Nat.mul_comm] using lanes_fit payload unit)

end
end Hierarchy.DescentSIMDLookup.Book

end OAI
