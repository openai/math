import OAI.Hierarchy.DescentTerminalFrozenSize
import OAI.Hierarchy.DescentTerminalFrozenCountBank
import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Fixed numeric shelves for building the authentic frozen cohort list -/
namespace Hierarchy.DescentTerminalFrozenRoster
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
namespace ROM
variable (base f k:ℕ)
local notation "P" => 2^f
local notation "K" => 2^k

def frozen : Bank := ⟨base,f⟩
def offsets : Bank := ⟨base+P,k⟩
def product : Bank := ⟨base+P+K,f+k⟩
def data (i:ℕ) : ℕ :=
  if i<P then i else if i<P+K then (i-P)*P else
  let n:=i-(P+K)
  (n%P+1)*(2^(f+1))^(n/P)

def setup (w:ℕ) := DescentStaticWordColumn.program w base (data f k) (size f k)
def mounted {w : ℕ} (m:Memory w) := DescentStaticWordColumn.image base (data f k) m (size f k)
def shelf (sorted homes rank:Bank) : Shelf :=
  ⟨sorted,homes,rank,frozen base f,offsets base f k,product base f k⟩

theorem room (h:ℕ) (small:f+k+2≤h/2) : size f k≤2^(h/2) := by
  have a : P≤2^(f+k):=Nat.pow_le_pow_right (by decide) (by omega)
  have b : K≤2^(f+k):=Nat.pow_le_pow_right (by decide) (by omega)
  calc
    size f k ≤ 4*2^(f+k) := by
      unfold size
      rw [show K*P=2^(f+k) by rw [pow_add,Nat.mul_comm]];omega
    _ = 2^(f+k+2) := by rw [pow_add (2:ℕ) (f+k) 2];ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) small

theorem run {w:ℕ} (m:Memory w) (fits:base+size f k<2^w) :
    (setup base f k w).Exec m (mounted base f k m) (4+10*size f k) ∧
    CheapCode (setup base f k w) ∧ DescentStaticWordColumn.names (setup base f k w)=15*(size f k+1) ∧
    ∀x,x<base ∨ base+size f k≤x→mounted base f k m x=m x :=
  ⟨DescentStaticWordColumn.mount base (size f k) (data f k) m fits,@DescentStaticWordColumn.cheap w base (data f k) (size f k),DescentStaticWordColumn.names_mount ..,
    fun x outside => DescentStaticWordColumn.frame base (size f k) (data f k) m x outside⟩

theorem reads {w:ℕ} (m:Memory w) (fits:base+size f k<2^w) (sorted homes rank:Bank) :
    Literals f K (shelf base f k sorted homes rank) (mounted base f k m) ∧
    ∀i:ℕ,i<2^w→(frozen base f).read (mounted base f k m) (i:Word w)=((i%P:ℕ):Word w) := by
  have pp:=Nat.two_pow_pos f
  have kk:=Nat.two_pow_pos k
  have stamp (i : ℕ) (hi : i<size f k) :
      mounted base f k m (base+i) = ((data f k i : ℕ) : Word w) :=
    DescentStaticWordColumn.read base (size f k) (data f k) m hi
  have edges:P+K+K*P<2^w:=by unfold size at fits;omega
  constructor
  · constructor
    · intro r hr
      have val:r<2^w:=by omega
      have h:P+r<size f k:=by unfold size;omega
      change mounted base f k m ((base+P)+(r:Word w).val%(2^k))=_
      rw [Fin.val_cast_of_lt val,Nat.mod_eq_of_lt hr,Nat.add_assoc,stamp _ h]
      simp [data,show ¬P+r<P by omega,show P+r<P+K by omega]
    · intro r hr x
      have sx:=x.isLt
      have cell:r*P+x.val<K*P:=by
        calc
          _ < (r+1)*P := by rw [Nat.succ_mul];omega
          _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
      have cellw:r*P+x.val<2^w:=by omega
      have cap:r*P+x.val<2^(f+k):=by simpa [pow_add,Nat.mul_comm] using cell
      have hi:(P+K)+(r*P+x.val)<size f k:=by unfold size;omega
      change mounted base f k m ((base+P+K)+((r*P+x.val:ℕ):Word w).val%(2^(f+k)))=_
      rw [Fin.val_cast_of_lt cellw,Nat.mod_eq_of_lt cap,show base+P+K+(r*P+x.val)=base+((P+K)+(r*P+x.val)) by omega,stamp _ hi]
      have quotient:(r*P+x.val)/P=r:=by rw [Nat.mul_comm r P,Nat.mul_add_div pp,Nat.div_eq_of_lt sx,Nat.add_zero]
      have residue:(r*P+x.val)%P=x.val:=by simp [Nat.add_mod,Nat.mod_eq_of_lt sx]
      simp [data,show ¬(P+K)+(r*P+x.val)<P by omega,show ¬(P+K)+(r*P+x.val)<P+K by omega,
        residue,quotient]
  · intro i ih
    have bound:=Nat.mod_lt i pp
    have hi:i%P<size f k:=by unfold size;omega
    change mounted base f k m (base+(i:Word w).val%P)=_
    rw [Fin.val_cast_of_lt ih,stamp _ hi];simp [data,bound]

end ROM
end
end Hierarchy.DescentTerminalFrozenRoster

end OAI
