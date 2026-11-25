import OAI.Hierarchy.DescentTerminalChipReadback
import OAI.Hierarchy.DescentTerminalScalarInput

namespace OAI
/-! # Materializing the full fixed-size raw-input bank from the shared pay bits and public word output -/
namespace Hierarchy.DescentTerminalRawJoin
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow DescentTerminalPorts Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {w rows publicRows B : ℕ} {P : Type} [Fintype P] {width : P→ℕ}

/-- Both arguments are actual earlier physical rows. The full dyadic target
is filled, including each of the two cable guards and all final empty cells. -/
def load (rows publicRows : ℕ) (candidate «public» : Bank) : Expr :=
  .branch .lt .row (.lit rows) (.lookup candidate .row)
    (.branch .lt .row (.lit (rows+2)) (.lit 0)
      (.branch .lt .row (.lit (rows+2+publicRows)) (.lookup «public» (.op .sub .row (.lit (rows+2)))) (.lit 0)))
def program (w rows publicRows : ℕ) (candidate «public» dest : Bank) :=
  scan w dest.base dest.size (load rows publicRows candidate «public»)
def output (rows publicRows : ℕ) (candidate «public» dest : Bank) (m : Memory w) :=
  image dest.base dest.size (load rows publicRows candidate «public») m

theorem run (candidate «public» dest : Bank) (m : Memory w) (cx : candidate.Fits w dest.base)
    (px : «public».Fits w dest.base) (fit : dest.base+dest.size<2^w) :
    (program w rows publicRows candidate «public» dest).Exec m (output rows publicRows candidate «public» dest m)
      (4+dest.size*(2*(load rows publicRows candidate «public»).work+4)) ∧
    CheapCode (program w rows publicRows candidate «public» dest) := by
  have good : (load rows publicRows candidate «public»).Fits w dest.base := by
    simp [load,Expr.Fits,cx,px]
  exact ⟨scan_exec _ _ _ _ good fit,@scan_cheap _ _ _ _⟩

theorem public_zero (ord : P ↪ ℕ) (x : Ports width) (k : ℕ) (room : (∑z,width z)≤k*B) :
    dense B (publicStream ord x) k=0 := by
  apply (wordBits B).injective
  funext j
  simp [dense,publicStream,show ¬k*B+j.val<∑z,width z by omega,wordBits_zero]

def expected (ord : P ↪ ℕ) (x : Ports width) (pay : RowBit rows B→Bool) (row : ℕ) :=
  if row<rows+2 then dense B (stream pay) row else dense B (publicStream ord x) (row-(rows+2))

theorem read (ord : P ↪ ℕ) (x : Ports width) (pay : RowBit rows B→Bool) (candidate «public» dest : Bank)
    (m : Memory w) (_cx : candidate.Fits w dest.base) (px : «public».Fits w dest.base)
    (fit : dest.base+dest.size<2^w) (space : rows+2+publicRows ≤ dest.size)
    (csize : rows≤candidate.size) (psize : publicRows≤«public».size) (room : (∑z,width z)≤publicRows*B)
    (cp : ∀i : Fin rows,m (candidate.base+i.val)=((dense B (stream pay) i.val).val:Word w))
    (pp : ∀i : Fin publicRows,m («public».base+i.val)=((dense B (publicStream ord x) i.val).val:Word w)) :
    ∀k<dest.size,output rows publicRows candidate «public» dest m (dest.base+k)=((expected ord x pay k).val:Word w) := by
  intro k hk
  rw [output,DescentTerminalChipRuntime.image_at _ _ _ _ (⟨k,hk⟩ : Fin dest.size)]
  have small : dest.size<2^w:=by omega
  have b₀ : rows<2^w:=by omega
  have b₁ : rows+2<2^w:=by omega
  have b₂ : rows+2+publicRows<2^w:=by omega
  have bk:=hk.trans small
  have less (v : ℕ) (lim:v<2^w) : ((k:Word w)<(v:Word w)) ↔ k<v := by
    change ((k:Word w).val<(v:Word w).val) ↔ _
    rw [Fin.val_cast_of_lt bk,Fin.val_cast_of_lt lim]
  have firstGuard : ((k : Word w) < (rows : Word w)+2) ↔ k<rows+2 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using less (rows+2) b₁
  have lastGuard : ((k : Word w) < (rows : Word w)+2+(publicRows : Word w)) ↔ k<rows+2+publicRows := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using less (rows+2+publicRows) b₂
  by_cases a : k<rows
  · have aa : k<rows+2:=by omega
    simpa [load,Expr.eval,Comparison.test,less _ b₀,a,aa,expected,Bank.read,Fin.val_cast_of_lt bk,
      Nat.mod_eq_of_lt (a.trans_le csize)] using cp ⟨k,a⟩
  · by_cases b : k<rows+2
    · simp [load,Expr.eval,Comparison.test,less _ b₀,firstGuard,a,b,expected,raw_sentinel pay k (by omega)]
    · by_cases c : k<rows+2+publicRows
      · have idx : k-(rows+2)<publicRows:=by omega
        have sub : (k:Word w)-(rows+2:ℕ) = ((k-(rows+2):ℕ):Word w) :=
          (Nat.cast_sub (R:=Word w) (by omega)).symm
        have offset : (k:Word w)-((rows:Word w)+2) = ((k-(rows+2):ℕ):Word w) := by
          simpa only [Nat.cast_add, Nat.cast_ofNat] using sub
        simpa [load,Expr.eval,Comparison.test,less _ b₀,firstGuard,lastGuard,a,b,c,expected,
          RowOp.opcode,BinaryOp.eval,offset,Bank.read,Fin.val_cast_of_lt ((idx.trans_le psize).trans px.2.1),
          Nat.mod_eq_of_lt (idx.trans_le psize)] using pp ⟨_,idx⟩
      · have high : publicRows≤k-(rows+2):=by omega
        simp [load,Expr.eval,Comparison.test,less _ b₀,firstGuard,lastGuard,a,b,c,expected,
          public_zero ord x _ (room.trans (Nat.mul_le_mul_right B high))]

end
end Hierarchy.DescentTerminalRawJoin

end OAI
