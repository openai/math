import OAI.Hierarchy.DescentZipBook
import OAI.Hierarchy.ProbeStageColumnScan

namespace OAI
/-! # Converting each packed lane to the common width used by the operand decoder -/
namespace Hierarchy.DescentOperandInputCast
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {N H G w : ℕ}
def convert (a b : ℕ) (x : Cell a) (_ : Cell 0) : Cell b := (x.val : ℕ)
def gates (width : Fin N→ℕ) (b : ℕ) (i : Fin N) : Book.Gate :=
  ⟨width i,0,b,convert (width i) b⟩
def words (n bound M : ℕ) := n*(2*2^(bound*M))
def endAddress (base n bound M : ℕ) := base+words n bound M
def tables (width : Fin N→ℕ) (b bound M base : ℕ) := Book.tables (gates width b) bound M base
def expr (width : Fin N→ℕ) (b bound M base : ℕ) (i : Fin N) (src : Expr) :=
  (tables width b bound M base i).read src (.lit 0)
def program (width : Fin N→ℕ) (b bound M base w : ℕ) := Book.install (gates width b) bound M w base
def image (width : Fin N→ℕ) (b bound M base : ℕ) (m : Memory w) := Book.image (gates width b) bound M base m

theorem any (width : Fin N→ℕ) (b bound M base : ℕ) (m : Memory w)
    (small : ∀ i,width i≤bound) (room : endAddress base N bound M<2^w) :
    (program width b bound M base w).Exec m (image width b bound M base m) (4+10*words N bound M) ∧
    CheapCode (program width b bound M base w) ∧
    (∀ z,z<base ∨ endAddress base N bound M≤z → image width b bound M base m z=m z) ∧
    ∀ i,Static (tables width b bound M base i) (convert (width i) b) M (image width b bound M base m) :=by
  obtain ⟨go,read,frame,cheap⟩:=Book.mount (gates width b) bound M base m (by
    intro i
    simpa only [gates,Nat.add_zero] using small i) room
  exact ⟨go,cheap,frame,read⟩

theorem expr_fits (width : Fin N→ℕ) (b bound M base : ℕ) (i : Fin N) (src : Expr)
    (small : width i≤bound) (fit : src.Fits w base) (room : endAddress base N bound M<2^w) :
    (expr width b bound M base i src).Fits w (endAddress base N bound M) :=by
  let top:=endAddress base N bound M
  have sides:=Book.geometry (gates width b) bound M base i (out:=top) le_rfl room
    (by simpa only [gates,Nat.add_zero] using small)
  have sliced : DescentPackedZip.Fits (tables width b bound M base i) src (.lit 0) (width i) 0 M top w :=by
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) fit,trivial,
      sides.1,sides.2,by simp [tables,Book.tables,gates],by simp [tables,Book.tables,gates]⟩
  exact ⟨sliced.apply,sliced.right,sliced.shift,sliced.left⟩

theorem issued (width : Fin N→ℕ) (b bound M base : ℕ) (i : Fin N) (src : Expr) (m : Memory w)
    (x : Fin H→Fin G→Cell (width i)) (small : ∀ j,width j≤bound)
    (fit : src.Fits w base) (read : Source src x M m) (room : endAddress base N bound M<2^w) :
    (expr width b bound M base i src).Fits w (endAddress base N bound M) ∧
    Source (expr width b bound M base i src) (fun h g=>(x h g).val : Fin H→Fin G→Cell b) M
      (image width b bound M base m) :=by
  let top:=endAddress base N bound M
  let out:=image width b bound M base m
  have printed:=any width b bound M base m small room
  have sides:=Book.geometry (gates width b) bound M base i (out:=top) le_rfl room
    (by simpa only [gates,Nat.add_zero] using small i)
  have sliced : DescentPackedZip.Fits (tables width b bound M base i) src (.lit 0) (width i) 0 M top w :=by
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) fit,trivial,
      sides.1,sides.2,by simp [tables,Book.tables,gates],by simp [tables,Book.tables,gates]⟩
  have stable : Source src x M out:=fun p=>(eval_below src _ m out fit
    (fun z hz=>printed.2.2.1 z (.inl hz))).trans (read p)
  have zero : Source (.lit 0) (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) M out:=by
    intro p
    have sz:=(data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p).isLt
    simp only [Nat.zero_mul,pow_zero] at sz
    have eqn : (data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p).val=0:=by omega
    have empty : data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p=0:=Fin.ext eqn
    rw [empty]
    rfl
  exact ⟨⟨sliced.apply,sliced.right,sliced.shift,sliced.left⟩,
    read_data _ _ _ top sliced (convert (width i) b) rfl out (printed.2.2.2 i) _ _ stable zero⟩

end
end Hierarchy.DescentOperandInputCast

end OAI
