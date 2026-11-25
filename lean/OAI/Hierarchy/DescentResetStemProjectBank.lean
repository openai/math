import OAI.Hierarchy.DescentVectorBookReshape

namespace OAI
/-! # Reading each projected block of a stem from the vector transpose -/
namespace Hierarchy.DescentResetStemProject
open DescentSIMDLookup DescentPackedZip ProtocolRAM DescentVectorBookReshape
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section

variable {out H G M X N w a : ℕ}

def page (out H G M X : ℕ) (q : Fin N) (x : Fin X) : Bank :=
  blockBank out H 1 G X M q x

def pageEnd (out N H G M X : ℕ) :=
  out+N*rows H 1 G X M+2^Nat.clog 2 (H*chunks G M+1)

theorem page_capacity (q : Fin N) (x : Fin X) : H*chunks G M≤(page out H G M X q x).size := by
  simpa only [page,Nat.mul_one] using blockBank_capacity out H 1 G X M q x

theorem page_fits (q : Fin N) (x : Fin X) (room : pageEnd out N H G M X<2^w) :
    (page out H G M X q x).Fits w (pageEnd out N H G M X) := by
  let width:=H*chunks G M
  have dims : rows H 1 G X M=X*width := by simp only [rows,Nat.mul_one,width]
  have last : q.val*(X*width)+X*width≤N*(X*width) := by
    rw [←Nat.succ_mul]
    exact Nat.mul_le_mul_right _ q.isLt
  have within : x.val*width≤X*width := Nat.mul_le_mul_right _ x.isLt.le
  have top : (page out H G M X q x).base≤out+N*rows H 1 G X M := by
    simp only [page,blockBank,DescentScalarBookReshape.dest,destBase,dims,Nat.mul_one]
    change out+q.val*(X*width)+x.val*width≤out+N*(X*width)
    omega
  have sz : (page out H G M X q x).size=2^Nat.clog 2 (width+1) := by
    simp only [page,blockBank,Bank.size,Nat.mul_one,width]
  unfold pageEnd at room ⊢
  refine ⟨Nat.two_pow_pos _,?_,?_⟩
  · rw [sz]
    dsimp only [width]
    omega
  · rw [sz]
    exact Nat.add_le_add_right top _

/-- The output of the one-key vector batch has its only key coordinate equal to
zero. Removing that coordinate keeps the same physical row and every padding lane. -/
theorem page_read (Y : Fin N→Fin H→Fin (G*X)→Cell a) (m : Memory w)
    (read : ∀q (x : Fin X) (p : Row (H*1) G M),
      m (DescentScalarBookReshape.dest H 1 G M (destBase out H 1 G X M q) x+
        (row (H*1) G M p).val)=((data (DescentScalarBookReshape.book (fun _ : Fin 1=>Y q) x) p).val:Word w))
    (q : Fin N) (x : Fin X) (p : Row H G M) :
    m ((page out H G M X q x).base+(row H G M p).val)=
      ((data (fun v g=>Y q v (finProdFinEquiv (g,x))) p).val:Word w) := by
  let lifted : Row (H*1) G M:=(finProdFinEquiv (p.1,(0:Fin 1)),p.2)
  have addr : (row (H*1) G M lifted).val=(row H G M p).val := by
    change p.2.val+chunks G M*(0+1*p.1.val)=p.2.val+chunks G M*p.1.val
    simp
  have value : data (DescentScalarBookReshape.book (fun _ : Fin 1=>Y q) x) lifted=
      data (fun v g=>Y q v (finProdFinEquiv (g,x))) p := by
    simp only [data,DescentScalarBookReshape.book,lifted,Equiv.symm_apply_apply]
  have h:=read q x lifted
  rw [addr,value] at h
  exact h

theorem page_source (Y : Fin N→Fin H→Fin (G*X)→Cell a) (m : Memory w)
    (read : ∀q (x : Fin X) (p : Row (H*1) G M),
      m (DescentScalarBookReshape.dest H 1 G M (destBase out H 1 G X M q) x+
        (row (H*1) G M p).val)=((data (DescentScalarBookReshape.book (fun _ : Fin 1=>Y q) x) p).val:Word w))
    (room : pageEnd out N H G M X<2^w) (q : Fin N) (x : Fin X) :
    Source (.lookup (page out H G M X q x) .row) (fun v g=>Y q v (finProdFinEquiv (g,x))) M m :=
  source_column _ _ (page_fits q x room) m _ (page_capacity q x) (page_read Y m read q x)

end
end Hierarchy.DescentResetStemProject

end OAI
