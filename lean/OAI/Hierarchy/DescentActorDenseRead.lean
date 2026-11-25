import OAI.Hierarchy.DescentActorCompactRAM
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Dense padded coordinates for genuine reset actor pages -/
namespace Hierarchy.DescentActorRaster.DenseRead
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def seats (B H K : ℕ) : Fin B × (Fin H × Fin K) ≃ Fin (B*(H*K)) :=
  ((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv

def page (base len : ℕ) : Bank := ⟨base,Nat.clog 2 len⟩
def host (B H K lo : ℕ) :=page lo (B*(H*K))
def offset (B H K lo : ℕ) :=page (lo+(host B H K lo).size) (B*(H*K))
def stride (B H K lo raw : ℕ) :=page ((offset B H K lo).base+(offset B H K lo).size) raw
def cells (B H K lo raw : ℕ) :=2*(host B H K lo).size+(stride B H K lo raw).size

def literals (B H K lo raw : ℕ) (p : ℕ) : ℕ :=
  let pad:=(host B H K lo).size
  if _h:p<pad then
    if q:p<B*(H*K) then ((seats B H K).symm ⟨p,q⟩).2.1.val else 0
  else if _l:p<2*pad then
    if q:p-pad<B*(H*K) then
      let z:=(seats B H K).symm ⟨p-pad,q⟩
      z.1.val*(raw*K)+z.2.2.val
    else 0
  else (p-2*pad)*K

def expr (B H K lo raw : ℕ) (cnt inv src : Bank) : Expr :=
  let h:=Expr.lookup (host B H K lo) .row
  .branch .lt h (.lookup cnt (.lit 0))
    (.lookup src (.op .add (.lookup (offset B H K lo) .row)
      (.lookup (stride B H K lo raw) (.lookup inv h)))) (.lit 0)

def proc (B H K lo raw start w : ℕ) (cnt inv src : Bank) :=
  (DescentStaticWordColumn.program w lo (literals B H K lo raw) (cells B H K lo raw)).seq
    (scan w start (B*(H*K)) (expr B H K lo raw cnt inv src))

variable {B H K raw w used : ℕ} (rank : Fin used→Fin raw)
def dense (x : Fin B→Fin raw→Fin K→Word w) (b : Fin B) (h : Fin H) (j : Fin K) :=
  if ok : h.val<used then x b (rank ⟨h.val,ok⟩) j else 0

theorem run (lo out : ℕ) (cnt inv src : Bank) (m : Memory w)
    (x : Fin B→Fin raw→Fin K→Word w) (stored : ∀b h j,m (src.base+(b.val*(raw*K)+h.val*K+j.val))=x b h j)
    (fit : (expr B H K lo raw cnt inv src).Fits w out) (rawSize : B*(raw*K)≤ src.size)
    (countSize : 0<cnt.size) (invSize : used≤ inv.size)
    (contiguous : cnt.base+cnt.size≤lo ∧ inv.base+inv.size≤lo ∧ src.base+src.size≤lo)
    (count : m cnt.base=(used:Word w)) (ids : ∀i : Fin used,m (inv.base+i.val)=((rank i).val:Word w))
    (prior : lo+cells B H K lo raw≤out) (room : out+B*(H*K)<2^w) (hSmall : H≤2^w) (live : used<2^w)
    (_hostFit : H>0) (_chunkFit : 0<K) :
    let decl:=DescentStaticWordColumn.image lo (literals B H K lo raw) m (cells B H K lo raw)
    let done:=ProtocolRAM.image out (B*(H*K)) (expr B H K lo raw cnt inv src) decl
    (proc B H K lo raw out w cnt inv src).Exec m done
      ((4+10*cells B H K lo raw)+(4+B*(H*K)*(2*(expr B H K lo raw cnt inv src).work+4))) ∧
      (∀b h j,done (out+((seats B H K) (b,h,j)).val)=dense rank x b h j) ∧
      ∀a,a<lo ∨ out+B*(H*K)≤a→done a=m a := by
  let p:=host B H K lo
  let o:=offset B H K lo
  let d:=stride B H K lo raw
  let decl:=DescentStaticWordColumn.image lo (literals B H K lo raw) m (cells B H K lo raw)
  have mountRoom:lo+cells B H K lo raw<2^w:=by omega
  have held (a : ℕ) (before : a<lo) : decl a=m a:=
    DescentStaticWordColumn.frame lo _ _ m _ (Or.inl before)
  have f₀:p.Fits w out:=fit.1.1
  have f₁:cnt.Fits w out:=fit.2.1.1
  have f₂:o.Fits w out:=fit.2.2.1.2.1.1
  have f₃:d.Fits w out:=fit.2.2.1.2.2.1
  have f₄:inv.Fits w out:=fit.2.2.1.2.2.2.1
  have f₅:src.Fits w out:=fit.2.2.1.1
  have maxRow:B*(H*K)≤p.size:=Nat.le_pow_clog (by decide) _
  have maxRaw:raw≤d.size:=Nat.le_pow_clog (by decide) _
  have pp:o.size=p.size:=rfl
  have cc:cells B H K lo raw=2*p.size+d.size:=rfl
  have literal (i : ℕ) (inside : i<cells B H K lo raw) :
      decl (lo+i)=(literals B H K lo raw i:Word w) :=
    DescentStaticWordColumn.read lo _ _ m inside
  have pub (i : Fin (B*(H*K))) : decl (lo+i.val)=(((seats B H K).symm i).2.1.val:Word w):=by
    rw [literal _ (by rw [cc];omega : i.val<cells B H K lo raw)]
    simp [literals,show i.val<(host B H K lo).size from i.isLt.trans_le maxRow,i.isLt]
  have off (i : Fin (B*(H*K))) : decl (o.base+i.val)=
      ((((seats B H K).symm i).1.val*(raw*K)+((seats B H K).symm i).2.2.val:ℕ):Word w):=by
    change decl (lo+p.size+i.val)=_
    rw [Nat.add_assoc,literal _ (by rw [cc];omega : p.size+i.val<cells B H K lo raw)]
    simp [literals,show (host B H K lo).size=p.size from rfl,Nat.not_lt.mpr (Nat.le_add_right ..),
      show p.size+i.val<2*p.size by omega,i.isLt]
  have scale (j : Fin raw) : decl (d.base+j.val)=((j.val*K:ℕ):Word w):=by
    change decl ((lo+p.size+p.size)+j.val)=_
    rw [show lo+p.size+p.size+j.val=lo+(2*p.size+j.val) by omega,
      literal _ (by rw [cc];omega : 2*p.size+j.val<cells B H K lo raw)]
    simp [literals,show (host B H K lo).size=p.size from rfl,show ¬2*p.size+j.val<p.size by omega,
      show ¬2*p.size+j.val<2*p.size by omega]
  refine ⟨Procedure.Exec.then (DescentStaticWordColumn.mount lo _ (literals B H K lo raw) m mountRoom)
    (scan_exec _ _ _ decl fit room),?_,?_⟩
  · intro b h j
    let i:=(seats B H K) (b,h,j)
    have hd : p.read decl (i.val:Word w)=(h.val:Word w) :=by
      rw [bank_read _ _ (i.isLt.trans_le maxRow) f₀,show p.base=lo from rfl,pub];simp [i]
    have od : o.read decl (i.val:Word w)=((b.val*(raw*K)+j.val:ℕ):Word w):=by
      rw [bank_read _ _ (i.isLt.trans_le (pp.symm ▸ maxRow)) f₂,off];simp [i]
    have cd : cnt.read decl 0=(used:Word w):=by
      rw [show (0:Word w)=((0:ℕ):Word w) by rfl,bank_read _ _ countSize f₁,Nat.add_zero,held _ (by omega),count]
    rw [ProtocolRAMGeneratedWrite.read_image]
    change (if DescriptorExpr.Comparison.lt.test (p.read decl (i.val:Word w)) (cnt.read decl 0) then
      src.read decl (o.read decl (i.val:Word w) + d.read decl (inv.read decl (p.read decl (i.val:Word w))))
      else 0)=dense rank x b h j
    rw [hd,cd]
    simp only [DescriptorExpr.Comparison.test,Fin.lt_def,Fin.val_cast_of_lt (h.isLt.trans_le hSmall),Fin.val_cast_of_lt live,decide_eq_true_eq]
    by_cases hn:h.val<used
    · let u:Fin used:=⟨_,hn⟩
      let part:=rank u
      have iv:inv.read decl (h.val:Word w)=(part.val:Word w):=by
        rw [bank_read _ _ (hn.trans_le invSize) f₄,held _ (by omega)]
        exact ids u
      have readD:d.read decl (part.val:Word w)=((part.val*K:ℕ):Word w):=
        (bank_read _ _ (part.isLt.trans_le maxRaw) f₃).trans (scale part)
      have address:b.val*(raw*K)+j.val+part.val*K<B*(raw*K):=by
        have c1:part.val*K+j.val<(part.val+1)*K:=by rw [Nat.succ_mul];omega
        have c2 : (part.val+1)*K≤raw*K:=Nat.mul_le_mul_right K part.isLt
        have c3:=(Nat.mul_le_mul_right (raw*K) b.isLt)
        rw [Nat.succ_mul] at c3
        omega
      simp only [ite_eq_left hn,dense,dite_eq_left hn,od,iv,readD,←Nat.cast_add]
      rw [bank_read _ _ (address.trans_le rawSize) f₅,held _ (by omega)]
      simpa [u,part,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using stored b part j
    · simp [hn,dense]
  · intro a outside
    rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)]
    exact DescentStaticWordColumn.frame lo _ _ m _ (by omega)

end
end Hierarchy.DescentActorRaster.DenseRead

end OAI
