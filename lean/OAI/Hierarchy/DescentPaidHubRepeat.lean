import OAI.Hierarchy.DescentSIMDLookup
import OAI.Hierarchy.DescentNativeBankLookup
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Broadcasting each physical one-bit hub word across the live group lanes at its previous host -/
namespace Hierarchy.DescentPaidResidentCount.HubRepeat
open DescentSIMDLookup DescentIssuedTerminalId ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (base H G M : ℕ)
def bits :=Nat.clog 2 (H*chunks G M)
def span :=2^(bits H G M)
def hosts : Bank :=⟨base,bits H G M⟩
def mask : Bank :=⟨base+span H G M,bits H G M⟩
def bank : Bank :=⟨base+2*span H G M,bits H G M⟩
def roof :=base+3*span H G M

theorem roof_affine : roof base H G M=base+roof 0 H G M :=by simp [roof]
theorem room : H*chunks G M≤ span H G M:=Nat.le_pow_clog (by decide) _

theorem bank_fits {w : ℕ} (space : roof base H G M<2^w) :
    (bank base H G M).Fits w (roof base H G M) :=by
  have pos : 0< span H G M:=Nat.two_pow_pos _
  change base+3*span H G M<2^w at space
  change 0< span H G M ∧ span H G M<2^w ∧ base+2*span H G M+span H G M≤base+3*span H G M
  omega

def page (i : ℕ) : ℕ :=
  if i< span H G M then
    if h : i<H*chunks G M then ((row H G M).symm ⟨i,h⟩).1.val else 0
  else if h : i-span H G M<H*chunks G M then
    (data (fun (_ : Fin H) (_ : Fin G)=>(1:Cell 1)) ((row H G M).symm ⟨i-span H G M,h⟩)).val else 0

def expr (scalar : Bank) : Expr :=
  .branch .eq (.lookup scalar (.lookup (hosts base H G M) .row)) (.lit 0) (.lit 0)
    (.lookup (mask base H G M) .row)

variable (scalar : Bank)
local notation "rows" => H*chunks G M
local notation "width" => span H G M
local notation "out" => (bank base H G M).base
local notation "field" => expr base H G M scalar

def program (w : ℕ) :=
  (DescentStaticWordColumn.program w base (page H G M) (2*width)).seq (scan w out rows field)
def ticks := (4+10*(2*width))+(4+rows*(2*(field).work+4))
def image {w : ℕ} (m : Memory w) :=
  ProtocolRAM.image out rows field (DescentStaticWordColumn.image base (page H G M) m (2*width))

theorem expr_work : (field).work=22 :=rfl

theorem cheap (w : ℕ) : CheapCode (program base H G M scalar w) :=by
  intro P R K pc reg pub exit i
  exact cheap_seq (DescentStaticWordColumn.cheap w base (page H G M) (2*width))
    (scan_cheap w out rows field) pc reg pub exit i

theorem any {w : ℕ} (m : Memory w) (previous : scalar.Fits w base) (fits : roof base H G M<2^w) :
    (program base H G M scalar w).Exec m (image base H G M scalar m) (ticks base H G M scalar) ∧
    (∀q,q<base ∨ roof base H G M≤q→image base H G M scalar m q=m q) ∧
    CheapCode (program base H G M scalar w) :=by
  have old:=room H G M
  have big : width>0:=Nat.two_pow_pos _
  have lower : base+2*width<2^w:=by change base+3*width<2^w at fits;omega
  have sizeFit : width<2^w:=by omega
  have early : base≤out:=Nat.le_add_right _ _
  have a : (hosts base H G M).Fits w out:=⟨big,sizeFit,by change base+width≤base+2*width;omega⟩
  have c : (mask base H G M).Fits w out:=⟨big,sizeFit,by change base+width+width≤base+2*width;omega⟩
  have access : (field).Fits w out :=
    ⟨⟨⟨previous.1,previous.2.1,previous.2.2.trans early⟩,a,trivial⟩,trivial,trivial,c,trivial⟩
  have spanRoom : out+rows≤roof base H G M:=by change base+2*width+rows≤base+3*width;omega
  let mid:=DescentStaticWordColumn.image base (page H G M) m (2*width)
  refine ⟨?_,?_,?_⟩
  · intro P R K mach
    exact Procedure.Exec.then (DescentStaticWordColumn.mount base (2*width) (page H G M) m lower)
      (scan_exec out rows field mid access (spanRoom.trans_lt fits)) mach
  · intro q avoid
    exact (ProtocolRAMGeneratedWrite.frame_image out rows field mid q
      (avoid.imp (fun h=>h.trans_le early) (fun h=>spanRoom.trans h))).trans
      (DescentStaticWordColumn.frame base (2*width) (page H G M) m q
        (avoid.imp_right (fun h=>(Nat.le_add_right out rows).trans (spanRoom.trans h))))
  · intro P R K pc reg pub exit i
    exact cheap_seq (DescentStaticWordColumn.cheap w base (page H G M) (2*width))
      (scan_cheap w out rows field) pc reg pub exit i

theorem issued {w : ℕ} (m : Memory w) (previous : scalar.Fits w base) (capacity : H≤ scalar.size)
    (hub : Fin H→ Cell 1) (actual : ∀v : Fin H,m (scalar.base+v.val)=((hub v).val:Word w)) (fits : roof base H G M<2^w)
    (a : Row H G M) :
    image base H G M scalar m (out+(row H G M a).val)=((data (fun h (_ : Fin G)=>hub h) a).val:Word w) :=by
  let i:=(row H G M a).val
  let mid:=DescentStaticWordColumn.image base (page H G M) m (2*width)
  have ir : i<rows:=(row H G M a).isLt
  have iw : i<width:=ir.trans_le (room H G M)
  have wp : 0<width:=Nat.two_pow_pos _
  have bytes : width<2^w:=by change base+3*width<2^w at fits;omega
  have one : 1<2^w:=by change base+3*width<2^w at fits;omega
  have first : page H G M i=a.1.val:=by
    simp only [page,ite_eq_left iw,dite_eq_left ir,i,Fin.eta,Equiv.symm_apply_apply]
  have second : page H G M (width+i)=(data (fun (_ : Fin H) (_ : Fin G)=>(1:Cell 1)) a).val:=by
    simp only [page,ite_eq_right (by omega : ¬width+i<width),Nat.add_sub_cancel_left,
      dite_eq_left ir,i,Fin.eta,Equiv.symm_apply_apply]
  have primary : (Expr.lookup (hosts base H G M) .row).eval mid (i:Word w)=(a.1.val:Word w) :=by
    rw [lookup_nat (hosts base H G M) mid _ .row i rfl iw bytes]
    exact (DescentStaticWordColumn.read base (2*width) (page H G M) m (by omega : i<2*width)).trans
      (congrArg (fun n : ℕ=>(n:Word w)) first)
  have lookup : (Expr.lookup scalar (.lookup (hosts base H G M) .row)).eval mid (i:Word w)=((hub a.1).val:Word w) :=by
    rw [lookup_nat _ mid _ _ a.1.val primary (a.1.isLt.trans_le capacity) previous.2.1]
    exact (DescentStaticWordColumn.frame base (2*width) (page H G M) m _ (.inl
      ((Nat.add_lt_add_left (a.1.isLt.trans_le capacity) _).trans_le previous.2.2))).trans (actual _)
  have keep : (Expr.lookup (mask base H G M) .row).eval mid (i:Word w)=
      ((data (fun (_ : Fin H) (_ : Fin G)=>(1:Cell 1)) a).val:Word w) :=by
    rw [lookup_nat (mask base H G M) mid _ .row i rfl iw bytes]
    change mid (base+width+i)=_
    rw [Nat.add_assoc]
    exact (DescentStaticWordColumn.read base (2*width) (page H G M) m (by omega : width+i<2*width)).trans
      (congrArg (fun n : ℕ=>(n:Word w)) second)
  rw [image,ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row H G M a)]
  change (if DescriptorExpr.Comparison.eq.test ((Expr.lookup scalar (.lookup (hosts base H G M) .row)).eval mid (i:Word w)) 0
    then 0 else (Expr.lookup (mask base H G M) .row).eval mid (i:Word w))=_
  rw [lookup,keep]
  have digit : hub a.1=0 ∨ hub a.1=1:=by
    have h:=(hub a.1).isLt
    change (hub a.1).val<2 at h
    have dz : (hub a.1).val=0 ∨ (hub a.1).val=1:=by omega
    rcases dz with z|z
    · exact .inl (Fin.ext z)
    · exact .inr (Fin.ext z)
  have flat : data (fun h (_ : Fin G)=>hub h) a=data (fun (_ : Fin H) (_ : Fin G)=>hub a.1) a:=rfl
  rw [flat]
  rcases digit with z|z
  · have clear : data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 1)) a=0 :=by
      apply Fin.ext
      change (finFunctionFinEquiv (fun j : Fin M=>if h : a.2.val*M+j.val<G then (0:Cell 1) else 0)).val=0
      simp
    simp [z,clear,DescriptorExpr.Comparison.test]
  · have nz : (1:Word w)≠0 :=by
      intro h;have bad:=congrArg Fin.val h
      change ((1:ℕ):Fin (2^w)).val=0 at bad
      rw [Fin.val_cast_of_lt one] at bad
      contradiction
    simp [z,DescriptorExpr.Comparison.test,nz]

theorem tariff (w : ℕ) : ticks base H G M scalar+7*DescentStaticWordColumn.names (program base H G M scalar w)
    ≤640*(width+rows+1) :=by
  simp only [ticks,program,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount,
    DescentStaticWordColumn.names_scan,expr_work]
  have positive : 0<width:=Nat.two_pow_pos _
  omega

end
end Hierarchy.DescentPaidResidentCount.HubRepeat

end OAI
