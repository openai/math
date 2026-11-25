import OAI.Hierarchy.DescentResetHaloBroadcast
import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Host-independent packed columns selected by one actual resident control word -/
namespace Hierarchy.DescentSharedSelectedColumns
open DescentSIMDLookup DescentDyadicSpan DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Layout where
  H : ℕ
  G : ℕ
  M : ℕ
  bits : ℕ
  keyBits : ℕ
  count : ℕ

namespace Layout
variable (L : Layout)
def pitch :=L.keyBits+Nat.clog 2 (chunks L.G L.M)
def rowBits:=Nat.clog 2 (L.H*chunks L.G L.M)
def rowBank (base : ℕ) : Bank:=⟨base,L.rowBits⟩
def tableBase (base : ℕ) :=base+2^L.rowBits
def table (base : ℕ) (j : Fin L.count) : Bank:=⟨L.tableBase base+j.val*2^L.pitch,L.pitch⟩
def endAddress (base : ℕ) :=L.tableBase base+L.count*2^L.pitch
def src (base : ℕ) (key : Bank) (j : Fin L.count) : Expr :=
  .lookup (L.table base j) (.op .add (.lookup (L.rowBank base) .row) (.lookup key (.lit 0)))
abbrev Fields:=Fin L.count→Cell L.keyBits→Fin L.G→Cell L.bits

def chunkValue (f : L.Fields) (j : Fin L.count) (idx : ℕ) :=
  if ht : idx/2^L.keyBits<chunks L.G L.M then
    (data (H:=1) (fun _=>f j ((idx:ℕ):Cell L.keyBits)) ((0:Fin 1),⟨_,ht⟩)).val
  else 0

def words (f : L.Fields) (i : ℕ) : ℕ :=
  if _low : i<2^L.rowBits then
    if valid : i<L.H*chunks L.G L.M then ((row L.H L.G L.M).symm ⟨i,valid⟩).2.val*2^L.keyBits else 0
  else
    let x:=i-2^L.rowBits
    if valid : x/2^L.pitch<L.count then L.chunkValue f ⟨_,valid⟩ (x%2^L.pitch) else 0

def size :=2^L.rowBits+L.count*2^L.pitch
def program (base : ℕ) (f : L.Fields) (w : ℕ) :=DescentStaticWordColumn.program w base (L.words f) L.size
def image {w : ℕ} (base : ℕ) (f : L.Fields) (m : Memory w) :=DescentStaticWordColumn.image base (L.words f) m L.size
def clock:=4+10*L.size

theorem any {w : ℕ} (base : ℕ) (f : L.Fields) (m : Memory w) (room : L.endAddress base<2^w) :
    (L.program base f w).Exec m (L.image base f m) L.clock ∧ CheapCode (L.program base f w) ∧
    ∀z,z<base ∨ L.endAddress base≤z→L.image base f m z=m z := by
  have fit : base+L.size<2^w:=by simpa only [size,endAddress,tableBase,Nat.add_assoc] using room
  refine ⟨DescentStaticWordColumn.mount base L.size (L.words f) m fit,
    @DescentStaticWordColumn.cheap _ _ _ _,?_⟩
  intro z hz
  apply DescentStaticWordColumn.frame
  simpa only [size,endAddress,tableBase,Nat.add_assoc] using hz

theorem src_fits {w : ℕ} (base : ℕ) (key : Bank) (j : Fin L.count) (low : key.Fits w base)
    (room : L.endAddress base<2^w) : (L.src base key j).Fits w (L.endAddress base) := by
  have start : base≤L.tableBase base:=Nat.le_add_right ..
  have ceiling : L.tableBase base≤L.endAddress base:=Nat.le_add_right ..
  have pages:=Nat.mul_le_mul_right (2^L.pitch) (Nat.succ_le_of_lt j.isLt)
  rw [Nat.succ_mul] at pages
  have tab : (L.table base j).Fits w (L.endAddress base) :=by
    have bound : (L.table base j).base+(L.table base j).size≤L.endAddress base:=by
      change L.tableBase base+j.val*2^L.pitch+2^L.pitch≤L.tableBase base+L.count*2^L.pitch
      omega
    exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (bound.trans_lt room),bound⟩
  have rows : (L.rowBank base).Fits w (L.endAddress base) :=by
    refine ⟨Nat.two_pow_pos _,?_,ceiling⟩
    change 2^L.rowBits<2^w
    exact (Nat.le_add_left ..).trans_lt (ceiling.trans_lt room)
  exact ⟨tab,⟨⟨rows,trivial⟩,⟨⟨low.1,low.2.1,low.2.2.trans (start.trans ceiling)⟩,trivial⟩⟩⟩

theorem read {w : ℕ} (base : ℕ) (key : Bank) (f : L.Fields) (m : Memory w) (j : Fin L.count)
    (picked : Cell L.keyBits) (seen : m key.base=(picked.val:Word w)) (low : key.Fits w base)
    (room : L.endAddress base<2^w) :
    Source (L.src base key j) (fun (_:Fin L.H) g=>f j picked g) L.M (L.image base f m) := by
  let a:=2^L.keyBits
  let D:=2^L.pitch
  let T:=2^L.rowBits
  have da : D=a*span (chunks L.G L.M):=by simp [D,pitch,a,span,pow_add]
  have count:=span_ge (L.H*chunks L.G L.M)
  have fits:=L.src_fits base key j low room
  have cap:=Nat.mul_le_mul_right D (Nat.succ_le_of_lt j.isLt)
  rw [Nat.succ_mul] at cap
  intro p
  let i:=row L.H L.G L.M p
  have ir : i.val<T:=i.isLt.trans_le count
  let x:=p.2.val*a+picked.val
  have xr : x<D:=by
    calc
      _<p.2.val*a+a:=Nat.add_lt_add_left picked.isLt _
      _=(p.2.val+1)*a:=(Nat.succ_mul ..).symm
      _≤(span (chunks L.G L.M))*a:=Nat.mul_le_mul_right _ (p.2.isLt.trans_le (span_ge _))
      _=D:=by rw [da,Nat.mul_comm]
  have idRead : L.image base f m (base+i.val)=((p.2.val*a:ℕ):Word w):=by
    rw [image,DescentStaticWordColumn.read base L.size (L.words f) m (ir.trans_le (Nat.le_add_right ..))]
    rw [words, dite_eq_left ir, dite_eq_left i.isLt]
    change ((((row L.H L.G L.M).symm i).2.val*a:ℕ):Word w)=_
    rw [show (row L.H L.G L.M).symm i=p from (row L.H L.G L.M).symm_apply_apply p]
  have keep:=(L.any base f m room).2.2
  have recorded : L.image base f m (key.base+0)=(picked.val:Word w):=by
    rw [Nat.add_zero,keep _ (.inl (by have h:=low.1;have k:=low.2.2;omega))];exact seen
  have literal : L.image base f m ((L.table base j).base+x)=
      ((data (fun (_:Fin L.H) g=>f j picked g) p).val:Word w) :=by
    change L.image base f m ((base+T+j.val*D)+x)=_
    rw [show base+T+j.val*D+x=base+(T+(j.val*D+x)) by omega,image,
      DescentStaticWordColumn.read base L.size (L.words f) m (show T+(j.val*D+x)<L.size by change _<T+L.count*D;omega)]
    have no : ¬T+(j.val*D+x)<T:=by omega
    have div_ : (j.val*D+x)/D=j.val:=by rw [Nat.mul_comm j.val,Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt xr,Nat.add_zero]
    have mod_ : (j.val*D+x)%D=x:=by rw [Nat.mul_comm j.val,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt xr]
    have digit : x/a=p.2.val:=by rw [show x=a*p.2.val+picked.val by simp [x,Nat.mul_comm],Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt picked.isLt,Nat.add_zero]
    have residue : (x:Cell L.keyBits)=picked:=by
      apply Fin.ext;change x%a=_
      rw [show x=a*p.2.val+picked.val by simp [x,Nat.mul_comm],Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt picked.isLt]
    have offset : T+(j.val*D+x)-2^L.rowBits=j.val*D+x := Nat.add_sub_cancel_left ..
    rw [words, dite_eq_right no]
    dsimp only
    rw [offset]
    change (((if valid : (j.val*D+x)/D<L.count then L.chunkValue f ⟨_,valid⟩ ((j.val*D+x)%D) else 0):ℕ):Word w)=_
    rw [div_, dite_eq_left j.isLt, mod_, chunkValue]
    have actual : x/2^L.keyBits=p.2.val := digit
    rw [actual, dite_eq_left p.2.isLt, residue]
    rfl
  change (L.table base j).read _ ((L.rowBank base).read _ (i.val:Word w)+key.read _ 0)=_
  rw [bank_read _ _ ir fits.2.1.1,show (L.rowBank base).base=base from rfl,idRead,show (0:Word w)=((0:ℕ):Word w) from rfl,bank_read _ _ low.1 low,recorded,
    ←Nat.cast_add,bank_read _ _ xr fits.1,literal]

end Layout
end
end Hierarchy.DescentSharedSelectedColumns

end OAI
