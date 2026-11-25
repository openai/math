import OAI.Hierarchy.DescentPackedMaskedData
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # Broadcast a measured host rank over active packed group lanes -/
namespace Hierarchy.DescentResetHaloBroadcast
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w H G M b S : ℕ}

def count (H G M b : ℕ) :=2*(H*chunks G M)+(M+1)*2^b
def bits (H G M b : ℕ) :=Nat.clog 2 (count H G M b+1)
def endAt (root H G M b : ℕ) :=root+2*(H*chunks G M)+2^(bits H G M b)
def point (b M n v : ℕ) : ℕ := (encode b M (fun j=>if j.val<n then ((v:ℕ):Cell b) else 0)).val

def literal (b G M : ℕ) (site : Fin H→Fin S) (i : ℕ) : ℕ :=
  let n:=H*chunks G M
  if first:i<n then (site ((row H G M).symm ⟨i,first⟩).1).val
  else if second:i-n<n then used G M ((row H G M).symm ⟨i-n,second⟩).2.val*2^b
  else let z:=i-2*n;point b M (z/2^b) (z%2^b)

def expr (src : Bank) (root H G M b : ℕ) : Expr :=
  let n:=H*chunks G M
  let ids : Bank:=⟨root,bits H G M b⟩
  let masks : Bank:=⟨root+n,bits H G M b⟩
  let page : Bank:=⟨root+2*n,bits H G M b⟩
  .lookup page (.op .add (.lookup masks .row) (.lookup src (.lookup ids .row)))

theorem amount (src : Bank) (root H G M b : ℕ) : (expr src root H G M b).work=25 := by rfl

private theorem point_read (f : Fin S→Cell b) (site : Fin H→Fin S) (p : Row H G M) :
    point b M (used G M p.2.val) (f (site p.1)).val=(data (fun a (_ : Fin G)=>f (site a)) p).val := by
  unfold point data
  congr 2
  funext j
  by_cases live:p.2.val*M+j.val<G
  · simp [active j live,live]
  · have no:¬j.val<used G M p.2.val := by
      intro h
      have positive:=lt_of_lt_of_le h (Nat.min_le_right .. : used G M p.2.val≤G-p.2.val*M)
      omega
    simp [no,live]

theorem schema_fit (src : Bank) (base H G M b : ℕ) (old : src.Fits w base) (room : endAt base H G M b<2^w) :
    (expr src base H G M b).Fits w (endAt base H G M b) := by
  let cells:=H*chunks G M
  let z:=2^(bits H G M b)
  have top : base+2*cells+z<2^w:=room
  have bank {at_ : ℕ} (loc : at_≤base+2*cells) :
      (⟨at_,bits H G M b⟩:Bank).Fits w (endAt base H G M b) :=
    ⟨Nat.two_pow_pos _,by change z<2^w;omega,by change at_+z≤base+2*cells+z;omega⟩
  have low : src.Fits w (endAt base H G M b):=
    ⟨old.1,old.2.1,old.2.2.trans ((Nat.le_add_right base (2*cells)).trans (Nat.le_add_right _ z))⟩
  exact ⟨bank le_rfl,⟨bank (by omega),trivial⟩,low,bank (by omega),trivial⟩

/-- The directory contains two physical words per packed row and one shared
dictionary of (live-lane count, scalar rank). The earlier input values are
read from their real host bank, including for receiver aliases. -/
theorem run (src : Bank) (root : ℕ) (site : Fin H→Fin S) (v : Fin S→Cell b) (m : Memory w)
    (old : src.Fits w root) (available : S ≤ src.size) (read : ∀i,m (src.base+i.val)=((v i).val:Word w))
    (room : endAt root H G M b<2^w) :
    let n:=count H G M b
    let f:=literal b G M site
    let final:=DescentStaticWordColumn.image root f m n
    (DescentStaticWordColumn.program w root f n).Exec m final (4+10*n) ∧
    Source (expr src root H G M b) (fun h (_ : Fin G)=>v (site h)) M final ∧
    (∀a,a<root ∨ root+n≤a→final a=m a) ∧ DescentStaticWordColumn.names (DescentStaticWordColumn.program w root f n)=15*(n+1) := by
  intro total f final
  let N:=H*chunks G M
  let Z:=(M+1)*2^b
  let u:=2^(bits H G M b)
  let ids:Bank:=⟨root,bits H G M b⟩
  let masks:Bank:=⟨root+N,bits H G M b⟩
  let page:Bank:=⟨root+2*N,bits H G M b⟩
  have size : total+1≤u:=Nat.le_pow_clog (by decide) _
  have past : root+2*N+u<2^w:=room
  have totalEq:total=2*N+Z:=rfl
  have enough:root+total<2^w:=by omega
  have fitIds:ids.Fits w (endAt root H G M b):=⟨Nat.two_pow_pos _,by change u<2^w;omega,by change root+u≤root+2*N+u;omega⟩
  have fitMasks:masks.Fits w (endAt root H G M b):=⟨Nat.two_pow_pos _,by change u<2^w;omega,by change root+N+u≤root+2*N+u;omega⟩
  have fitPage:page.Fits w (endAt root H G M b):=⟨Nat.two_pow_pos _,by change u<2^w;omega,le_rfl⟩
  have keep:=DescentStaticWordColumn.frame root total f m
  refine ⟨DescentStaticWordColumn.mount root total f m enough,?_,keep,DescentStaticWordColumn.names_mount ..⟩
  intro p
  let i:=row H G M p
  have small:i.val<N:=i.isLt
  have ir:i.val<u:=by omega
  let q:=used G M p.2.val
  let digit:=(v (site p.1)).val
  have bitsRoom:digit<2^b:=(v _).isLt
  have idx:q*2^b+digit<Z:=by
    calc
      _<q*2^b+2^b:=Nat.add_lt_add_left bitsRoom _
      _=(q+1)*2^b:=(Nat.succ_mul ..).symm
      _≤Z:=Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.min_le_left ..))
  have source:final (src.base+(site p.1).val)=(digit:Word w):=
    (keep _ (.inl ((Nat.add_lt_add_left ((site p.1).isLt.trans_le available) _).trans_le old.2.2))).trans (read _)
  have atRow (u : ℕ) (within : u<total) : final (root+u)=(f u:Word w) :=
    DescentStaticWordColumn.read root total f m within
  have idCell:final (ids.base+i.val)=((site p.1).val:Word w):=by
    change final (root+i.val)=_
    rw [atRow i.val (by omega)]
    simp [f,literal,N,i,small]
  have maskCell:final (masks.base+i.val)=((q*2^b:ℕ):Word w):=by
    change final (root+N+i.val)=_
    rw [Nat.add_assoc,atRow (N+i.val) (by omega)]
    simp [f,literal,N,show ¬N+i.val<N by omega,small,i,q]
  have valCell:final (page.base+(q*2^b+digit))=((point b M q digit):Word w):=by
    change final ((root+2*N)+(q*2^b+digit))=_
    rw [Nat.add_assoc,atRow (2*N+(q*2^b+digit)) (by omega)]
    have rest:¬2*N+(q*2^b+digit)-N<N:=by omega
    have first : ¬2*N+(q*2^b+digit)<N := by omega
    dsimp only [N] at first rest ⊢
    simp only [f,literal]
    split
    next hit => exact (first hit).elim
    next =>
      rw [Nat.add_sub_cancel_left,Nat.mul_comm q,Nat.mul_add_div (Nat.two_pow_pos b),
        Nat.div_eq_of_lt bitsRoom,Nat.add_zero,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt bitsRoom]
  change page.read final (masks.read final (i.val:Word w)+src.read final (ids.read final (i.val:Word w)))=_
  rw [bank_read masks final ir fitMasks,maskCell,bank_read ids final ir fitIds,idCell,
    bank_read src final ((site p.1).isLt.trans_le available) old,source,←Nat.cast_add,
    bank_read page final (by change q*2^b+digit<u; omega) fitPage,valCell,point_read v site p]

end
end Hierarchy.DescentResetHaloBroadcast

end OAI
