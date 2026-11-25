import OAI.Hierarchy.DescentDonorFreshRAM
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Literal word image and clock for the public per-leaf supply dictionaries -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Fresh.Book
open DescentSIMDLookup DescentPacking.PackedMatch ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (s : DepotRAM.Shape) (z : DescentPacking.PackedMatch.Shape) (K H G M : ℕ)
local notation "R" => rawBits s*M
local notation "T" => SixBirths.topology z M
local notation "U" => SixBirths.width z M
local notation "rows" => H*chunks G M

def bits := M+(R+T+U)
def physicalSize := rows+(2^R+(2^T+K*2^(bits s z M)))
abbrev Input := Fin (M+1)×(Cell R×(Cell T×Cell U))
abbrev Index := Fin rows ⊕ (Cell R ⊕ (Cell T ⊕ (Fin K×Cell (bits s z M))))

def rawIndex : Input s z M ≃ Fin ((M+1)*codeSize s z M) :=
  let tail := finProdFinEquiv (m:=2^T) (n:=2^U)
  let data := ((Equiv.refl (Cell R)).prodCongr tail).trans finProdFinEquiv
  (((Equiv.refl (Fin (M+1))).prodCongr data).trans finProdFinEquiv).trans
    (finCongr (by simp only [codeSize,pow_add];ring))

theorem raw_val (q : Input s z M) :
    (rawIndex s z M q).val=code s z q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  change q.2.2.2.val + 2^U*q.2.2.1.val + (2^T*2^U)*q.2.1.val +
    (2^R*(2^T*2^U))*q.1.val = _
  simp only [code,codeSize,pow_add]
  ring

theorem room : (M+1)*codeSize s z M ≤2^(bits s z M) := by
  change (M+1)*codeSize s z M ≤ 2^(M+(R+T+U))
  rw [pow_add (2 : ℕ) M (R+T+U)]
  exact Nat.mul_le_mul_right (codeSize s z M) Nat.lt_two_pow_self

def ordinal : Index s z K H G M ≃ Fin (physicalSize s z K H G M) :=
  let pages := finProdFinEquiv (m:=K) (n:=2^(bits s z M))
  let tails := ((Equiv.refl (Cell T)).sumCongr pages).trans finSumFinEquiv
  let tabs := ((Equiv.refl (Cell R)).sumCongr tails).trans finSumFinEquiv
  ((Equiv.refl (Fin rows)).sumCongr tabs).trans finSumFinEquiv

def bank (base : ℕ) (top born : Bank) : Fresh.Banks K where
  topology:=top
  births:=born
  active:=⟨base,Nat.clog 2 rows⟩
  terrainShift:=⟨base+rows,R⟩
  topShift:=⟨base+rows+2^R,T⟩
  dictionary q:=⟨base+rows+2^R+2^T+q.val*2^(bits s z M),bits s z M⟩

def address (base : ℕ) : Index s z K H G M→ℕ
  | .inl i=>base+i.val
  | .inr (.inl u)=>base+rows+u.val
  | .inr (.inr (.inl k))=>base+rows+2^R+k.val
  | .inr (.inr (.inr (q,t)))=>base+rows+2^R+2^T+q.val*2^(bits s z M)+t.val

theorem atOrdinal (base : ℕ) (j : Index s z K H G M) :
    address s z K H G M base j=base+(ordinal s z K H G M j).val := by
  rcases j with t|u|v|⟨q,p⟩
  · rfl
  · change base+rows+u.val = base+(rows+u.val)
    omega
  · change base+rows+2^R+v.val = base+(rows+(2^R+v.val))
    omega
  · change base+rows+2^R+2^T+q.val*2^(bits s z M)+p.val =
      base+(rows+(2^R+(2^T+(p.val+2^(bits s z M)*q.val))))
    ring

def words (B prof C pad scale : ℕ) : Index s z K H G M→ℕ
  | .inl i=>used G M ((row H G M).symm i).2.val*codeSize s z M
  | .inr (.inl u)=>u.val*2^(T+U)
  | .inr (.inr (.inl v))=>v.val*2^U
  | .inr (.inr (.inr (q,p)))=>
    if hi:p.val<(M+1)*codeSize s z M then
      let a:=(rawIndex s z M).symm ⟨p.val,hi⟩
      keyed s z B prof C pad scale q.val a.1.val a.2.1 a.2.2.1 a.2.2.2
    else 0

def data (B prof C pad scale : ℕ) (i : ℕ) : ℕ :=
  if inside:i<physicalSize s z K H G M then words s z K H G M B prof C pad scale ((ordinal s z K H G M).symm ⟨i,inside⟩) else 0

def install (w base B prof C pad scale : ℕ) :=
  DescentStaticWordColumn.program w base (data s z K H G M B prof C pad scale) (physicalSize s z K H G M)
def image {w : ℕ} (base B prof C pad scale : ℕ) (m : Memory w) :=
  DescentStaticWordColumn.image base (data s z K H G M B prof C pad scale) m (physicalSize s z K H G M)

theorem mount (w base B prof C pad scale : ℕ) (top born : Bank) (m : Memory w)
    (limit : base+physicalSize s z K H G M<2^w) :
    let result:=image s z K H G M base B prof C pad scale m
    (install s z K H G M w base B prof C pad scale).Exec m result (4+10*physicalSize s z K H G M) ∧
      Fresh.Fixed (H:=H) (G:=G) (M:=M) s z (bank s z K H G M base top born) B prof C pad scale result ∧
      ∀a,a<base ∨ base+physicalSize s z K H G M≤a→ result a=m a := by
  intro result
  have read (i : Index s z K H G M) : result (address s z K H G M base i)=(words s z K H G M B prof C pad scale i:Word w) := by
    rw [atOrdinal]
    have got:=DescentStaticWordColumn.read base (physicalSize s z K H G M) (data s z K H G M B prof C pad scale)
      m (j:=(ordinal s z K H G M i).val) (ordinal s z K H G M i).isLt
    have back : (ordinal s z K H G M).symm
        ⟨(ordinal s z K H G M i).val,(ordinal s z K H G M i).isLt⟩ = i :=
      (ordinal s z K H G M).symm_apply_apply i
    simpa only [result,image,data,dite_eq_left (ordinal s z K H G M i).isLt,back] using got
  refine ⟨DescentStaticWordColumn.mount base _ _ m limit,?_,DescentStaticWordColumn.frame base _ _ m⟩
  constructor
  · intro p;simpa [bank,address,words] using read (.inl (row H G M p))
  · intro v;exact read (.inr (.inl v))
  · intro v;exact read (.inr (.inr (.inl v)))
  · intro q n u v w'
    let args : Input s z M:=(n,u,v,w')
    let key:=rawIndex s z M args
    let idx : Cell (bits s z M):=key.castLE (room s z M)
    have exactKey : key.val=code s z n u v w':=raw_val s z M args
    have imageRead:=read (.inr (.inr (.inr (q,idx))))
    have recover : (rawIndex s z M).symm ⟨key.val,key.isLt⟩ = args :=
      (rawIndex s z M).symm_apply_apply args
    simpa only [address,words,idx,Fin.val_castLE,key.isLt,dite_eq_left,recover,args,bank,←exactKey]
      using imageRead

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Fresh.Book

end OAI
