import OAI.Hierarchy.DescentGLNielsen
import OAI.Hierarchy.DescentExteriorSelectedMatrix
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Native issue of the elementary row controls from the physically selected matrix -/
namespace Hierarchy.DescentGLControlCode
open DescentGL DescentGLNielsen Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {d w N : ℕ}

def Count (d : ℕ) := (schedule d).length

def liveFlag (L : Layout d) (i : Fin (Count d)) : Bool := ((controls L)[i.val]?).getD false

def flat (i : Fin (Count d)) (key : Fin N) : Fin (Count d*N) := finProdFinEquiv (i,key)

def code (name : Layout d ↪ Fin N) (j : Fin (Count d*N)) : ℕ :=
  let p:=finProdFinEquiv.symm j
  (Function.extend name (fun L=>liveFlag L p.1) (fun _=>false) p.2).toNat

theorem code_live (name : Layout d ↪ Fin N) (L : Layout d) (i : Fin (Count d)) :
    code name (flat i (name L))=(liveFlag L i).toNat := by
  simp only [code,flat,Equiv.symm_apply_apply,name.injective.extend_apply]

structure Tables where
  offsets : Bank
  switches : Bank

def Tables.expr (T : Tables) (k : Expr) := Expr.lookup T.switches (.op .add k (.lookup T.offsets .row))

def fits (T : Tables) (k : Expr) (w out : ℕ) : Prop :=
  k.Fits w out ∧ T.offsets.Fits w out ∧ T.switches.Fits w out

def installed (T : Tables) (name : Layout d ↪ Fin N) (mem : Memory w) : Prop :=
  (∀i : Fin (Count d),mem (T.offsets.base+i.val)=((N*i.val:ℕ):Word w)) ∧
    ∀j : Fin (Count d*N),mem (T.switches.base+j.val)=(code name j:Word w)

/-- Static switch rows contain only the true conditional Gaussian controls for each possible key. -/
def mount (T : Tables) (name : Layout d ↪ Fin N) (mem : Memory w) (addr : ℕ) : Word w :=
  if h : T.offsets.base≤addr ∧ addr<T.offsets.base+Count d then ((N*(addr-T.offsets.base):ℕ):Word w)
  else if h : T.switches.base≤addr ∧ addr<T.switches.base+Count d*N then
    (code name ⟨addr-T.switches.base,by omega⟩:Word w)
  else mem addr

theorem mounted (T : Tables) (name : Layout d ↪ Fin N) (mem : Memory w)
    (apart : T.offsets.base+Count d≤T.switches.base) : installed T name (mount T name mem) := by
  constructor
  · intro i
    have e:=i.isLt
    simp [mount,show T.offsets.base≤T.offsets.base+i.val ∧ T.offsets.base+i.val<T.offsets.base+Count d by omega]
  · intro ⟨j,hj⟩
    have off : ¬(T.offsets.base≤T.switches.base+j ∧ T.switches.base+j<T.offsets.base+Count d):=by omega
    have on : T.switches.base≤T.switches.base+j ∧ T.switches.base+j<T.switches.base+Count d*N:=by omega
    simp [mount,off,on]

theorem image_read (T : Tables) (name : Layout d ↪ Fin N) (k : Expr) (L : Layout d) (out : ℕ)
    (parts : fits T k w out) (offsets : Count d≤T.offsets.size) (space : Count d*N≤T.switches.size)
    (mem : Memory w) (pre : installed T name mem ∧ ∀i : Fin (Count d),k.eval mem (i.val:Word w)=((name L).val:Word w)) :
    ∀i : Fin (Count d),ProtocolRAM.image out (Count d) (T.expr k) mem (out+i.val)=((liveFlag L i).toNat:Word w) := by
  intro i
  have live : out≤out+i.val ∧ out+i.val<out+Count d:=by have:=i.isLt;omega
  simp only [ProtocolRAM.image,fillSegment,ite_eq_left live,Nat.cast_add,add_sub_cancel_left]
  let j:=flat i (name L)
  have ix:j.val=(name L).val+N*i.val:=rfl
  have offset : T.offsets.read mem (i.val : Word w) = ((N*i.val : ℕ) : Word w) :=
    (DescentPackedZip.bank_read T.offsets mem (i.isLt.trans_le offsets) parts.2.1).trans (pre.1.1 i)
  have indexWord : k.eval mem (i.val : Word w) + T.offsets.read mem (i.val : Word w) = (j.val : Word w) := by
    rw [pre.2 i,offset,ix,Nat.cast_add]
  change T.switches.read mem (k.eval mem (i.val : Word w) + T.offsets.read mem (i.val : Word w)) = _
  rw [indexWord]
  exact (DescentPackedZip.bank_read T.switches mem (j.isLt.trans_le space) parts.2.2).trans
    ((pre.1.2 j).trans (congrArg (fun n : ℕ => (n : Word w)) (code_live name L i)))

theorem native (T : Tables) (name : Layout d ↪ Fin N) (k : Expr) (L : Layout d) (out : ℕ)
    (parts : fits T k w out) (offsets : Count d≤T.offsets.size) (space : Count d*N≤T.switches.size)
    (high : out+Count d<2^w) :
    (scan w out (Count d) (T.expr k)).Spec
      (fun mem=>installed T name mem ∧ ∀i : Fin (Count d),k.eval mem (i.val:Word w)=((name L).val:Word w))
      (fun old mem=>mem=ProtocolRAM.image out (Count d) (T.expr k) old ∧
        ∀i : Fin (Count d),mem (out+i.val)=((liveFlag L i).toNat:Word w))
      (4+Count d*(2*(T.expr k).work+4)) ∧ CheapCode (scan w out (Count d) (T.expr k)) := by
  refine ⟨?_,scan_cheap w out (Count d) (T.expr k)⟩
  intro P R K mach pc reg pub exit rom regs cfg mem start pre
  have okay : (T.expr k).Fits w out:=⟨parts.2.2,parts.1,parts.2.1,trivial⟩
  obtain ⟨t,ticks,stop,nxt,ran,ended,eqn⟩:=scan_exec out (Count d) (T.expr k) mem okay high mach pc reg pub exit rom regs cfg mem start rfl
  refine ⟨t,ticks,stop,nxt,ran,ended,eqn,?_⟩
  simpa only [eqn] using image_read T name k L out parts offsets space mem pre

def rowName (d : ℕ) : Layout d ↪ Fin ((2^d)^d) :=
  ⟨DescentExteriorSelectedMatrix.ord,DescentExteriorSelectedMatrix.ord_injective d⟩

def chosenName (d : ℕ) : Layout d ↪ Word (d*d) := ⟨DescentExterior.matrixCode,DescentExterior.matrixCode_injective d⟩

theorem from_rows (T : Tables) (off : Bank) (ptr : Fin d→ℕ) (L : Layout d) (out : ℕ)
    (ofit : off.Fits w out) (room : (2^d)^d≤off.size) (wide : 1<2^w) (above : ∀i,ptr i<out)
    (mem : Memory w) (powers : ∀j : Fin ((2^d)^d),mem (off.base+j.val)=((2^d*j.val:ℕ):Word w))
    (actual : ∀i,mem (ptr i)=((rowIndex d (rowFunctional L i)).val:Word w))
    (real : installed T (rowName d) mem) :
    let key:=DescentExteriorSelectedMatrix.expr off d ptr
    key.Fits w out ∧ installed T (rowName d) mem ∧
      (∀i : Fin (Count d),key.eval mem (i.val:Word w)=(((rowName d) L).val:Word w)) ∧ key.work=1+12*d := by
  exact ⟨DescentExteriorSelectedMatrix.expr_fits off ofit wide d ptr above,real,
    fun i=>DescentExteriorSelectedMatrix.expr_read off ofit room mem powers d (by omega) ptr _ actual _,
    DescentExteriorSelectedMatrix.expr_work off d ptr⟩

theorem from_code (T : Tables) (B : Bank) (out : ℕ) (key : B.Fits w out) (L : Layout d)
    (mem : Memory w) (read : mem B.base=((DescentExterior.matrixCode L).val:Word w))
    (real : installed T (chosenName d) mem) :
    (Expr.lookup B (.lit 0)).Fits w out ∧ installed T (chosenName d) mem ∧
      ∀i : Fin (Count d),(Expr.lookup B (.lit 0)).eval mem (i.val:Word w)=(((chosenName d) L).val:Word w) := by
  refine ⟨⟨key,trivial⟩,real,?_⟩
  intro i
  simpa [Expr.eval,Bank.read,chosenName] using read

theorem rate (T : Tables) (k : Expr) : (T.expr k).work=k.work+13 := rfl

theorem table_price (d n : ℕ) (short : d*d≤n/2) :
    Count d*2^(d*d)≤(2*d*d)*2^(n/2) := by
  have length:=DescentGLNielsen.length d
  have le : Count d≤2*d*d := by
    unfold Count
    have lower:=Nat.mul_le_mul_left (3*d) (Nat.sub_le d 1)
    nlinarith
  exact Nat.mul_le_mul le (Nat.pow_le_pow_right (by decide) short)

end
end Hierarchy.DescentGLControlCode

end OAI
