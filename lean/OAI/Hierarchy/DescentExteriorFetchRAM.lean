import OAI.Hierarchy.DescentExteriorShelfOperands
import OAI.Hierarchy.DescentExteriorLookup
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # A cheap native row read and within-row permutation for each exterior chunk -/
namespace Hierarchy.DescentExteriorFetch
open DescentExterior DescentGL Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section

structure Banks where
  key : Bank
  slab : Bank
  source : Bank
  offsets : Bank
  data : Bank
  table : Bank

def Banks.all (g : Banks) := [g.key,g.slab,g.source,g.offsets,g.data,g.table]

def gather (g : Banks) : Expr :=
  let k:=Expr.lookup g.key .row
  let src:=Expr.op .add (.lookup g.slab .row) (.lookup g.source k)
  .lookup g.table (.op .add (.lookup g.offsets k) (.lookup g.data src))

theorem gather_work (g : Banks) : (gather g).work=43 := rfl

def program (bits out n : ℕ) (g : Banks) := scan bits out n (gather g)
variable {bits j r t e : ℕ}
local notation "R" => 2^(j+r)
local notation "radix" => 2^(2^j*t)
local notation "keys" => 2^(keyBits j r)
local notation "I" => Fin (e*R)

def encoded (M : Fin e→Layout (j+(j+r))) (i : I) :=
  keyIndex j r (key (M (slab i)) (dest i))

def Inputs (g : Banks) (p : Fin 3) (M : Fin e→Layout (j+(j+r)))
    (x : Fin e→Plane j r→Fin t→Bool) (m : Memory bits) : Prop :=
  (∀i:I,m (g.key.base+i.val)=((encoded M i).val:Word bits)) ∧
  (∀i:I,m (g.slab.base+i.val)=(((slab i).val*R:ℕ):Word bits)) ∧
  (∀a:Fin keys,m (g.source.base+a.val)=((source j r p ((keyIndex j r).symm a)).val:Word bits)) ∧
  (∀a:Fin keys,m (g.offsets.base+a.val)=((a.val*radix:ℕ):Word bits)) ∧
  (∀(a:Fin e) (v:Rows j r),m (g.data.base+(a.val*R+(rowOrd j r v).val))=
    ((pack (fun l=>x a (l,v))).val:Word bits)) ∧
  (∀(a:Fin keys) (d:Word (2^j*t)),m (g.table.base+(a.val*radix+d.val))=
    ((entry j r t p ((keyIndex j r).symm a) d).val:Word bits))

def result (p : Fin 3) (M : Fin e→Layout (j+(j+r))) (x : Fin e→Plane j r→Fin t→Bool) (i : I) :
    Word (2^j*t) := pack (fun a=>push (pass (M (slab i)) p) (x (slab i)) (a,dest i))

private theorem bank_nat (g : Bank) (m : Memory bits) (a out : ℕ) (ha : a<g.size)
    (fit : g.Fits bits out) : g.read m (a : Word bits)=m (g.base+a) := by
  simp [Bank.read,Fin.val_cast_of_lt (ha.trans fit.2.1),Nat.mod_eq_of_lt ha]

theorem read {out : ℕ} (g : Banks) (fits : ∀b∈g.all,b.Fits bits out)
    (gk : e*R≤g.key.size) (gs : e*R≤g.slab.size) (offset : keys≤g.offsets.size)
    (dir : keys≤g.source.size) (rows : e*R≤g.data.size) (tab : keys*radix≤g.table.size)
    (p : Fin 3) (M : Fin e→Layout (j+(j+r))) (x : Fin e→Plane j r→Fin t→Bool)
    (m : Memory bits) (input : Inputs g p M x m) (i : I) :
    (gather g).eval m (i.val : Word bits)=((result p M x i).val:Word bits) := by
  obtain ⟨hkey,hslab,hsrc,hoff,hdata,htab⟩:=input
  let k:=encoded M i
  let a:=slab i
  let d:=dest i
  let z:=((pass (M a) p).row.symm d)
  let data:=pack (fun l=>x a (l,z))
  have dataIdx : a.val*R+(rowOrd j r z).val<g.data.size := by
    have h : (a.val+1)*R≤e*R := Nat.mul_le_mul_right R a.isLt
    have hr:=(rowOrd j r z).isLt
    rw [Nat.add_mul,Nat.one_mul] at h
    omega
  have kz : (keyIndex j r).symm k=key (M a) d := (keyIndex j r).symm_apply_apply _
  have tableIdx : k.val*radix+data.val<g.table.size := by
    have h : (k.val+1)*radix≤keys*radix := Nat.mul_le_mul_right radix k.isLt
    have hr:=data.isLt
    rw [Nat.add_mul,Nat.one_mul] at h
    omega
  simp only [gather,Expr.eval,RowOp.opcode,BinaryOp.eval]
  rw [bank_nat g.key m _ out (i.isLt.trans_le gk) (fits _ (by simp [Banks.all])),hkey]
  change g.table.read m (g.offsets.read m (k.val:Word bits)+
    g.data.read m (g.slab.read m (i.val:Word bits)+g.source.read m (k.val:Word bits)))=_
  rw [bank_nat g.offsets m _ out (k.isLt.trans_le offset) (fits _ (by simp [Banks.all])),hoff,
    bank_nat g.slab m _ out (i.isLt.trans_le gs) (fits _ (by simp [Banks.all])),hslab,
    bank_nat g.source m _ out (k.isLt.trans_le dir) (fits _ (by simp [Banks.all])),hsrc,
    kz,source_key,←Nat.cast_add,bank_nat g.data m _ out dataIdx (fits _ (by simp [Banks.all])),hdata,
    ←Nat.cast_add,bank_nat g.table m _ out tableIdx (fits _ (by simp [Banks.all])),htab,kz,entry_key]
  rfl

theorem spec (out : ℕ) (g : Banks) (fits : ∀b∈g.all,b.Fits bits out)
    (gk : e*R≤g.key.size) (gs : e*R≤g.slab.size) (offset : keys≤g.offsets.size)
    (dir : keys≤g.source.size) (rows : e*R≤g.data.size) (tab : keys*radix≤g.table.size)
    (p : Fin 3) (M : Fin e→Layout (j+(j+r))) (x : Fin e→Plane j r→Fin t→Bool) (stop : out+e*R<2^bits) :
    (program bits out (e*R) g).Spec (Inputs g p M x)
      (fun m after=>after=image out (e*R) (gather g) m ∧
        ∀i:I,after (out+i.val)=((result p M x i).val:Word bits)) (4+90*(e*R)) ∧
      CheapCode (program bits out (e*R) g) := by
  refine ⟨?_,@scan_cheap _ _ _ _⟩
  have fit : (gather g).Fits bits out := by
    simp only [gather,Expr.Fits,fits g.key (by simp [Banks.all]),fits g.slab (by simp [Banks.all]),
      fits g.source (by simp [Banks.all]),fits g.data (by simp [Banks.all]),
      fits g.offsets (by simp [Banks.all]),fits g.table (by simp [Banks.all]),and_self]
  intro P N K machine pc reg pub exit rom «public» cfg m start input
  obtain ⟨time,he,done,after,run,ended,mem⟩ := scan_exec out (e*R) (gather g) m fit stop
    machine pc reg pub exit rom «public» cfg m start rfl
  refine ⟨time,by simpa [gather_work,Nat.mul_comm] using he,done,after,run,ended,mem,?_⟩
  intro i
  rw [mem]
  simpa [ProtocolRAM.image,fillSegment,show out≤out+i.val ∧ out+i.val<out+e*R by have:=i.isLt;omega,
    Nat.cast_add] using read g fits gk gs offset dir rows tab p M x m input i

end
end Hierarchy.DescentExteriorFetch

end OAI
