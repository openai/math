import OAI.Hierarchy.DescentResetMeasuredPositions
import OAI.Hierarchy.DescentResetPortLevels
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # Short address programs for the previous host depth and paid port total -/
namespace Hierarchy.DescentPlainTerminal.Suffix.PortLevels
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentPackedColony.Phase DescentPackedWalsh
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w : ℕ}

structure AddressBook where
  origin : ℕ
  hosts : ℕ
  groups : ℕ
  batch : ℕ
  dimension : ℕ
  high : ℕ
  degree : ℕ

namespace AddressBook
variable (L : AddressBook)
def rows := L.hosts*chunks L.groups L.batch
def rbits := Nat.clog 2 L.rows
def hbits := Nat.clog 2 L.hosts
def pos : Bank := ⟨L.origin,L.rbits⟩
def depth : Bank := ⟨L.pos.base+L.pos.size,L.hbits⟩
def lead : Bank := ⟨L.depth.base+L.depth.size,L.hbits⟩
def stop := L.lead.base+L.lead.size
def index (h : ℕ) := (L.hosts*(L.dimension+1)+h*L.degree)*2^L.high
def chart : Arena.Image w := ⟨L.origin,L.stop,fun a=>
  if a<L.depth.base then
    if hi:a-L.origin<L.rows then
      ((DescentSIMDLookup.row L.hosts L.groups L.batch).symm ⟨_,hi⟩).1.val else 0
  else if a<L.lead.base then (((a-L.depth.base)*(L.dimension+1):ℕ):Word w)
  else L.index (a-L.lead.base)⟩

theorem addresses (mem : Memory w) (installed : L.chart.Resident mem) :
    (∀p : Row L.hosts L.groups L.batch,mem (L.pos.base+(DescentSIMDLookup.row _ _ _ p).val)=(p.1.val:Word w)) ∧
    (∀v : Fin L.hosts,mem (L.depth.base+v.val)=(v.val*(L.dimension+1):ℕ)) ∧
    (∀v : Fin L.hosts,mem (L.lead.base+v.val)=(L.index v.val:ℕ)) := by
  have rp : L.rows≤L.pos.size:=Nat.le_pow_clog (by decide) _
  have hp : L.hosts≤L.depth.size:=Nat.le_pow_clog (by decide) _
  have lp : L.hosts≤L.lead.size:=Nat.le_pow_clog (by decide) _
  have de : L.depth.base=L.origin+L.pos.size:=rfl
  have be : L.lead.base=L.depth.base+L.depth.size:=rfl
  have en : L.stop=L.lead.base+L.lead.size:=rfl
  refine ⟨?_,?_,?_⟩
  · intro p
    let j:=DescentSIMDLookup.row L.hosts L.groups L.batch p
    have h : j.val<L.rows:=j.isLt
    have hd:L.origin+j.val<L.depth.base:=by omega
    have rd:=installed (L.origin+j.val) (Nat.le_add_right ..) (by change _<L.stop;omega)
    change mem (L.origin+(DescentSIMDLookup.row _ _ _ p).val)=(p.1.val:Word w)
    simpa only [chart,ite_eq_left hd,Nat.add_sub_cancel_left,dite_eq_left h,Fin.eta,j,Equiv.symm_apply_apply] using rd
  · intro v
    have bound:=v.isLt
    have nd:¬L.depth.base+v.val<L.depth.base:=by omega
    have lb:L.depth.base+v.val<L.lead.base:=by omega
    have rd:=installed (L.depth.base+v.val) (by change L.origin≤_;omega) (by change _<L.stop;omega)
    simpa only [chart,ite_eq_right nd,ite_eq_left lb,Nat.add_sub_cancel_left] using rd
  · intro v
    have bound:=v.isLt
    have nd:¬L.lead.base+v.val<L.depth.base:=by omega
    have nl:¬L.lead.base+v.val<L.lead.base:=by omega
    have rd:=installed (L.lead.base+v.val) (by change L.origin≤_;omega) (by change _<L.stop;omega)
    simpa only [chart,ite_eq_right nd,ite_eq_right nl,Nat.add_sub_cancel_left] using rd

def host := Expr.lookup L.pos .row
def levelAt (levels : Bank) (v : Expr) := Expr.lookup levels (.lookup L.depth v)
def zeroAt (v : Expr) (j : ℕ) := Expr.op .add (.lookup L.lead v) (.lit (j*2^L.high))

theorem host_word (mem : Memory w) (out : ℕ) (static : L.chart.Resident mem) (fit : L.pos.Fits w out)
    (p : Row L.hosts L.groups L.batch) :
    L.host.eval mem ((DescentSIMDLookup.row _ _ _ p).val:Word w)=(p.1.val:Word w) := by
  have size:L.rows≤L.pos.size:=Nat.le_pow_clog (by decide) _
  exact (bank_read L.pos mem ((DescentSIMDLookup.row _ _ _ p).isLt.trans_le size) fit).trans ((L.addresses mem static).1 p)

theorem level_at (levels : Bank) (v : Expr) (mem : Memory w) (tick : Word w) (out : ℕ) (ord : Fin L.hosts)
    (static : L.chart.Resident mem) (fit : L.depth.Fits w out) (levelFit : levels.Fits w out)
    (hi : ord.val*(L.dimension+1)<levels.size) (h : v.eval mem tick=(ord.val:Word w)) :
    (L.levelAt levels v).eval mem tick=mem (levels.base+ord.val*(L.dimension+1)) := by
  have size:L.hosts≤L.depth.size:=Nat.le_pow_clog (by decide) _
  simp only [levelAt,Expr.eval,h,bank_read L.depth mem (ord.isLt.trans_le size) fit,
    (L.addresses mem static).2.1 ord,bank_read levels mem hi levelFit]

theorem zero_at (v : Expr) (j : ℕ) (mem : Memory w) (tick : Word w) (out : ℕ) (ord : Fin L.hosts)
    (static : L.chart.Resident mem) (fit : L.lead.Fits w out) (h : v.eval mem tick=(ord.val:Word w)) :
    (L.zeroAt v j).eval mem tick=(((L.hosts*(L.dimension+1)+ord.val*L.degree+j)*2^L.high:ℕ):Word w) := by
  have size:L.hosts≤L.lead.size:=Nat.le_pow_clog (by decide) _
  simp only [zeroAt,Expr.eval,h,bank_read L.lead mem (ord.isLt.trans_le size) fit,
    (L.addresses mem static).2.2 ord,RowOp.opcode,BinaryOp.eval,index,Nat.add_mul,Nat.cast_add]

def cutoff (levels total K scale bound : ℕ) : Arena.Image w :=
  ⟨L.stop,Cutoff.finish L.stop levels total,Cutoff.header L.stop levels total K scale bound (fun _=>0)⟩

theorem issue (levels total K scale bound : ℕ) (mem : Memory w) (room : Cutoff.finish L.stop levels total<2^w) :
    let I:Arena.Image w:=L.chart
    let J:Arena.Image w:=L.cutoff levels total K scale bound
    let dst:=J.output (I.output mem)
    (I.program.seq J.program).Exec mem dst (8+10*(Cutoff.finish L.stop levels total-L.origin)) ∧
    L.chart.Resident dst ∧ Cutoff.Resident L.stop levels total K scale bound dst ∧
    (∀a,a<L.origin ∨ Cutoff.finish L.stop levels total≤a→dst a=mem a) ∧ CheapCode (I.program.seq J.program) := by
  let I:Arena.Image w:=L.chart
  let J:Arena.Image w:=L.cutoff levels total K scale bound
  have a:L.origin≤L.stop:=by dsimp [stop,lead,depth,pos];omega
  have b:L.stop≤Cutoff.finish L.stop levels total:= (Nat.le_add_right L.stop _).trans (Nat.le_add_right ..)
  have ia : L.origin+(L.stop-L.origin)<2^w:=by omega
  have ib : L.stop+(Cutoff.finish L.stop levels total-L.stop)<2^w:=by omega
  obtain ⟨run,rom,data,frame,cheap,_⟩:=I.pair J mem (Or.inl le_rfl) ia ib
  have table:=Cutoff.mounted L.stop levels total K scale bound (fun _=>0 : Memory w)
  refine ⟨?_,rom,⟨?_,?_⟩,?_,cheap⟩
  · have len:I.length+J.length=Cutoff.finish L.stop levels total-L.origin:=by
      change L.stop-L.origin+(Cutoff.finish L.stop levels total-L.stop)=_;omega
    rw [←len]
    exact @run
  · intro i hi
    exact (data _ (Nat.le_add_right ..) (by
      exact (Nat.add_lt_add_left hi L.stop).trans_le (Nat.le_add_right ..))).trans (table.1 i hi)
  · intro i hi z hz
    have l:=Nat.mul_le_mul_right (2^total) hi
    rw [Nat.succ_mul,←pow_add] at l
    have slot : 2^total*i+z < 2^(levels+total) := by
      rw [Nat.mul_comm (2^total) i]
      exact (Nat.add_lt_add_left hz _).trans_le l
    exact (data (L.stop+2^levels+(2^total*i+z))
      ((Nat.le_add_right L.stop _).trans (Nat.le_add_right ..))
      (Nat.add_lt_add_left slot _)).trans (table.2 i hi z hz)
  · intro x ok
    exact frame x (by change x<L.origin∨L.stop≤x;omega) (by change x<L.stop∨Cutoff.finish L.stop levels total≤x;omega)

end AddressBook
end
end Hierarchy.DescentPlainTerminal.Suffix.PortLevels

end OAI
