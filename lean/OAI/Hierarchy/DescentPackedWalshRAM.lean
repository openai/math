import OAI.Hierarchy.DescentPackedWalshRow
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # One fixed word-RAM pass for a complete Walsh layer at every old host -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {b w H u l : ℕ}

def row (v : Fin H) (x : Cube u) : Fin (H*2^u) := finProdFinEquiv (v,ordinal u x)

def unrow (i : Fin (H*2^u)) : Fin H × Cube u :=
  let p:=finProdFinEquiv.symm i
  (p.1,(ordinal u).symm p.2)

theorem unrow_row (v : Fin H) (x : Cube u) : unrow (row v x)=(v,x) := by simp [unrow,row]

/-- The pointer columns describe only the chosen public axis and the common host rectangle. -/
structure Banks where
  old : Bank
  lo : Bank
  hi : Bank
  sign : Bank
  shift : Bank
  table : Bank

def Banks.read (B : Banks) : Expr :=
  .lookup B.table (.op .add (.lookup B.sign .row) (.op .add
    (.lookup B.old (.lookup B.hi .row)) (.lookup B.shift (.lookup B.old (.lookup B.lo .row)))))

def layerProgram (B : Banks) (out H u w : ℕ) := scan w out (H*2^u) B.read

structure Room (B : Banks) (out H u l b w : ℕ) : Prop where
  old : B.old.Fits w out
  lo : B.lo.Fits w out
  hi : B.hi.Fits w out
  sign : B.sign.Fits w out
  shift : B.shift.Fits w out
  table : B.table.Fits w out
  sites : H*2^u≤B.old.size
  lows : H*2^u≤B.lo.size
  highs : H*2^u≤B.hi.size
  signs : H*2^u≤B.sign.size
  shifts : 2^(b*2^l)≤B.shift.size
  tables : 2^(1+(b+b)*2^l)≤B.table.size
  finish : out+H*2^u<2^w

structure Literal (B : Banks) (a : Axis u l) (H b : ℕ) (m : Memory w) : Prop where
  lo : ∀(v : Fin H) p,m (B.lo.base+(row v p).val)=((row v (above a p false)).val:Word w)
  hi : ∀(v : Fin H) p,m (B.hi.base+(row v p).val)=((row v (above a p true)).val:Word w)
  sign : ∀(v : Fin H) p,m (B.sign.base+(row v p).val)=((2^((b+b)*2^l)*(upperSign a p).toNat:ℕ):Word w)
  shift : ∀j : Cell (b*2^l),m (B.shift.base+j.val)=((2^(b*2^l)*j.val:ℕ):Word w)
  table : ∀j : Cell (1+(b+b)*2^l),m (B.table.base+j.val)=((dictionary (b:=b) a j).val:Word w)

def Installed (B : ℕ) (x : Fin H→Cube u→Cube l→Cell b) (m : Memory w) : Prop :=
  ∀v p,m (B+(row v p).val)=((chunk (x v p)).val:Word w)

theorem read_step (B : Banks) (a : Axis u l) (out : ℕ) (room : Room B out H u l b w)
    (m : Memory w) (fixed : Literal B a H b m) (x : Fin H→Cube u→Cube l→Cell b)
    (old : Installed B.old.base x m) (v : Fin H) (p : Cube u) :
    B.read.eval m ((row v p).val:Word w)=((chunk (step a (x v) p)).val:Word w) := by
  let q:=row v p
  let xlo:=chunk (x v (above a p false))
  let xhi:=chunk (x v (above a p true))
  let idx:=record b l (upperSign a p) xlo xhi
  change B.table.read m (B.sign.read m (q.val:Word w)+(B.old.read m (B.hi.read m (q.val:Word w))+
    B.shift.read m (B.old.read m (B.lo.read m (q.val:Word w)))))=_
  rw [DescentPackedZip.bank_read B.sign m (q.isLt.trans_le room.signs) room.sign,fixed.sign,
    DescentPackedZip.bank_read B.hi m (q.isLt.trans_le room.highs) room.hi,fixed.hi,
    DescentPackedZip.bank_read B.lo m (q.isLt.trans_le room.lows) room.lo,fixed.lo,
    DescentPackedZip.bank_read B.old m ((row v (above a p false)).isLt.trans_le room.sites) room.old,old,
    DescentPackedZip.bank_read B.old m ((row v (above a p true)).isLt.trans_le room.sites) room.old,old,
    DescentPackedZip.bank_read B.shift m (xlo.isLt.trans_le room.shifts) room.shift,fixed.shift,
    ←Nat.cast_add,←Nat.cast_add]
  change B.table.read m ((2^((b+b)*2^l)*(upperSign a p).toNat+(xhi.val+2^(b*2^l)*xlo.val):ℕ):Word w)=_
  rw [←record_val,DescentPackedZip.bank_read B.table m (idx.isLt.trans_le room.tables) room.table,fixed.table,
    record_read]
  exact congrArg (fun z : Cell (b*2^l)=>(z.val:Word w)) (row_correct a (x v) p)

theorem layer (B : Banks) (a : Axis u l) (out : ℕ) (room : Room B out H u l b w)
    (m : Memory w) (fixed : Literal B a H b m) (x : Fin H→Cube u→Cube l→Cell b)
    (old : Installed B.old.base x m) :
    let dst:=image out (H*2^u) B.read m
    (layerProgram B out H u w).Exec m dst (4+90*(H*2^u)) ∧
      Installed out (fun v=>step a (x v)) dst ∧
      (∀z<out,dst z=m z) ∧ ∀z,out+H*2^u≤z→dst z=m z := by
  have safe : B.read.Fits w out:=⟨room.table,⟨room.sign,trivial⟩,⟨room.old,room.hi,trivial⟩,room.shift,room.old,room.lo,trivial⟩
  refine ⟨?_,?_,fun z hz=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl hz),
    fun z hz=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr hz)⟩
  · have price : 2*B.read.work+4=90:=rfl
    rw [show 4+90*(H*2^u)=4+(H*2^u)*(2*B.read.work+4) by rw [price,Nat.mul_comm 90]]
    intro P R K machine
    exact scan_exec out (H*2^u) B.read m safe room.finish machine
  · intro v p
    exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans (read_step B a out room m fixed x old v p)

theorem layer_cheap (B : Banks) (out H u w : ℕ) : CheapCode (layerProgram B out H u w) := by
  exact scan_cheap w out (H*2^u) B.read

end
end Hierarchy.DescentPackedWalsh

end OAI
