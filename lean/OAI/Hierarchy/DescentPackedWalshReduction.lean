import OAI.Hierarchy.DescentPackedWalshRAM

namespace OAI
/-! # Merging two sites at a larger digit precision with independent lane subdivision -/
namespace Hierarchy.DescentPackedWalshReduction
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {H K Z L b c w : ℕ}

/-- Z subdivisions of L entries occupy one predecessor word. -/
abbrev Data (H K Z L b : ℕ) := Fin H→Bool→Fin K→Fin Z→Fin L→Cell b

def part (x : Fin Z→Fin L→Cell b) : Cell (b*(Z*L)) :=
  encode b (Z*L) (fun i=>let p:=finProdFinEquiv.symm i;x p.1 p.2)

def merged (x : Data H K Z L b) (h : Fin H) (i : Fin K) (z : Fin Z) (j : Fin L) : Cell c :=
  ((x h false i z j).val+(x h true i z j).val:ℕ)

def leftRow (h : Fin H) (s : Bool) (i : Fin K) : Fin ((H*2)*K) :=
  finProdFinEquiv (finProdFinEquiv (h,finTwoEquiv.symm s),i)

def rightRow (h : Fin H) (i : Fin K) (z : Fin Z) : Fin ((H*K)*Z) :=
  finProdFinEquiv (finProdFinEquiv (h,i),z)

def key (idx : ℕ) (z : Cell idx) (x y : Cell (b*(Z*L))) : Cell (idx+(b+b)*(Z*L)) :=
  ((finProdFinEquiv.trans (finCongr (by rw [pow_add]))) : Cell idx × Cell ((b+b)*(Z*L)) ≃ Cell (idx+(b+b)*(Z*L)))
    (z,DescentPackedZip.key b b (Z*L) (x,y))

theorem key_val (idx : ℕ) (z : Cell idx) (x y : Cell (b*(Z*L))) :
    (key idx z x y).val=2^((b+b)*(Z*L))*z.val+(y.val+2^(b*(Z*L))*x.val) := by
  change (DescentPackedZip.key b b (Z*L) (x,y)).val+2^((b+b)*(Z*L))*z.val=_
  rw [DescentPackedZip.key_val,Nat.add_comm]

def lut {idx : ℕ} (i : Cell (idx+(b+b)*(Z*L))) : Cell (c*L) :=
  let pair:=(((finProdFinEquiv.trans (finCongr (by rw [pow_add]))) : Cell idx × Cell ((b+b)*(Z*L)) ≃ Cell (idx+(b+b)*(Z*L)))).symm i
  let words:=(DescentPackedZip.key b b (Z*L)).symm pair.2
  if live : pair.1.val<Z then encode c L (fun j=>
    let k:=finProdFinEquiv (⟨pair.1.val,live⟩,j)
    ((((encode b (Z*L)).symm words.1 k).val+((encode b (Z*L)).symm words.2 k).val:ℕ):Cell c))
  else 0

theorem pair {idx : ℕ} (x : Data H K Z L b) (v : Fin H) (i : Fin K) (z : Fin Z) (room : Z≤2^idx) :
    lut (c:=c) (key idx (⟨z.val,z.isLt.trans_le room⟩)
      (part (x v false i)) (part (x v true i)))=encode c L (merged x v i z) := by
  simp only [lut,key,Equiv.symm_apply_apply,z.isLt,dite_eq_left,part]
  apply congrArg (encode c L)
  funext j
  simp [merged]

def oldWords (B : ℕ) (x : Data H K Z L b) (m : Memory w) : Prop :=
  ∀v side i,m (B+(leftRow v side i).val)=((part (x v side i)).val:Word w)

structure Header (B : DescentPackedWalsh.Banks) (H K Z L b c idx : ℕ) (m : Memory w) : Prop where
  lo : ∀v i z,m (B.lo.base+(rightRow (H:=H) (K:=K) (Z:=Z) v i z).val)=((leftRow v false i).val:Word w)
  hi : ∀v i z,m (B.hi.base+(rightRow (H:=H) (K:=K) (Z:=Z) v i z).val)=((leftRow v true i).val:Word w)
  tag : ∀v i z,m (B.sign.base+(rightRow (H:=H) (K:=K) (Z:=Z) v i z).val)=((2^((b+b)*(Z*L))*z.val:ℕ):Word w)
  shift : ∀x : Cell (b*(Z*L)),m (B.shift.base+x.val)=((2^(b*(Z*L))*x.val:ℕ):Word w)
  table : ∀i : Cell (idx+(b+b)*(Z*L)),m (B.table.base+i.val)=((lut (c:=c) i).val:Word w)

structure Room (B : DescentPackedWalsh.Banks) (out H K Z L b idx w : ℕ) : Prop where
  old : B.old.Fits w out
  lo : B.lo.Fits w out
  hi : B.hi.Fits w out
  tag : B.sign.Fits w out
  shift : B.shift.Fits w out
  table : B.table.Fits w out
  source : H*2*K≤B.old.size
  loRows : H*K*Z≤B.lo.size
  hiRows : H*K*Z≤B.hi.size
  tagRows : H*K*Z≤B.sign.size
  shiftRows : 2^(b*(Z*L))≤B.shift.size
  tableRows : 2^(idx+(b+b)*(Z*L))≤B.table.size
  split : Z≤2^idx
  finish : out+H*K*Z<2^w

set_option maxHeartbeats 800000 in
private theorem read_row {idx : ℕ} (B : DescentPackedWalsh.Banks) (out : ℕ)
    (x : Data H K Z L b) (m : Memory w) (room : Room B out H K Z L b idx w)
    (header : Header B H K Z L b c idx m) (stored : oldWords B.old.base x m)
    (v : Fin H) (i : Fin K) (z : Fin Z) :
    B.read.eval m ((rightRow v i z).val:Word w)=((encode c L (merged x v i z)).val:Word w) := by
  let q:=rightRow v i z
  let xlo:=part (x v false i)
  let xhi:=part (x v true i)
  let code:=key idx ⟨z.val,z.isLt.trans_le room.split⟩ xlo xhi
  change B.table.read m (B.sign.read m (q.val:Word w)+(B.old.read m (B.hi.read m (q.val:Word w))+
    B.shift.read m (B.old.read m (B.lo.read m (q.val:Word w)))))=_
  rw [DescentPackedZip.bank_read B.sign m (q.isLt.trans_le room.tagRows) room.tag,header.tag,
    DescentPackedZip.bank_read B.hi m (q.isLt.trans_le room.hiRows) room.hi,header.hi,
    DescentPackedZip.bank_read B.lo m (q.isLt.trans_le room.loRows) room.lo,header.lo,
    DescentPackedZip.bank_read B.old m ((leftRow v false i).isLt.trans_le room.source) room.old,stored,
    DescentPackedZip.bank_read B.old m ((leftRow v true i).isLt.trans_le room.source) room.old,stored,
    DescentPackedZip.bank_read B.shift m (xlo.isLt.trans_le room.shiftRows) room.shift,header.shift,
    ←Nat.cast_add,←Nat.cast_add]
  have equalKey:=key_val idx (⟨z.val,z.isLt.trans_le room.split⟩ : Cell idx) xlo xhi
  change B.table.read m ((2^((b+b)*(Z*L))*z.val+(xhi.val+2^(b*(Z*L))*xlo.val):ℕ):Word w)=_
  rw [←equalKey]
  rw [DescentPackedZip.bank_read B.table m (code.isLt.trans_le room.tableRows) room.table,header.table]
  exact congrArg (fun z : Cell (c*L)=>(z.val:Word w)) (pair x v i z room.split)


theorem run {idx : ℕ} (B : DescentPackedWalsh.Banks) (out : ℕ) (x : Data H K Z L b) (m : Memory w)
    (room : Room B out H K Z L b idx w) (header : Header B H K Z L b c idx m) (stored : oldWords B.old.base x m) :
    let dst:=image out (H*K*Z) B.read m
    (scan w out (H*K*Z) B.read).Exec m dst (4+90*(H*K*Z)) ∧
      (∀v i z,dst (out+(rightRow v i z).val)=((encode c L (merged x v i z)).val:Word w)) ∧
      (∀a<out,dst a=m a) ∧ ∀a,out+H*K*Z≤a→dst a=m a := by
  have legal : B.read.Fits w out:=⟨room.table,⟨room.tag,trivial⟩,⟨room.old,room.hi,trivial⟩,room.shift,room.old,room.lo,trivial⟩
  have price : 2*B.read.work+4=90:=rfl
  refine ⟨?_,?_,fun a ha=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ha),
    fun a ha=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr ha)⟩
  · rw [show 4+90*(H*K*Z)=4+(H*K*Z)*(2*B.read.work+4) by rw [price,Nat.mul_comm 90]]
    intro P R publicCount machine
    exact scan_exec out (H*K*Z) B.read m legal room.finish machine
  · intro v i z
    exact (ProtocolRAMGeneratedWrite.read_image out (H*K*Z) B.read m (rightRow v i z)).trans
      (read_row B out x m room header stored v i z)

end
end Hierarchy.DescentPackedWalshReduction

end OAI
