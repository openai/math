import OAI.Hierarchy.DescentExteriorMatrixDateCore
import OAI.Hierarchy.DescentExteriorSpineMatrix
import OAI.Hierarchy.DescentResetDigits
import OAI.Hierarchy.DescentDatedImage
import OAI.Hierarchy.DescentGLConditional

namespace OAI
/-! # The two public changes of coordinates and their native product tables -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentColonies DescentGL DescentExterior
noncomputable section

def ordinaryCut {m r : ℕ} (k:ℕ) (fit:m=r+k) (turn:Layout k) :
    Bits (m+k) ≃ₗ[ZMod 2] (Bits (r+k)×Bits k) :=
  (splitRows m k).trans ((castBits fit).prodCongr turn)

def resetCut {m r : ℕ} (k:ℕ) (fit:m=r+k) (turn:Layout (m+k)) :
    Bits (m+k) ≃ₗ[ZMod 2] (Bits (r+k)×Bits k) :=
  (turn.trans (splitRows m k)).trans ((castBits fit).prodCongr (LinearEquiv.refl _ (Bits k)))

end
end Hierarchy.DescentSixParty.Chronology

/-! # The public matrix-product data for an ordinary date or a reset date -/
namespace Hierarchy.DescentExteriorMatrixUpdate
open DescentGL DescentExterior DescentCompiler DescentSixParty.Chronology DescentColonies
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentPackedColony.Phase.Arena
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {h d w : ℕ}

def pages (d h : ℕ) := 2^(d*d)+2^(d*d)*2^(h*h)

def tableSheet (base : ℕ) (ext : Layout h→Layout d) : Image w :=
  ⟨base,base+pages d h,fun a=>if mem : a-base < pages d h then rom ext ⟨a-base,mem⟩ else 0⟩

theorem table_words (base : ℕ) (ext : Layout h→Layout d) (m : Memory w)
    (read : (tableSheet base ext).Resident m) (i : Fin (pages d h)) :
    m (base+i.val)=rom ext i := by
  obtain ⟨j,hj⟩:=i
  have delta : base+j-base=j:=by omega
  have got:=read (base+j) (show base≤base+j by omega)
    (show base+j<base+pages d h by omega)
  simp only [tableSheet,delta,dite_eq_left hj] at got
  exact got

def cell (old rot publicBase out : ℕ) (d h : ℕ) : Cell :=
  ⟨⟨old,0⟩,⟨rot,0⟩,offsetBank publicBase d,tableBank publicBase d h,out⟩

theorem shelf_of_rotate (old rot base out : ℕ) (ext : Layout h→Layout d) (L : Layout h) (m : Memory w)
    (saved : m rot=((matrixCode L).val:Word w)) (printed : (tableSheet base ext).Resident m) :
    (cell old rot base out d h).Shelf m ext L := by
  refine ⟨saved,fun x=>(table_words base ext m printed (finSumFinEquiv (.inl x))).trans (rom_offset ext x),?_⟩
  intro x y
  have val:=(table_words base ext m printed (finSumFinEquiv (.inr (finProdFinEquiv (x,y))))).trans (rom_entry ext x y)
  change m (base+(2^(d*d)+(y.val+2^(h*h)*x.val)))=_ at val
  change m (base+2^(d*d)+(x.val*2^(h*h)+y.val))=_
  rw [show base+2^(d*d)+(x.val*2^(h*h)+y.val)=base+(2^(d*d)+(y.val+2^(h*h)*x.val)) by ring]
  exact val

theorem cell_room (old rot base out d h w : ℕ) (low : old < out) (entered : rot < out)
    (before : base+pages d h ≤ out) (size : out+1 < 2^w) :
    (cell old rot base out d h).Room w d h := by
  let A:=2^(d*d)
  let B:=2^(h*h)
  have ha : 0 < A:=Nat.two_pow_pos _
  have hb : 0 < B:=Nat.two_pow_pos _
  have hab : 0 < A*B:=Nat.mul_pos ha hb
  have both : base+A+A*B ≤ out:=by change base+(A+A*B) ≤ out at before;omega
  have bits : (tableBank base d h).size=A*B:=by change 2^(d*d+h*h)=_;rw [pow_add]
  refine ⟨⟨by change 0<1;decide,by change 1 < 2^w;omega,by change old+1 ≤ out;omega⟩,
    ⟨by change 0<1;decide,by change 1 < 2^w;omega,by change rot+1 ≤ out;omega⟩,
    ⟨ha,by change A < 2^w;omega,by change base+A ≤ out;omega⟩,
    ⟨bits.symm ▸ hab,by change (tableBank base d h).size<2^w;rw [bits];omega,by change base+A+(tableBank base d h).size ≤ out;rw [bits];exact both⟩,
    le_rfl,bits.ge,size⟩

variable (S : AtomSchedule) (k tail i : ℕ)
private theorem split_width (alive : i ≤ S.length) :
    (S.groupWidth k tail i+k)+(k*i)=S.groupWidth k tail 0+k := by
  have sum : S.length-i+i=S.length:=Nat.sub_add_cancel alive
  have blocks:=congrArg (fun n=>k*n) sum
  rw [Nat.mul_add] at blocks
  simp only [AtomSchedule.groupWidth,Nat.sub_zero]
  omega

private theorem next_width (alive : i < S.length) :
    (S.groupWidth k tail (i+1)+k)+(k+k*i)=S.groupWidth k tail 0+k := by
  have h:=split_width S k tail (i+1) (by omega)
  rw [Nat.mul_succ] at h
  omega

def ordinaryMap (alive : i < S.length) : Layout k→Layout (S.groupWidth k tail 0+k) :=
  Spine.promoteCut (split_width S k tail i alive.le) (next_width S k tail i alive) (ordinaryCut k (S.group_cut alive))

def resetMap (alive : i < S.length) : Layout (S.groupWidth k tail i+k)→Layout (S.groupWidth k tail 0+k) :=
  Spine.promoteCut (split_width S k tail i alive.le) (next_width S k tail i alive) (resetCut k (S.group_cut alive))

theorem ordinaryMap_eq (alive : i < S.length) {f : ℕ} (eq : f=k*i)
    (prior : (S.groupWidth k tail i+k)+f=S.groupWidth k tail 0+k)
    (following : (S.groupWidth k tail (i+1)+k)+(k+f)=S.groupWidth k tail 0+k) :
    Spine.promoteCut prior following (ordinaryCut k (S.group_cut alive))=ordinaryMap S k tail i alive := by
  subst f;rfl

theorem resetMap_eq (alive : i < S.length) {f : ℕ} (eq : f=k*i)
    (prior : (S.groupWidth k tail i+k)+f=S.groupWidth k tail 0+k)
    (following : (S.groupWidth k tail (i+1)+k)+(k+f)=S.groupWidth k tail 0+k) :
    Spine.promoteCut prior following (resetCut k (S.group_cut alive))=resetMap S k tail i alive := by
  subst f;rfl

end
end Hierarchy.DescentExteriorMatrixUpdate

end OAI
