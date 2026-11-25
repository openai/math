import OAI.Hierarchy.DescentPackedOverlap
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # Literal address and fragment pages for an arbitrary packed width change -/
namespace Hierarchy.DescentSIMDLookup.Overlap
open ProtocolRAM DescentOrdinaryAtomFieldRAM.ROM DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {a H G A B w : ℕ}
def rows (H G B : ℕ) := H*chunks G B
def mapBits (H G B : ℕ) := Nat.clog 2 (rows H G B+1)
def keyBits (a A : ℕ) := Nat.clog 2 (A+1)+a*A
def stride (a A : ℕ) := 2^(a*A)

def pointer (p : Row H G B) (j : ℕ) := (source (A:=A) p j).elim (rows H G A) (fun q=>(row H G A q).val)
def directory (H G A B a : ℕ) (j : Fin (pieces G A B+1)) : Page :=
  ⟨mapBits H G B,fun z=>if h : z.val<rows H G B then
    let p:=(row H G B).symm ⟨_,h⟩
    if j.val<pieces G A B then pointer (A:=A) p j.val else phase p.2.val B A*stride a A
    else 0⟩
def dictionary (G A B a : ℕ) (j : Fin (pieces G A B)) : Page :=
  ⟨keyBits a A,fun val=>(portion a A B (val.val/stride a A) j.val
    ⟨val.val%stride a A,Nat.mod_lt _ (Nat.two_pow_pos _)⟩).val⟩
def dictBase (base H G A B : ℕ) := base+(pieces G A B+1)*2^mapBits H G B
def dest (base H G A B a : ℕ) := dictBase base H G A B+pieces G A B*2^keyBits a A
def finish (base H G A B a : ℕ) := dest base H G A B a+rows H G B
def endAddress (base H G A B a : ℕ) := dest base H G A B a+2^mapBits H G B
def outputBank (base H G A B a : ℕ) : Bank := ⟨dest base H G A B a,mapBits H G B⟩

theorem output_fits (base H G A B a w : ℕ) (space : endAddress base H G A B a<2^w) :
    (outputBank base H G A B a).Fits w (endAddress base H G A B a) ∧
    rows H G B≤(outputBank base H G A B a).size ∧ finish base H G A B a≤endAddress base H G A B a := by
  have cover : rows H G B≤2^mapBits H G B:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  refine ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt space,le_rfl⟩,cover,Nat.add_le_add_left cover _⟩

def ptrBank (base H G A B a : ℕ) (j : Fin (pieces G A B+1)) :=
  bank (directory H G A B a) (mapBits H G B) base j
def lutBank (base H G A B a : ℕ) (j : Fin (pieces G A B)) :=
  bank (dictionary G A B a) (keyBits a A) (dictBase base H G A B) j

def tables (base H G A B a w : ℕ) :=
  (mount (directory H G A B a) (mapBits H G B) w base).seq
    (mount (dictionary G A B a) (keyBits a A) w (dictBase base H G A B))
def seeded (base H G A B a : ℕ) (m : Memory w) :=
  after (dictionary G A B a) (keyBits a A) (dictBase base H G A B)
    (after (directory H G A B a) (mapBits H G B) base m)

theorem resident (base : ℕ) (m : Memory w)
    (space : finish base H G A B a<2^w) :
    let out:=dest base H G A B a
    let seed:=seeded base H G A B a m
    (tables base H G A B a w).Exec m seed (8+10*(out-base)) ∧
    (∀i,(ptrBank base H G A B a i).Fits w out) ∧ (∀j,(lutBank base H G A B a j).Fits w out) ∧
    (∀j (p : Row H G B), seed ((ptrBank base H G A B a j).base+(row H G B p).val)=
      ((if j.val<pieces G A B then pointer (A:=A) p j.val else phase p.2.val B A*stride a A:ℕ):Word w)) ∧
    (∀j (sh : Fin A) (z : Cell (a*A)),seed ((lutBank base H G A B a j).base+(sh.val*stride a A+z.val))=
       ((portion a A B sh.val j.val z).val:Word w)) ∧
    (∀x,x<base ∨ out≤x→seed x=m x) := by
  intro out seed
  let addr:=dictBase base H G A B
  let pre:=after (directory H G A B a) (mapBits H G B) base m
  have ext : out<2^w:=(Nat.le_add_right ..).trans_lt space
  have ord : addr≤out:=Nat.le_add_right ..
  have extent : base≤addr:=Nat.le_add_right ..
  have hi : base+(pieces G A B+1)*2^mapBits H G B≤out:=ord
  have lo : addr+pieces G A B*2^keyBits a A≤out:=le_rfl
  have pf:=fun j=>bank_room (directory H G A B a) (mapBits H G B) base addr j le_rfl (le_refl addr) (ord.trans_lt ext)
  have qt:=fun j=>bank_room (dictionary G A B a) (keyBits a A) addr out j le_rfl lo ext
  refine ⟨?_,fun j=>⟨(pf j).1,(pf j).2.1,(pf j).2.2.trans ord⟩,qt,?_,?_,?_⟩
  · have r₀:=run (directory H G A B a) _ base m (ord.trans_lt ext)
    have r₁:=run (dictionary G A B a) _ addr pre ext
    have sum : 8+10*(out-base)=(4+10*((pieces G A B+1)*2^mapBits H G B))+
        (4+10*(pieces G A B*2^keyBits a A)) :=by dsimp [out,dest,dictBase];omega
    rw [sum];intro P R K machine
    exact Procedure.Exec.then r₀.1 r₁.1 machine
  · intro j p
    let t:=row H G B p
    have bound : t.val<2^mapBits H G B :=t.isLt.trans_le ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _))
    have early : (ptrBank base H G A B a j).base+t.val<addr :=
      (Nat.add_lt_add_left bound _).trans_le (pf j).2.2
    have previous:=frame (dictionary G A B a) (keyBits a A) addr pre _ (Or.inl early)
    change after (dictionary G A B a) (keyBits a A) addr pre ((ptrBank base H G A B a j).base+t.val)=_
    rw [previous]
    have actual:=read (directory H G A B a) _ base m j le_rfl ⟨t.val,bound⟩
    have present : t.val<rows H G B:=t.isLt
    have back : (row H G B).symm (⟨t.val,present⟩ : Fin (H*chunks G B))=p:= (row H G B).symm_apply_apply p
    change (after (directory H G A B a) (mapBits H G B) base m)
      ((bank (directory H G A B a) (mapBits H G B) base j).base+t.val)=_
    simpa only [directory,dite_eq_left present,back] using actual
  · intro j sh z
    have lim : A≤2^Nat.clog 2 (A+1) :=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
    have zbound : z.val<stride a A:=z.isLt
    have kt : sh.val*stride a A+z.val<2^keyBits a A:=by
      rw [keyBits,pow_add]; exact (Nat.add_lt_add_left zbound _).trans_le (by
        rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right _ (sh.isLt.trans_le lim))
    have actual:=read (dictionary G A B a) _ addr pre j le_rfl ⟨_,kt⟩
    have div : (sh.val*stride a A+z.val)/stride a A=sh.val:=by
      have str : 0<stride a A:=Nat.two_pow_pos _
      rw [Nat.mul_comm sh.val,Nat.mul_add_div str,Nat.div_eq_of_lt zbound,Nat.add_zero]
    have rem_ : (sh.val*stride a A+z.val)%stride a A=z.val:=by simp [Nat.add_mod,Nat.mod_eq_of_lt zbound]
    change after (dictionary G A B a) (keyBits a A) addr pre ((bank (dictionary G A B a) (keyBits a A) addr j).base+_)=_
    simpa only [dictionary,div,rem_,Fin.eta] using actual
  · intro x hx
    have after₂:=frame (dictionary G A B a) (keyBits a A) addr pre x (by rcases hx with h|h;exact Or.inl (h.trans_le extent);exact Or.inr h)
    have after₁:=frame (directory H G A B a) (mapBits H G B) base m x (by rcases hx with h|h;exact Or.inl h;exact Or.inr (ord.trans h))
    exact after₂.trans after₁

end
end Hierarchy.DescentSIMDLookup.Overlap

end OAI
