import OAI.Hierarchy.DescentPackedWalshLiteral
import OAI.Hierarchy.DescentPackedWalshCube

namespace OAI
/-! # The fixed chronological sequence of packed butterfly layers for a full Walsh transform -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H u l b w : ℕ}

def axesList (u l : ℕ) := (List.finRange (u+l)).reverse

def location (first H u s : ℕ) := first+s*page H u

def code (w root first H u l b : ℕ) : ℕ→List (Fin (u+l))→Procedure w
  | _,[]=>scan w first 0 .row
  | z,_::rest=>(layerProgram (shelf root first z H u l b) (outPage first H u z) H u w).seq
      (code w root first H u l b (z+1) rest)

def after (root first H u l b : ℕ) : ℕ→List (Fin (u+l))→Memory w→Memory w
  | _,[],m=>m
  | z,_::rest,m=>after root first H u l b (z+1) rest
      (image (outPage first H u z) (H*2^u) (shelf root first z H u l b).read m)

def duration (H u q : ℕ) := q*(4+90*(H*2^u))+4

private theorem idle (first : ℕ) (mem : Memory w) (small : first<2^w) : (scan w first 0 .row).Exec mem mem 4 := by
  have eqn : image first 0 .row mem=mem := by
    funext i
    exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)
  have run : (scan w first 0 .row).Exec mem (image first 0 .row mem) (4+0*(2*Expr.row.work+4)) :=
    @scan_exec w first 0 .row mem trivial (by omega)
  rw [eqn] at run
  intro pc reg ports machine
  exact run machine

theorem runFrom (root first z : ℕ) (seq : List (Fin (u+l))) (header : List (Axis u l)) (mem src : Memory w)
    (x : Fin H→Cube (u+l)→Cell b)
    (agree : ∀i : Fin seq.length,header[z+i.val]?=some (axis seq[i.val]))
    (space : root+header.length*span H u l b≤first)
    (roomLast : first+(z+seq.length+1)*page H u<2^w)
    (saved : ∀v<first,mem v=mounted H b root header src v)
    (old : Installed (location first H u z) (fun v=>shaped (x v)) mem) :
    let dst:=after root first H u l b z seq mem
    (code w root first H u l b z seq).Exec mem dst (duration H u seq.length) ∧
    Installed (location first H u (z+seq.length)) (fun v=>shaped (DescentWalshPhysical.steps seq (x v))) dst ∧
      (∀v<first,dst v=mem v) ∧ ∀v,first+(z+seq.length+1)*page H u≤v→dst v=mem v := by
  induction seq generalizing z mem x with
  | nil=>
    have pos : first<2^w:=by omega
    simp only [code,after,duration,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.add_zero,
      DescentWalshPhysical.steps,List.foldl_nil]
    exact ⟨@idle w first mem pos,old,fun _ _=>trivial,fun _ _=>trivial⟩
  | cons a seq ih=>
    have good:=agree 0
    change header[z+0]?=some (axis a) at good
    simp only [Nat.add_zero] at good
    have live : z<header.length:=by by_contra! hz; rw [List.getElem?_eq_none (by omega)] at good;contradiction
    have real : header[z]=axis a:=by simpa [live] using good
    have endRoom : first+(z+2)*page H u<2^w := (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by simp only [List.length_cons];omega : z+2≤z+(a::seq).length+1)) _).trans_lt roomLast
    have fits:=room root first z H u l b ((Nat.add_le_add_left (Nat.mul_le_mul_right _ live) _).trans space) endRoom
    have pin:=header_after header ⟨z,live⟩ src mem saved space
    rw [real] at pin
    obtain ⟨run,read,low,high⟩:=layer _ (axis a) _ fits mem pin (fun v=>shaped (x v)) old
    let mid:=image (outPage first H u z) (H*2^u) (shelf root first z H u l b).read mem
    have new : Installed (location first H u (z+1)) (fun v=>shaped (DescentWalshPhysical.layer a (x v))) mid := by
      simpa only [step_shaped,mid,location,outPage] using read
    have tail (i : Fin seq.length) : header[z+1+i.val]?=some (axis seq[i.val]) := by
      have e : z+1+i.val=z+(i.val+1):=by omega
      rw [e]
      simpa only [Fin.val_succ,List.getElem_cons_succ] using agree i.succ
    have keep (v : ℕ) (before : v<first) := (low v (before.trans_le (Nat.le_add_right _ _))).trans (saved v before)
    obtain ⟨next,nextRead,nextLo,nextHi⟩:=ih (z+1) mid (fun v=>DescentWalshPhysical.layer a (x v)) tail
      (by
        have eq : z+1+seq.length+1=z+(a::seq).length+1:=by simp only [List.length_cons];omega
        rwa [eq]) keep new
    refine ⟨?_,?_,fun v hv=>(nextLo v hv).trans (low v (hv.trans_le (Nat.le_add_right _ _))),?_⟩
    · have ticks : duration H u ((a::seq).length) = (4+90*(H*2^u))+duration H u seq.length := by
        simp only [duration,List.length_cons,Nat.succ_mul]
        omega
      rw [ticks]
      intro pc reg ports machine
      exact Procedure.Exec.then run next machine
    · have off : z+(a::seq).length=z+1+seq.length := by simp only [List.length_cons];omega
      rw [off]
      exact nextRead
    · intro v hv
      have small := rows_le H u
      have highBound : outPage first H u z+H*2^u≤first+(z+seq.length+2)*page H u := by
        have ho : z+2≤z+seq.length+2:=by omega
        have h:=Nat.mul_le_mul_right (page H u) ho
        rw [Nat.succ_mul (z+1)] at h
        unfold outPage;omega
      have pos : z+(a::seq).length+1=z+seq.length+2:=by simp only [List.length_cons];omega
      have stop : first+(z+seq.length+2)*page H u≤v:=pos ▸ hv
      have byTime : z+1+seq.length+1=z+seq.length+2:=by omega
      exact (nextHi v (by rwa [byTime])).trans (high v (highBound.trans stop))

theorem full (root first : ℕ) (mem src : Memory w) (x : Fin H→Cube (u+l)→Cell b)
    (header : root+(u+l)*span H u l b≤first) (lim : first+(u+l+1)*page H u<2^w)
    (pins : ∀v<first,mem v=mounted H b root ((axesList u l).map axis) src v)
    (read : Installed first (fun v=>shaped (x v)) mem) :
    let seq:=axesList u l;let dst:=after root first H u l b 0 seq mem
    (code w root first H u l b 0 seq).Exec mem dst (duration H u (u+l)) ∧
      Installed (location first H u (u+l)) (fun v=>shaped (DescentWalshPhysical.transform (x v))) dst ∧
      (∀z<first,dst z=mem z) ∧ ∀z,first+(u+l+1)*page H u≤z→dst z=mem z := by
  simpa [axesList,DescentWalshPhysical.transform,location] using
    runFrom root first 0 (axesList u l) ((axesList u l).map axis) mem src x (by intro i;simp [i.isLt])
      (by simpa [axesList] using header) (by simpa [axesList] using lim) pins (by simpa [location] using read)

end
end Hierarchy.DescentPackedWalsh

end OAI
