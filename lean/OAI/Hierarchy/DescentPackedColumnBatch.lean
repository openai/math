import OAI.Hierarchy.DescentSIMDLookup
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Physical order, framing and tariff of all packed directed socket columns -/
namespace Hierarchy.DescentPackedFlowBatch
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}

def passes (base rows pitch : ℕ) (e : ℕ→Expr) (start : ℕ) : ℕ→List Pass
  | 0=>[]
  | n+1=>⟨base+start*pitch,rows,e start⟩::passes base rows pitch e (start+1) n

theorem interval (base rows pitch : ℕ) (e : ℕ→Expr) (start n : ℕ) (p : Pass)
    (member : p∈passes base rows pitch e start n) :
    ∃j,start≤j ∧ j<start+n ∧ p=⟨base+j*pitch,rows,e j⟩ := by
  induction n generalizing start with
  | zero=>simp [passes] at member
  | succ n ih=>
    rcases List.mem_cons.mp member with rfl|tail
    · exact ⟨start,le_rfl,by omega,rfl⟩
    · obtain ⟨j,h,k,eq⟩:=ih (start+1) tail;exact ⟨j,by omega,by omega,eq⟩

theorem read_all (base rows pitch start n : ℕ) (e : ℕ→Expr) (m src : Memory w)
    (parts : rows≤pitch) (old : ∀a<base,m a=src a)
    (fits : ∀j,start≤j→j<start+n→(e j).Fits w base) :
    ∀s : Fin n,∀i : Fin rows,
      result (passes base rows pitch e start n) m (base+(start+s.val)*pitch+i.val)=(e (start+s.val)).eval src (i.val:Word w) := by
  induction n generalizing start m with
  | zero=>intro s;exact Fin.elim0 s
  | succ n ih=>
    let first : Pass:=⟨base+start*pitch,rows,e start⟩
    let mid:=first.apply m
    have frame (a : ℕ) (ha : a<base) : mid a=src a :=
      (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega : a<base+start*pitch ∨ base+start*pitch+rows≤a)).trans (old a ha)
    intro s i
    refine Fin.cases ?_ (fun j=>?_) s
    · change result (passes base rows pitch e (start+1) n) mid (base+(start+0)*pitch+i.val)=_
      rw [Nat.add_zero]
      rw [result_below _ _ _ (by
        intro p hp
        obtain ⟨j,lower,_,rfl⟩:=interval _ _ _ _ _ _ _ hp
        have gap:=Nat.mul_le_mul_right pitch lower
        rw [Nat.succ_mul] at gap
        change base+start*pitch+i.val<base+j*pitch
        have hi:=i.isLt;omega)]
      exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ i).trans (eval_below _ _ src m (fits _ le_rfl (by omega)) old)
    · have read:=ih (start+1) mid frame (fun j lo hi=>fits j (by omega) (by omega)) j i
      change result (passes base rows pitch e (start+1) n) mid (base+(start+j.succ.val)*pitch+i.val)=
        (e (start+j.succ.val)).eval src (i.val:Word w)
      simpa only [Fin.val_succ,Nat.add_right_comm start 1 j.val,Nat.add_assoc] using read

theorem execute (base rows pitch n : ℕ) (e : ℕ→Expr) (m : Memory w) (fits : ∀j<n,(e j).Fits w base)
    (endAt : base+n*pitch<2^w) (parts : rows≤pitch) :
    (program w (passes base rows pitch e 0 n)).Exec m (result (passes base rows pitch e 0 n) m) (clock (passes base rows pitch e 0 n)) ∧
    (∀j : Fin n,∀i : Fin rows,result (passes base rows pitch e 0 n) m (base+j.val*pitch+i.val)=(e j.val).eval m (i.val:Word w)) ∧
    ∀a<base,result (passes base rows pitch e 0 n) m a=m a := by
  refine ⟨program_exec _ _ ?_,?_,?_⟩
  · intro p hp
    obtain ⟨j,_,hit,rfl⟩:=interval _ _ _ _ _ _ _ hp
    simp only [Nat.zero_add] at hit
    refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right _ _) (fits j hit),?_⟩
    have next:=Nat.mul_le_mul_right pitch hit;rw [Nat.succ_mul] at next
    change base+j*pitch+rows<2^w
    omega
  · simpa only [Nat.zero_add] using read_all base rows pitch 0 n e m m parts (fun _ _=>rfl) (fun j _ h=>fits j (by omega))
  · intro a ha
    apply result_below
    intro p hp
    obtain ⟨j,_,_,rfl⟩:=interval _ _ _ _ _ _ _ hp
    exact ha.trans_le (Nat.le_add_right _ _)

theorem above (base rows pitch : ℕ) (e : ℕ→Expr) (m : Memory w) (start n a : ℕ)
    (sep : rows≤pitch) (finish : base+(start+n)*pitch≤a) :
    result (passes base rows pitch e start n) m a=m a := by
  induction n generalizing start m with
  | zero=>rfl
  | succ n ih=>
    let p : Pass:=⟨base+start*pitch,rows,e start⟩
    have tail : base+(start+1+n)*pitch≤a := by simpa only [show start+1+n=start+(n+1) by omega] using finish
    apply (ih (p.apply m) (start+1) tail).trans
    apply ProtocolRAMGeneratedWrite.frame_image
    right
    have later:=Nat.mul_le_mul_right pitch (show start+1 ≤ start+(n+1) by omega)
    rw [Nat.succ_mul] at later
    change base+start*pitch+rows≤a
    omega

theorem tariff (base rows pitch n : ℕ) (e : ℕ→Expr) (K : ℕ) (limit : ∀j<n,(e j).work≤K) :
    clock (passes base rows pitch e 0 n)≤4+n*(4+rows*(2*K+4)) := by
  have each (start z : ℕ) (sep : start+z≤n) :
      clock (passes base rows pitch e start z)≤4+z*(4+rows*(2*K+4)) := by
    induction z generalizing start with
    | zero=>simp [passes,clock]
    | succ z ih=>
      have later:=ih (start+1) (by omega)
      have this:=Nat.mul_le_mul_left rows (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (limit start (by omega))) 4)
      change 4+rows*(2*(e start).work+4)+clock (passes base rows pitch e (start+1) z) ≤
        4+(z+1)*(4+rows*(2*K+4))
      rw [Nat.succ_mul z (4+rows*(2*K+4))]
      omega
  exact each 0 n (by omega)

end
end Hierarchy.DescentPackedFlowBatch

end OAI
