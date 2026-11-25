import OAI.Hierarchy.DescentDatedImage
import OAI.Hierarchy.DescentResetOriginalPlanes
import OAI.Hierarchy.DescentEstimatorArenaExtent

namespace OAI
/-! # Issuing the selected-row decoder, original index planes, and gate-route tables after the estimator -/
namespace Hierarchy.DescentGLPacked.BankImage.Dated
open DescentPackedColony.Phase.Arena DescentGLControlCode DescentGLPacked DescentGL DescentGLNielsen
open DescentSIMDLookup DescentColonies Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {h l b w H : ℕ}

def keys (d : ℕ) := (2^d)^d

/-- Consecutive literal cells for row-base multiplication, the offsets of each switch
row, the switch values themselves, and the original coordinate bit planes. -/
def powers (base d : ℕ) : Bank := ⟨base,Nat.clog 2 (keys d)⟩
def cols (base d : ℕ) : Tables :=
  ⟨⟨base+keys d,Nat.clog 2 (Count d)⟩,⟨base+keys d+Count d,Nat.clog 2 (Count d*keys d)⟩⟩
def plane (base d : ℕ) := base+keys d+Count d+Count d*keys d
def wordEnd (base h l : ℕ) := plane base (h+l)+(h+l)*2^h

def controlImage (base : ℕ) (pos : 0<b) : Image w :=
  let d:=h+l
  let T:=cols base d
  let numbers : Memory w:=fun a=>((2^d*(a-base):ℕ):Word w)
  ⟨base,wordEnd base h l,Original.image (h:=h) (l:=l) (plane base d) pos (DescentGLControlCode.mount T (rowName d) numbers)⟩

theorem control_reads (base : ℕ) (pos : 0<b) (mem : Memory w)
    (read : (controlImage (h:=h) (l:=l) base pos).Resident mem) :
    let d:=h+l
    let T:=cols base d
    (∀j : Fin (keys d),mem ((powers base d).base+j.val)=((2^d*j.val:ℕ):Word w)) ∧
    installed T (rowName d) mem ∧
    ∀j z,mem ((Original.bank (plane base d) h j).base+z.val)=(Original.packed (h:=h) (l:=l) pos j z:Word w) := by
  let d:=h+l
  let T:=cols base d
  let src : Memory w:=fun a=>((2^d*(a-base):ℕ):Word w)
  have controls:=mounted T (rowName d) src (by dsimp [T,cols];omega)
  have all (z : ℕ) (lb : base≤z) (ub : z<wordEnd base h l) :
      mem z=Original.image (h:=h) (l:=l) (plane base d) pos (DescentGLControlCode.mount T (rowName d) src) z := read z lb ub
  have before (z : ℕ) (lb : base≤z) (ub : z<plane base d) : mem z=DescentGLControlCode.mount T (rowName d) src z := by
    rw [all z lb (ub.trans_le (Nat.le_add_right (plane base d) (d*2^h)))]
    simp [Original.image,show ¬plane base d≤z by omega]
  refine ⟨?_,⟨?_,?_⟩,?_⟩
  · intro j
    have hj : j.val < keys d := j.isLt
    have off : ¬(T.offsets.base ≤ base+j.val ∧ base+j.val < T.offsets.base+Count d) := by
      change ¬(base+keys d ≤ base+j.val ∧ _)
      omega
    have sw : ¬(T.switches.base ≤ base+j.val ∧ base+j.val < T.switches.base+Count d*((2^d)^d)) := by
      change ¬(base+keys d+Count d ≤ base+j.val ∧ _)
      omega
    change mem (base+j.val) = ((2^d*j.val : ℕ) : Word w)
    rw [before _ (Nat.le_add_right ..) (by unfold plane; omega)]
    simp only [DescentGLControlCode.mount,dite_eq_right off,dite_eq_right sw,src,Nat.add_sub_cancel_left]
  · intro i
    have hi : i.val < Count d := i.isLt
    exact (before (base+keys d+i.val) (by omega) (by unfold plane; omega)).trans (controls.1 i)
  · intro j
    have hj : j.val < Count d*keys d := j.isLt
    exact (before (base+keys d+Count d+j.val) (by omega) (by unfold plane; omega)).trans (controls.2 j)
  · intro j z
    have zlt:=z.isLt
    have room:=Nat.mul_le_mul_right (2^h) j.isLt
    rw [Nat.succ_mul] at room
    rw [all _ (by dsimp [Original.bank,plane];omega) (by dsimp [Original.bank,wordEnd,plane,d] at *;omega)]
    exact Original.resident ..

def routes (C : Chart) (H h l b w : ℕ) : Image w :=
  ⟨C.start,C.heap (h+l),C.install H h l b (fun _=>0)⟩

theorem route_reads (C : Chart) (mem : Memory w) (read : (routes C H h l b w).Resident mem) :
    ∀s : Slot (h+l),∀i : Fin C.page,mem (addr C (s,i))=literal H h l b w s i.val := by
  intro s i
  have upper:=Nat.mul_le_mul_right C.page (finProdFinEquiv s).isLt
  change ((finProdFinEquiv s).val+1)*C.page≤((schedule (h+l)).length*6)*C.page at upper
  rw [Nat.succ_mul] at upper
  have full := upper.trans_eq
    (congrArg (fun n : ℕ => n*C.page) (Nat.mul_comm (schedule (h+l)).length 6))
  have lo : C.start ≤ addr C (s,i) := by dsimp [addr,Chart.base]; omega
  have hi : addr C (s,i) < C.heap (h+l) := by
    have lt := i.isLt
    change C.start+(finProdFinEquiv s).val*C.page+i.val<C.start+6*(schedule (h+l)).length*C.page
    omega
  exact (read _ lo hi).trans (at_slot C H h l b (fun _ => 0) s i)

theorem hardware_lengths (base : ℕ) (pos : 0<b) (C : Chart) :
    (controlImage (w:=w) (h:=h) (l:=l) base pos).length=
      keys (h+l)+Count (h+l)+Count (h+l)*keys (h+l)+(h+l)*2^h ∧
    (routes C H h l b w).length=6*(schedule (h+l)).length*C.page := by
  simp [Image.length,controlImage,wordEnd,plane,routes,Chart.heap,Chart.base]; omega

end
end Hierarchy.DescentGLPacked.BankImage.Dated

end OAI
