import OAI.Hierarchy.DescentDatedPrimitiveExtent
import OAI.Hierarchy.DescentSeedPrintedPitch
import OAI.Hierarchy.DescentGrainCalendar

namespace OAI
/-! Public ordinary work and durable primitive pitches, fixed before the dated choice. -/
namespace Hierarchy.DescentOrdinaryPalette.Configuration
open DescentSixParty DescentCompiler DescentSIMDLookup DescentOrdinaryPrimitiveCheckpoint DescentPrimitivePalette
noncomputable section
variable {F : Type} [Field F]

def returnUnit (bits nodes : ℕ) :=max 1 (bits*nodes)
def returned (h bits nodes : ℕ) :=lanes h (returnUnit bits nodes)

/-- Charge each original digit ROM, lookup, hulling and selector key at the larger of the two real batch widths. -/
def workUnit (degree k cap oldNodes nodes bits : ℕ) :=
  let r:=2^k
  let N:=(degree+1)^4*r*(oldNodes+cap*6)
  let o:=Nat.clog 2 (N+1)
  let refs : DescentOrdinaryRefsROM.Chart:=⟨0,degree,k,oldNodes,nodes,cap,bits,0,0,1⟩
  max 1 (max r (max ((bits*oldNodes)*r) (max (refs.keyBits*r) (max ((bits*N)*r)
    (max (o*nodes+bits*N) (bits*nodes))))))

def atOrdinary (G : PoweredGadget F) (S : AtomSchedule) (op : RotorSpec)
    (p h degree k cap oldNodes nodes previousRoleLanes : ℕ) : Configuration :=
  let s:=S.firstWidth G.b p
  let Z:=S.grainAt G.b p 0
  let b:=printedBits G s Z op
  ⟨op,s,Z,previousRoleLanes,lanes h (workUnit degree k cap oldNodes nodes b),returned h b nodes⟩

theorem returned_fit (h bits nodes : ℕ) : (bits*nodes)*returned h bits nodes≤h/2:=by
  exact (Nat.mul_le_mul_right _ (Nat.le_max_right 1 _)).trans
    (by simpa only [returned,returnUnit,Nat.mul_comm] using lanes_fit h (returnUnit bits nodes))

theorem returned_occupancy (h bits nodes : ℕ) (wide : 2*returnUnit bits nodes≤h) :
    0<returned h bits nodes ∧ h≤4*returned h bits nodes*returnUnit bits nodes:=
  occupancy h _ (lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left ..)) wide

theorem work_room (h D k cap old nodes bits : ℕ) :
    let r:=2^k
    let N:=(D+1)^4*r*(old+cap*6)
    let o:=Nat.clog 2 (N+1)
    let R:DescentOrdinaryRefsROM.Chart:=⟨0,D,k,old,nodes,cap,bits,0,0,1⟩
    let W:=lanes h (workUnit D k cap old nodes bits)
    (bits*old)*(W*r)≤h/2 ∧ R.keyBits*(W*r)≤h/2 ∧ (bits*N*r)*W≤h/2 ∧
      (o*nodes+bits*N)*W≤h/2 ∧ bits*nodes*W≤h/2:=by
  intro r N o R W
  have transferred (v : ℕ) (small : v≤workUnit D k cap old nodes bits) : v*W≤h/2:=
    (Nat.mul_le_mul_right W small).trans (by simpa only [Nat.mul_comm] using lanes_fit h (workUnit D k cap old nodes bits))
  refine ⟨?_,?_,transferred _ (by simp [workUnit,N,r]),transferred _ (by simp [workUnit,o,N,r]),transferred _ (by simp [workUnit])⟩
  · calc (bits*old)*(W*r)=(bits*old*r)*W:=by ac_rfl
         _ ≤ _ :=transferred _ (by simp [workUnit,r])
  · calc R.keyBits*(W*r)=(R.keyBits*r)*W:=by ac_rfl
         _ ≤ _ :=transferred _ (by simp [workUnit,R,r])

theorem return_at (G : PoweredGadget F) (S : AtomSchedule) (op : RotorSpec)
    (p h deg k cap old nodes prior : ℕ) :
    let C:=atOrdinary G S op p h deg k cap old nodes prior
    printedBits G C.seedWidth C.grainLimit op*nodes*C.nextLanes≤h/2:=
  returned_fit ..

end
end Hierarchy.DescentOrdinaryPalette.Configuration

end OAI
