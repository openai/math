import OAI.Hierarchy.ProtocolRAMStripColumnPrograms
import OAI.Hierarchy.ProtocolRAMStripPhysicalStep
import OAI.Hierarchy.ProtocolRAMBoughtEventColumn
import OAI.Hierarchy.ProbeStripPortGeometry

namespace OAI
/-! # Original-ball edge programs for both geometries of the actual strip chart -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe BoughtSockets PurchaseFrozen
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
variable {z W k dp attempts w : ℕ} {S : PurchaseSampler}

/-- Original chronological purchase × original stratum × original DFS candidate.
Only that immutable prefix and the actual row register enter the lookup. -/
def birthRow (stride birth : ℕ) : Expr := .op .add (.lit (birth*stride)) .row

theorem birthRow_read (v : Directory attempts) (S : PurchaseSampler) (z d k depth : ℕ) (a : Fin attempts)
    (i : Fin (v.header z d k S.degree depth).ports) (m : Memory w) :
    (birthRow (v.header z d k S.degree depth).ports a.val).eval m (i.val:Word w)=
      (((v.header z d k S.degree depth).enum ⟨a,i⟩).val:Word w) := by
  let stride := (v.header z d k S.degree depth).ports
  change ((a.val*stride:ℕ):Word w)+(i.val:Word w)=((i.val+stride*a.val:ℕ):Word w)
  rw [←Nat.cast_add,Nat.mul_comm a.val stride,Nat.add_comm]

/-- In a later repair one obtains exactly the parent's real positive row from
its original ball and the physical flag of the same chronological acquisition. -/
theorem checkedOriginal (b : Board) (v : Directory attempts) (S : PurchaseSampler) (z d k depth : ℕ)
    (size : (v.header z d k S.degree depth).count=b.boughtRows)
    (a : Fin attempts) (j : Fin (v.header z d k S.degree depth).ports) (m : Memory w) (r : Word w) (ball : Expr)
    (ballRead : ball.eval m r=(j.val:Word w)) (fit : b.rows<2^w)
    (funded : b.bought.flag.eval m (((v.header z d k S.degree depth).enum ⟨a,j⟩).val:Word w)≠0) :
    let head:=v.header z d k S.degree depth
    let physical:=b.boughtIndex (Fin.cast size (head.enum ⟨a,j⟩))
    (b.commonID (b.originalProbe head.ports a.val ball)).eval m r-(b.idBase:Word w)=(physical.val:Word w) := by
  intro head physical
  let candidate := (v.header z d k S.degree depth).enum ⟨a,j⟩
  apply (b.commonID_sub (b.originalProbe head.ports a.val ball) m r).trans
  apply b.checked_bought _ m r (Fin.cast size candidate) fit _ funded
  rw [b.originalProbe_read head.ports a.val ball m r j ballRead]
  have index : candidate.val=a.val*head.ports+j.val := by
    change j.val+head.ports*a.val=a.val*head.ports+j.val
    rw [Nat.mul_comm head.ports a.val,Nat.add_comm]
  change (((b.coreRows+(a.val*head.ports+j.val):ℕ):Word w)).val=b.coreRows+candidate.val
  rw [←index]
  have bounded : b.coreRows + candidate.val < 2^w := physical.isLt.trans fit
  exact Fin.val_cast_of_lt bounded

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
