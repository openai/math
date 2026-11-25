import OAI.Hierarchy.DescentPaidSweepLayout
import OAI.Hierarchy.DescentPaidActorPresence

namespace OAI
/-! # One field directory for all resolved successor labels and one shared funded-count directory -/
namespace Hierarchy.DescentPaidResidentCount.Sweep
open DescentSIMDLookup DescentPackedZip DescentPackedActorMask DescentOrdinaryAtomFieldRAM.ROM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {n p : ℕ}

def select (N : ℕ) (label : Cell n) (ids : Cell (n*N)) (_ : Cell 0) :=target n N label ids

theorem select_empty (N : ℕ) (label : Cell n) : select N label 0 0=0 := by
  have decoded : (encode n N).symm 0=fun _=>0 := by
    apply (encode n N).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    change 0=(finFunctionFinEquiv (fun _ : Fin N=>(0:Cell n))).val
    simp []
  have clear : ∀i : Fin N,¬(label≠0 ∧ (encode n N).symm 0 i=label) :=by
    intro i h
    exact h.1 (by simpa only [decoded] using h.2.symm)
  apply Fin.ext
  change (finFunctionFinEquiv (fun i : Fin N=>if label≠0 ∧ (encode n N).symm 0 i=label then (1:Cell 1) else 0)).val=0
  simp [clear]

def maskPages (labels : Fin p→ Cell n) (N M : ℕ) (j : Fin (p*2)) : Page :=
  let t:=finProdFinEquiv.symm j
  binary (select N (labels t.1)) M t.2

def maskTable (labels : Fin p→ Cell n) (N M base : ℕ) (j : Fin p) :=
  joined (maskPages labels N M) ((n*N)*M) base (Presence.pair j)

def sumPages (D cap b M : ℕ) :=binary (counted D cap b) M
def sumTable (D cap b M base : ℕ) :=
  joined (sumPages D cap b M) (sumBits D cap b M) base id

theorem mask_page (labels : Fin p→ Cell n) (N M : ℕ) (j : Fin p) (t : Fin 2) :
    maskPages labels N M (Presence.pair j t)=binary (select N (labels j)) M t :=by
  simp [maskPages,Presence.pair]

theorem mask_width (labels : Fin p→ Cell n) (N M : ℕ) (i : Fin (p*2)) :
    (maskPages labels N M i).bits≤(n*N)*M :=by
  obtain ⟨⟨j,t⟩,rfl⟩:=finProdFinEquiv.surjective i
  change (maskPages labels N M (Presence.pair j t)).bits≤(n*N)*M
  rw [mask_page labels N M j t]
  fin_cases t
  · exact le_rfl
  · change (n*N+0)*M≤(n*N)*M
    simp

theorem sum_width (D cap b M : ℕ) (i : Fin 2) :
    (sumPages D cap b M i).bits≤ sumBits D cap b M :=by
  fin_cases i
  · exact Nat.mul_le_mul_right M (Nat.le_add_right _ _)
  · exact le_rfl

theorem table_kept {w M a b c top : ℕ} {T : Tables} {u v : Expr} {f : Cell a→ Cell b→ Cell c}
    {m o : Memory w} (fit : Fits T u v a b M top w) (previous : Static T f M m)
    (keep : ∀q,q<top→ o q=m q) : Static T f M o := by
  refine ⟨fun k=>?_,fun k=>?_⟩
  · have bound : k.val<T.shift.size := by simpa only [Bank.size,fit.shiftBits] using k.isLt
    exact (keep _ ((Nat.add_lt_add_left bound _).trans_le fit.shift.2.2)).trans (previous.1 k)
  · have bound : k.val<T.apply.size :=by simpa only [Bank.size,fit.applyBits] using k.isLt
    exact (keep _ ((Nat.add_lt_add_left bound _).trans_le fit.apply.2.2)).trans (previous.2 k)

theorem clear_source {H G M w : ℕ} (m : Memory w) :
    Source (.lit 0) (fun (_:Fin H) (_:Fin G)=>(0:Cell 0)) M m :=
  Presence.clear_source m

def job (base D cap b M : ℕ) (labels : Fin p→ Cell n) (ids counts : Expr) (j : Fin p) : Expr :=
  (sumTable D cap b M (sumBase base p D cap n M)).read
    ((maskTable labels (actors D cap) M base j).read ids (.lit 0)) counts

theorem job_work (base D cap b M : ℕ) (labels : Fin p→ Cell n) (ids counts : Expr) (j : Fin p) :
    (job base D cap b M labels ids counts j).work=ids.work+counts.work+23 :=by
  simp only [job,DescentPackedZip.work,Expr.work];omega

end
end Hierarchy.DescentPaidResidentCount.Sweep

end OAI
