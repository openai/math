import OAI.Hierarchy.DescentRecordedBranch
import OAI.Hierarchy.DescentMergedCore
import OAI.Hierarchy.DescentCableUnbundling

namespace OAI
/-! # Recurring core bundle units and the distinct exterior tether invoice -/

namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] {D : ℕ} {P : Type*} {bits : P → ℕ}
variable {I C : Type} [Fintype I]

namespace MarkedWorld

private theorem same_complement {α : Type*} (s : Finset α) (left right : Fintype α)
    (dl dr : DecidableEq α) :
    (letI := left; letI := dl; sᶜ) = (letI := right; letI := dr; sᶜ) := by
  cases Subsingleton.elim left right
  cases Subsingleton.elim dl dr
  rfl

variable (A : MarkedWorld F D P bits)
def pieces (q : ℕ) (m : A.graph.Edge → ℕ) (fit : ∀e∈A.core,A.graph.width e=m e*q) :
    MarkedWorld F D P bits :=
  ⟨⟨DescentCableUnbundling.network A.graph A.core m q,
    DescentCableUnbundling.tables A.graph A.core m q fit A.tables⟩,
   DescentCableUnbundling.nextCore A.graph A.core m q⟩

theorem pieces_value (q : ℕ) (m : A.graph.Edge → ℕ) (fit : ∀e∈A.core,A.graph.width e=m e*q)
    (x : Ports bits) : (A.pieces q m fit).value x=A.value x :=
  DescentCableUnbundling.value_eq A.graph A.core m q fit A.tables x

omit [Field F] in
theorem pieces_core (q : ℕ) (m : A.graph.Edge → ℕ) (fit : ∀e∈A.core,A.graph.width e=m e*q) :
    (A.pieces q m fit).liveWidth=A.liveWidth := DescentCableUnbundling.core_width A.graph A.core m q fit

omit [Field F] in
theorem pieces_tether (q : ℕ) (m : A.graph.Edge → ℕ) (fit : ∀e∈A.core,A.graph.width e=m e*q) :
    (A.pieces q m fit).tetherWidth=A.tetherWidth := by
  have bill := DescentCableUnbundling.tether_width A.graph A.core m q
  unfold tetherWidth
  refine Eq.trans ?_ (bill.trans ?_)
  all_goals
    apply Finset.sum_congr _ (fun _ _ => rfl)
    exact same_complement _ _ _ _ _

variable (G : PoweredGadget F) (pick : I×Fin 2 ↪ A.graph.Edge) (z : I → ℕ) (hz : ∀i,0<z i)
  (fit : ∀i s,A.graph.width (pick (i,s))=z i*G.b) (pack : A.graph.Site→C)

def selected (p : I→Profile G.C) : MarkedWorld F D P bits :=
  ⟨recorded G A.toWorld pick z hz fit pack p,
    GadgetNetwork.nextCore A.graph pick (branchWidth G z p) (bestLayout (branchWidth G z p)) pack
      (fun _ => (0 : EuclideanSpace ℝ (Fin D))) (fun _ => by simp) A.core⟩

theorem selected_sum (x : Ports bits) : (∑p,(selected A G pick z hz fit pack p).value x)=A.value x :=
  recorded_sum G A.toWorld pick z hz fit pack x

set_option maxHeartbeats 600000 in
theorem selected_tether (p : I→Profile G.C) :
    (selected A G pick z hz fit pack p).tetherWidth≤A.tetherWidth := by
  have bill := GadgetNetwork.nextTether_width_le A.graph pick (branchWidth G z p)
    (bestLayout (branchWidth G z p)) pack (fun _ => (0 : EuclideanSpace ℝ (Fin D)))
    (fun _ => by simp) A.core
  unfold tetherWidth
  refine (le_of_eq ?_).trans (bill.trans (le_of_eq ?_))
  all_goals
    apply Finset.sum_congr _ (fun _ _ => rfl)
    exact same_complement _ _ _ _ _

theorem selected_core (picked : ∀t,pick t∈A.core) (p : I→Profile G.C) :
    ((selected A G pick z hz fit pack p).liveWidth:ℝ)+2*(G.b:ℝ)*(∑i,z i:ℕ)≤
      (A.liveWidth:ℝ)+G.rate*(G.b*(∑i,z i):ℕ) := by
  let sw := branchWidth G z p
  obtain ⟨l,room⟩ := G.common_layout_saving p z
  have best : (surviving sw (bestLayout sw):ℝ)≤surviving sw l := by exact_mod_cast best_le sw l
  have raw := GadgetNetwork.nextCore_width_paid A.graph pick sw (bestLayout sw) pack
    (fun _ => (0 : EuclideanSpace ℝ (Fin D))) (fun _ => by simp) A.core picked G.b z fit
  have realBill : ((selected A G pick z hz fit pack p).liveWidth:ℝ)+2*(G.b:ℝ)*(∑i,z i:ℕ)≤
      (A.liveWidth:ℝ)+(surviving sw (bestLayout sw):ℝ) := by exact_mod_cast raw
  exact realBill.trans (add_le_add (le_refl _) (best.trans room))

/-- After a layer all surviving cables retain the next coarser common integer unit.
This makes the next sum of physical gadget occurrences well typed. -/
theorem selected_dvd (q : ℕ) (unit : ∀e∈A.core,q∣A.graph.width e)
    (picked : ∀t,pick t∈A.core) (zunit : ∀i,q∣z i) (p : I→Profile G.C) :
    ∀e∈(selected A G pick z hz fit pack p).core,q∣(selected A G pick z hz fit pack p).graph.width e := by
  rintro ⟨e,he⟩ marked
  have yes := (GadgetNetwork.mem_nextCore A.graph pick (branchWidth G z p) (bestLayout (branchWidth G z p))
    pack (fun _ => (0 : EuclideanSpace ℝ (Fin D))) (fun _=>by simp) A.core ⟨e,he⟩).mp marked
  rcases e with old|(arm|wire)
  · exact unit old yes
  · exact unit (pick arm) (picked arm)
  · exact dvd_mul_of_dvd_left (zunit wire.1) _

end MarkedWorld
end
end Hierarchy.DescentSixParty

end OAI
