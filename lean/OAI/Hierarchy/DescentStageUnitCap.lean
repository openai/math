import OAI.Hierarchy.DescentMatrixBirthLoad
import OAI.Hierarchy.DescentIntegralSiteLoad
import OAI.Hierarchy.DescentRecordedCore

namespace OAI
/-! # Physical nonhub load including the local history of the installed matrices -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open Computability.BorderVNP.Crossing GadgetNetwork
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {d : ℕ} {P : Type*} {bits : P→ℕ} {Aty Bty : Type*}

omit [Field F] in
/-- Both endpoint columns and the carried descriptions are charged in the original units. -/
theorem units_pay_history (W : MarkedWorld F d P bits) (hub : W.graph.Site→Bool)
    (old : W.graph.Site→List Aty) (wire β hist : ℕ) (hβ : 1≤β) (v : W.graph.Site) :
    wire*GadgetNetwork.siteLoad W.graph v+hist*(old v).length≤W.siteUnits hub old wire β hist v := by
  have h := siteUnits_cover W hub (fun _=>([] : List Aty)) wire β hist hβ v
  unfold siteUnits at h ⊢
  simpa only [List.length_nil,mul_zero,add_zero] using Nat.add_le_add_right h (hist*(old v).length)

omit [Field F] in
/-- Distinct endpoints prevent duplication of a wire in the two columns at a nonhub. -/
theorem siteUnits_nonhub (W : MarkedWorld F d P bits) (hub : W.graph.Site→Bool)
    (old : W.graph.Site→List Aty) (wire β hist : ℕ) (v : W.graph.Site) (ordinary : hub v=false)
    (separates : ∀e,W.graph.src e≠W.graph.dst e) :
    W.siteUnits hub old wire β hist v=wire*GadgetNetwork.siteLoad W.graph v+hist*(old v).length := by
  classical
  unfold siteUnits GadgetNetwork.siteLoad
  rw [←Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl;intro e _
  have diff := separates e
  by_cases s : v=W.graph.src e <;> by_cases t : v=W.graph.dst e
  · exact (diff (s.symm.trans t)).elim
  · simp [←s,t,Ne.symm t,ordinary]
  · simp [←t,s,Ne.symm s,ordinary]
  · simp [s,t,Ne.symm s,Ne.symm t]

variable {I C : Type} [Fintype I] (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (pick : I×Fin 2 ↪ W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
local notation "lay" => bestLayout (branchWidth G z p)
local notation "Z" => W.selected G pick z hz fit pack p
local notation "loc" => (fun u : W.graph.Site=>newSite W.graph pick lay pack (Sum.inl u))

/-- Independently of the arrangement of the old histories, the actual number of new matrix
records plus the surviving wire load costs at most six times the full original fiber. -/
theorem selected_siteUnits_six (hub : W.graph.Site→Bool) (newHub : (Z).graph.Site→Bool)
    (old : W.graph.Site→List Aty) (next : (Z).graph.Site→List Bty) (wire β hist : ℕ)
    (hβ : 1≤β) (enough : ∀i s,6*hist≤wire*W.graph.width (pick (i,s))) (v : (Z).graph.Site)
    (nonhub : newHub v=false)
    (rows : (next v).length=(∑u : {u : W.graph.Site // loc u=v},(old u.val).length)+siteBirths W.graph pick lay pack v) :
    (Z).siteUnits newHub next wire β hist v ≤
      6*(∑u : {u : W.graph.Site // loc u=v},W.siteUnits hub old wire β hist u.val) := by
  classical
  let Fiber := {u : W.graph.Site // loc u=v}
  let oldW := ∑u : Fiber,GadgetNetwork.siteLoad W.graph u.val
  let info := hist*(∑u : Fiber,(old u.val).length)
  let birth := siteBirths W.graph pick lay pack v
  have pay : wire*oldW+info≤∑u : Fiber,W.siteUnits hub old wire β hist u.val := by
    dsimp only [oldW,info];rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun u _=>units_pay_history W hub old wire β hist hβ u.val
  have atomic : hist*birth≤wire*oldW := by
    rw [Nat.mul_comm hist birth]
    exact siteBirths_paid W.graph pick lay pack v hist wire enough
  let zeroPos := fun _ : Merged W.graph pick lay pack=>(0:EuclideanSpace ℝ (Fin d))
  let ball := fun u=> (by simp [zeroPos] : ‖zeroPos u‖≤1)
  have wires : GadgetNetwork.siteLoad (Z).graph v≤5*oldW := merged_site_load_five W.graph pick lay pack zeroPos ball v G z p fit
  have scaled : wire*GadgetNetwork.siteLoad (Z).graph v≤5*(wire*oldW) := (Nat.mul_le_mul_left wire wires).trans_eq (by ring)
  rw [siteUnits_nonhub Z newHub next wire β hist v nonhub (fun e=>e.property),rows,Nat.mul_add]
  change wire*GadgetNetwork.siteLoad (Z).graph v+(info+hist*birth)≤_
  calc
    _ ≤ 6*(wire*oldW+info) := by omega
    _ ≤ 6*(∑ u : Fiber, W.siteUnits hub old wire β hist u.val) := Nat.mul_le_mul_left 6 pay
    _ = _ := congrArg (fun n : ℕ => 6*n) (Finset.sum_congr (by ext; simp) (fun _ _ => rfl))

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
