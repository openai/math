import OAI.Hierarchy.DescentResetCoefficient
import OAI.Hierarchy.DescentResetGoodSites
import OAI.Hierarchy.DescentResetMixedCharge
import OAI.Hierarchy.DescentBadBundles

namespace OAI
/-! # The wire amount of the actual substituted reset network -/

namespace Hierarchy.DescentResetInvoice
open DescentColonies DescentGL DescentBaseVariance DescentMixedRouter
open scoped Classical BigOperators
noncomputable section

variable {I C R W K V : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
    [Fintype V] [DecidableEq V] {n h C₀ bits u k : ℕ}
    {G : NonlinearExpanders.Graph n h} {hw : 0<bits} {contact : I→C}
    {input : Bool→I→R} {site : Bool→R→W} {owner : Bool→C→W}
    {align : ∀s i,site s (input s i)=owner s (contact i)}
local notation "Ch" => Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align

/-- Good sites are selected by inspecting the actual branch at that site. -/
def rotorSites (select : ∀s w,Ch s w) : Finset (Bool×W) :=
  Finset.univ.filter (fun q => (select q.1 q.2).isExceptional=false)

omit [Fintype C] [Fintype R] [Fintype W] in
/-- A core relay is charged once to its marked base even if both ends are
marked. A failed base cannot turn an outside tether into a core term. -/
private theorem flagged_core_invoice (select : ∀s w,Ch s w) (core : Finset I)
    (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k) (keys : Finset (V×ℕ))
    (src dst : I→V×Block k) (weight : V→Block k→ℝ) (unit : ℝ) (hu : 0≤unit)
    (flag : ∀i∈badCore select core,label b (baseOf b hk L (src i))∈keys ∨
      label b (baseOf b hk L (dst i))∈keys)
    (inc : ∀p,load src (fun i=> if i∈core then unit else 0) p +
      load dst (fun i=> if i∈core then unit else 0) p ≤ weight p.1 p.2) :
    (∑ _i∈badCore select core,unit) ≤ ∑ p∈validBases b keys,baseValue b hk weight L p := by
  let hit (i : I) := label b (baseOf b hk L (src i))∈keys ∨ label b (baseOf b hk L (dst i))∈keys
  refine LE.le.trans ?_ (exceptional_core b hk L src dst
    (fun i=> if i∈core then unit else 0) weight (fun i=>by split <;> positivity) inc keys)
  calc
    _ = ∑i : I,if i∈badCore select core then unit else 0 := by simp []
    _ ≤ ∑ i,if hit i then (if i∈core then unit else 0) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases member : i∈badCore select core
      · have inCore : i∈core := (Finset.mem_filter.mp member).1
        simp only [ite_eq_left member,ite_eq_left inCore]
        split
        · exact le_refl _
        · rename_i missing
          exact (missing (flag i member)).elim
      · simp only [ite_eq_right member]
        split <;> first | (split <;> positivity) | positivity

omit [Fintype R] in
/-- The left side sums the widths of the actual substituted graph. The layout
and its bad keys are shared by the endpoint classifier and both placement
receipts. A rotor site is identified by its physical base name and its side. -/
theorem installed_invoice (select : ∀s w,Ch s w) (D : ℕ) (core : Finset I) (H Ht : ℕ)
    (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k) (keys : Finset (V×ℕ))
    (src dst : I→V×Block k) (weight : V→Block k→ℝ) {price pay scale ε β : ℝ}
    (hp : 0≤price) (hn : 0≤pay) (he : 0≤ε) (hb : 0≤β) (rate : price*pay=scale)
    (named : ∃ f : rotorSites select → Bool×BaseId b,Function.Injective f)
    (perBase : ∀q∈rotorSites select,(select q.1 q.2).goodBudget≤pay)
    (flag : ∀i∈badCore select core,label b (baseOf b hk L (src i))∈keys ∨
      label b (baseOf b hk L (dst i))∈keys)
    (inc : ∀p,load src (fun i=> if i∈core then price*u else 0) p +
      load dst (fun i=> if i∈core then price*u else 0) p ≤ weight p.1 p.2)
    (fallback : ∀i∈badCore select core,edgeHops select i≤H)
    (external : ∀i∉core,edgeHops select i≤Ht)
    (hub : (∑v,∑i,weight v i) ≤
      2*(price*∑_i∈core,(u:ℝ))+(β+1)*(price*∑_i∈coreᶜ,(u:ℝ))+ε)
    (span : scale*(∑v,(2:ℝ)^b v) ≤ 4*(ε+∑v,∑i,weight v i))
    (marked : (H:ℝ)*(∑p∈validBases b keys,baseValue b hk weight L p)≤ε+∑v,∑i,weight v i) :
    price*((∑e,(network (K:=K) (C₀:=C₀) G hw u contact input site owner align select D).width e : ℕ):ℝ) ≤
      internalRate h C₀*(price*(∑_i∈core,(u:ℝ))+ε) +
        exteriorRate h C₀ β Ht*(price*∑_i∈coreᶜ,(u:ℝ)) := by
  let M := ∑v,∑i,weight v i
  let X := price*∑_i∈core,(u:ℝ)
  let E := price*∑_i∈coreᶜ,(u:ℝ)
  let budgets := ∑ q : Bool×W,(select q.1 q.2).goodBudget
  let hinges := ∑ _i∈badCore select core,(u:ℝ)
  have xPos : 0≤X := by dsimp [X]; positivity
  have ePos : 0≤E := by dsimp [E]; positivity
  have off (q : Bool×W) (out : q∉rotorSites select) : (select q.1 q.2).goodBudget=0 := by
    apply Choice.goodBudget_eq_zero_of_exceptional
    cases value : (select q.1 q.2).isExceptional <;> simp_all [rotorSites]
  have costs : budgets≤2*(pay*∑v,(2:ℝ)^b v) :=
    DescentRotor.Physical.paired_good_site_pay_le b _ _ named off perBase hn
  have rk : 0≤rotorRate h C₀ := by dsimp [rotorRate]; positivity
  have good : price*(rotorRate h C₀*budgets) ≤
      42*((2*h+4)*(2*h*C₀+2):ℕ)*(scale*∑v,(2:ℝ)^b v) := by
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left costs rk) hp).trans_eq
    rw [←rate]
    dsimp [rotorRate]
    ring
  have exceptional := flagged_core_invoice select core b hk L keys src dst weight (price*u)
    (mul_nonneg hp (Nat.cast_nonneg _)) flag inc
  rw [←Finset.mul_sum] at exceptional
  have paid := (mul_le_mul_of_nonneg_left exceptional (Nat.cast_nonneg H)).trans marked
  have trees : price*((H:ℝ)*hinges + (Ht:ℝ)*(∑_i∈coreᶜ,(u:ℝ))) ≤ M+ε+(Ht:ℝ)*E := by
    dsimp only [hinges,E,M]
    linarith only [paid]
  have joined : price*((∑_i : I,u : ℕ):ℝ)=X+E := by
    dsimp [X,E]
    rw [Nat.cast_sum,←mul_add,Finset.sum_add_sum_compl]
  have complete := component_invoice h C₀ Ht xPos ePos he hb hub
    (show scale*(∑v,(2:ℝ)^b v)≤4*(M+ε) from
      span.trans_eq (congrArg (fun x : ℝ => 4*x) (add_comm ε M)))
    good trees joined.le
  have physical := mul_le_mul_of_nonneg_left
    (DescentMixedRouter.physical_invoice select D core H Ht fallback external) hp
  dsimp only [M,X,E,budgets,hinges] at complete
  linarith only [physical,complete]

end
end Hierarchy.DescentResetInvoice

end OAI
