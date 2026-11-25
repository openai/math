import OAI.Hierarchy.DescentNetworkWorld
import OAI.Hierarchy.DescentBaseVariance

namespace OAI
/-! # The total occurrence load of an actual marked network -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open DescentBaseVariance
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {D : ℕ} {P : Type*} {bits : P → ℕ}

/-- Charge an ordinary endpoint once and a hub endpoint at its fixed
exterior-tether multiplier. Each occurrence keeps its own list of atoms. -/
def siteLoad {Aty : Type*} (W : MarkedWorld F D P bits) (hub : W.graph.Site → Bool)
    (atoms : W.graph.Site → List Aty) (u β atomUnit : ℝ) (v : W.graph.Site) : ℝ :=
  load W.graph.src (fun e => u * W.graph.width e * (if hub (W.graph.src e) then β else 1)) v +
  load W.graph.dst (fun e => u * W.graph.width e * (if hub (W.graph.dst e) then β else 1)) v +
  atomUnit * (atoms v).length

omit [Field F] in
/-- Each core edge has two ordinary incidences. A tether has one ordinary
incidence and one hub incidence, even when its public slot represents a
stack of many original exterior bits. -/
theorem siteLoad_sum {Aty : Type*} (W : MarkedWorld F D P bits) (hub : W.graph.Site → Bool)
    (atoms : W.graph.Site → List Aty) (u β atomUnit : ℝ)
    (core : ∀ e∈W.core,hub (W.graph.src e)=false ∧ hub (W.graph.dst e)=false)
    (tether : ∀ e∉W.core,hub (W.graph.src e)≠hub (W.graph.dst e)) :
    (∑ v,siteLoad W hub atoms u β atomUnit v) =
      2*(u*W.liveWidth)+(β+1)*(u*W.tetherWidth)+
        atomUnit*(∑ v,((atoms v).length : ℝ)) := by
  have mass (p : W.graph.Edge→W.graph.Site) (val : W.graph.Edge→ℝ) :
      (∑v,load p val v)=∑e,val e := by
    unfold load
    rw [Finset.sum_comm]
    simp
  simp only [siteLoad,Finset.sum_add_distrib,mass,liveWidth,tetherWidth,Nat.cast_sum,Finset.mul_sum]
  apply congrArg (·+∑v,atomUnit*((atoms v).length:ℝ))
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_sum_compl W.core]
  congr 1
  · apply Finset.sum_congr rfl
    intro e he
    obtain ⟨a,b⟩ := core e he
    simp [a,b]
    ring
  · apply Finset.sum_congr rfl
    intro e he
    have diff := tether e (Finset.mem_compl.mp he)
    cases a : hub (W.graph.src e) <;> cases b : hub (W.graph.dst e) <;>
      simp [a,b] at diff ⊢ <;> ring

omit [Field F] in
/-- The only extra load comes from the retained atoms in these lists. -/
theorem siteLoad_bound {Aty : Type*} (W : MarkedWorld F D P bits) (hub : W.graph.Site → Bool)
    (atoms : W.graph.Site → List Aty) (u β atomUnit ε : ℝ)
    (core : ∀ e∈W.core,hub (W.graph.src e)=false ∧ hub (W.graph.dst e)=false)
    (tether : ∀ e∉W.core,hub (W.graph.src e)≠hub (W.graph.dst e))
    (retained : atomUnit*(∑ v,((atoms v).length : ℝ))≤ε) :
    (∑ v,siteLoad W hub atoms u β atomUnit v) ≤
      2*(u*W.liveWidth)+(β+1)*(u*W.tetherWidth)+ε := by
  rw [siteLoad_sum W hub atoms u β atomUnit core tether]
  exact add_le_add_right retained _

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
