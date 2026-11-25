import OAI.Hierarchy.DescentStageMeasures
import OAI.Hierarchy.DescentCensusRAM

namespace OAI
/-! # Native row census of an old marked branch -/

namespace Hierarchy.DescentSixParty.MarkedCensus
open StarKeys DescentColonies
open scoped Classical BigOperators
noncomputable section

variable {F P V A : Type} [Field F] [Fintype V] [DecidableEq V] {d k N H : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (pos : W.graph.Site→V) (block : W.graph.Site→Block k)
variable (idx : V ≃ Fin H)

def address (u : W.graph.Site) : Fin (H*2^k) := finProdFinEquiv (idx (pos u),block u)
def cell (v : V) (j : Block k) : Fin (H*2^k) := finProdFinEquiv (idx v,j)

omit [Field F] [Fintype V] [DecidableEq V] in
theorem address_eq (u : W.graph.Site) (v : V) (j : Block k) :
    address W pos block idx u=cell idx v j ↔ pos u=v ∧ block u=j := by
  simp [address,cell,Prod.ext_iff]

omit [Field F] [Fintype V] in
theorem edge_bin (endpt : W.graph.Edge→W.graph.Site) (amount : W.graph.Edge→ℕ)
    (v : V) (j : Block k) :
    blockMass W.graph pos block (fun u=>∑e,if u=endpt e then amount e else 0) v j =
    ∑e,if pos (endpt e)=v ∧ block (endpt e)=j then amount e else 0 := by
  let cond (u : W.graph.Site) := pos u=v ∧ block u=j
  have pull (u : W.graph.Site) :
      (if cond u then ∑e,if u=endpt e then amount e else 0 else 0)=
      ∑e,if u=endpt e then (if cond (endpt e) then amount e else 0) else 0 := by
    by_cases h : cond u
    · rw [ite_eq_left h]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs with hit hc <;> simp_all
    · rw [ite_eq_right h]
      symm;apply Finset.sum_eq_zero
      intro e _
      split_ifs with hit hc <;> simp_all
  change (∑u,if cond u then ∑e,if u=endpt e then amount e else 0 else 0)=_
  simp_rw [pull]
  rw [Finset.sum_comm]
  simp [cond]

def terminalWeight (hub : W.graph.Site→Bool) (wire β : ℕ) (endpt : W.graph.Edge→W.graph.Site)
    (e : W.graph.Edge) := wire*W.graph.width e*(if hub (endpt e) then β else 1)

def historyWeight (atoms : W.graph.Site→List A) (hist : ℕ) (u : W.graph.Site) := hist*(atoms u).length

omit [Field F] [Fintype V] in
theorem endpoint_counts (edges : Fin N ≃ W.graph.Edge) (endpt : W.graph.Edge→W.graph.Site)
    (amount : W.graph.Edge→ℕ) (v : V) (j : Block k) :
    DescentCensusRAM.sumAt (fun i=>address W pos block idx (endpt (edges i))) (amount ∘ edges) (cell idx v j)=
    blockMass W.graph pos block (fun u=>∑e,if u=endpt e then amount e else 0) v j := by
  rw [edge_bin]
  unfold DescentCensusRAM.sumAt
  simp only [address_eq,Function.comp_apply]
  exact edges.sum_comp (fun e=>if pos (endpt e)=v ∧ block (endpt e)=j then amount e else 0)

def marked (e : W.graph.Edge) : ℕ := if e∈W.core then 1 else 0

omit [Field F] [Fintype V] in
/-- A tagged source record contributes precisely one for each genuine core edge. -/
theorem outgoing (edges : Fin N ≃ W.graph.Edge) (v : V) (j : Block k) :
    DescentCensusRAM.sumAt (fun i=>address W pos block idx (W.graph.src (edges i))) (marked W ∘ edges)
      (cell idx v j) =
      blockMass W.graph pos block (fun u=>(W.core.filter (fun e=>W.graph.src e=u)).card) v j := by
  rw [endpoint_counts]
  congr 1
  funext u
  rw [Finset.card_filter]
  calc
    _ = ∑e,if e∈W.core then (if W.graph.src e=u then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases mem : e∈W.core <;> by_cases owns : u=W.graph.src e <;> simp_all [marked,eq_comm]
    _ = _ := by rw [←Finset.sum_filter];simp

omit [Field F] [Fintype V] in
/-- The full weight array consists of the two charged endpoints of every old
cable plus the actual retained history at each old site. A loop contributes
two endpoint occurrences at its own recorded coordinates. -/
theorem full {M : ℕ} (edges : Fin N ≃ W.graph.Edge) (sites : Fin M ≃ W.graph.Site)
    (hub : W.graph.Site→Bool) (atoms : W.graph.Site→List A) (wire β hist : ℕ) (v : V) (j : Block k) :
    DescentCensusRAM.sumAt (fun i=>address W pos block idx (W.graph.src (edges i)))
        (terminalWeight W hub wire β W.graph.src ∘ edges) (cell idx v j) +
      DescentCensusRAM.sumAt (fun i=>address W pos block idx (W.graph.dst (edges i)))
        (terminalWeight W hub wire β W.graph.dst ∘ edges) (cell idx v j) +
      DescentCensusRAM.sumAt (fun i=>address W pos block idx (sites i)) (historyWeight W atoms hist ∘ sites)
        (cell idx v j) = blockMass W.graph pos block (W.siteUnits hub atoms wire β hist) v j := by
  rw [endpoint_counts,endpoint_counts]
  have stored :
      DescentCensusRAM.sumAt (fun i=>address W pos block idx (sites i)) (historyWeight W atoms hist ∘ sites)
        (cell idx v j) = blockMass W.graph pos block (historyWeight W atoms hist) v j := by
    unfold DescentCensusRAM.sumAt blockMass
    simp only [address_eq,Function.comp_apply]
    exact sites.sum_comp (fun u=>if pos u=v ∧ block u=j then historyWeight W atoms hist u else 0)
  rw [stored]
  unfold blockMass
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : pos u=v ∧ block u=j <;> simp [h,MarkedWorld.siteUnits,terminalWeight,historyWeight]

end
end Hierarchy.DescentSixParty.MarkedCensus

end OAI
