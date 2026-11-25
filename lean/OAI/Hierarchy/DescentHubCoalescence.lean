import OAI.Hierarchy.DescentHubDirectory
import OAI.Hierarchy.DescentRecordedCore

namespace OAI
/-! # The physical marked graph after coalescing the external hub prefixes -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open Computability.BorderVNP.Crossing DescentNetworkPartition DescentHostDirectory DescentColonies
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {d : ℕ} {P V : Type} {bits : P→ℕ} [DecidableEq V]
variable (A : MarkedWorld F d P bits) (key : A.graph.Site→Key V)
variable (hub : V→Bool) (k g : ℕ)

def reclaimed : Finset (Key V) := Finset.univ.image (mergeHub hub k g ∘ key)
def address (u : A.graph.Site) : reclaimed A key hub k g :=
  ⟨mergeHub hub k g (key u),Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

local notation "site" => address A key hub k g
local notation "pos" => (fun _ : reclaimed A key hub k g=>(0:EuclideanSpace ℝ (Fin d)))
local notation "ball" => (fun v=> (by simp : ‖pos v‖≤1))

def coalesced : MarkedWorld F d P bits :=
  ⟨⟨quotient A.graph site pos ball,tables A.graph site pos ball A.tables⟩,
    Finset.univ.filter fun e=>e.val∈A.core⟩

theorem coalesced_value (x : Ports bits) : (coalesced A key hub k g).value x=A.value x :=
  value_eq A.graph site pos ball A.tables x

theorem coalesced_read (p : P) :
    ((coalesced A key hub k g).graph.attach p).val=mergeHub hub k g (key (A.graph.attach p)) := rfl

private theorem subset_widths {E : Type} [Fintype E] {C : E→Prop} [DecidablePred C]
    (w : E→ℕ) (s : Finset E) :
    (∑ e∈(Finset.univ.filter fun e : Subtype C=>e.val∈s),w e.val)≤∑e∈s,w e := by
  let S := Finset.univ.filter fun e : Subtype C=>e.val∈s
  let inc := Function.Embedding.subtype C
  have small : S.map inc⊆s := by
    rintro _ hx
    obtain ⟨e,mem,rfl⟩ := Finset.mem_map.mp hx
    exact (Finset.mem_filter.mp mem).2
  simpa only [S,inc,Finset.sum_map,Function.Embedding.coe_subtype] using
    (Finset.sum_le_sum_of_subset small (f:=w))

theorem coalesced_core : (coalesced A key hub k g).liveWidth≤A.liveWidth :=
  subset_widths A.graph.width A.core

theorem coalesced_tether : (coalesced A key hub k g).tetherWidth≤A.tetherWidth := by
  calc
    _ = ∑ e ∈ (Finset.univ.filter fun e : CrossingEdge A.graph site => e.val ∈ A.coreᶜ),
        A.graph.width e.val := by
      unfold tetherWidth
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      have in_univ (ft : Fintype (CrossingEdge A.graph site)) (e : CrossingEdge A.graph site) :
          e ∈ @Finset.univ _ ft := @Finset.mem_univ _ ft e
      ext e
      constructor
      · intro tether
        have outside : e ∉ (coalesced A key hub k g).core := Finset.mem_compl.mp tether
        apply Finset.mem_filter.mpr
        refine ⟨in_univ _ e, Finset.mem_compl.mpr ?_⟩
        intro inside
        apply outside
        exact Finset.mem_filter.mpr ⟨in_univ _ e, inside⟩
      · intro surviving
        have outside := Finset.mem_compl.mp (Finset.mem_filter.mp surviving).2
        apply Finset.mem_compl.mpr
        intro inside
        exact outside (Finset.mem_filter.mp inside).2
    _ ≤ _ := subset_widths A.graph.width A.coreᶜ

theorem coalesced_geometry (near : V→Finset V) {a D slots : ℕ}
    (ag : a≤g) (gk : g≤k)
    (close : ∀e,key (A.graph.dst e)∈directory near D slots 8 (key (A.graph.src e)))
    (room : ∀u,(key u).2.2<slots)
    (full : ∀u,hub (key u).1=true→∃b : Block k,(key u).2.1=(k-a,group (k-a) b))
    (e : (coalesced A key hub k g).graph.Edge) :
    ((coalesced A key hub k g).graph.dst e).val∈directory near (D+g) slots 10
      ((coalesced A key hub k g).graph.src e).val :=
  merged_cable_hops hub near ag gk (close e.val) (room _) (room _) (full _) (full _)

theorem coalesced_dvd (q : ℕ) (div : ∀e∈A.core,q∣A.graph.width e) :
    ∀e∈(coalesced A key hub k g).core,q∣(coalesced A key hub k g).graph.width e := by
  intro e he
  exact div e.val (Finset.mem_filter.mp he).2

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
