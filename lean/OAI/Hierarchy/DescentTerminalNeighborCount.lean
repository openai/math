import OAI.Hierarchy.DescentTerminalPortPartners
import OAI.Hierarchy.DescentTerminalReachedOrder

namespace OAI
/-! # Every terminal port group corresponds to a real neighbor or the exterior -/
namespace Hierarchy.DescentTerminalGraphPositions.Order
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {D S p : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} {N : Network D P bits}
variable (L : Order N S p) (near : Fin S→Finset (Fin S))
  (edges : ∀e,L.home (N.dst e)∈near (L.home (N.src e)) ∧ L.home (N.src e)∈near (L.home (N.dst e)))

include edges

omit [Fintype P] in
theorem active_neighbor (i j : Fin S) (z : Group L i) (eqn : z.val=some j) :
    j∈near i := by
  obtain ⟨nm,mem,side⟩:=z.property
  cases nm with
  | inr a=>exact False.elim (by have h:=side.trans eqn;change none=some j at h;cases h)
  | inl a=>
    obtain ⟨e,d⟩:=a
    rcases (between_edge L i j e d).1 ⟨mem,side.trans eqn⟩ with ⟨u,v⟩|⟨u,v⟩
    · simpa only [←u,←v] using (edges e).1
    · simpa only [←u,←v] using (edges e).2

theorem group_count (i : Fin S) : (L.site i).groups≤(near i).card+1 := by
  let f (z : Group L i) : Option (↥(near i)) := match h:z.val with
    | none=>none
    | some j=>some ⟨j,active_neighbor L near edges i j z h⟩
  have reads (z : Group L i) : (f z).map Subtype.val=z.val := by
    rcases z with ⟨_ | j, occupied⟩ <;> rfl
  have inj : Function.Injective f := by
    intro a b eqn
    exact Subtype.ext ((reads a).symm.trans ((congrArg (Option.map Subtype.val) eqn).trans (reads b)))
  change Fintype.card (Group L i)≤_
  simpa using Fintype.card_le_of_injective f inj

end
end Hierarchy.DescentTerminalGraphPositions.Order

namespace Hierarchy.DescentSixParty.Reached
open DescentCompiler DescentHostDirectory DescentTerminalGraphPositions
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits}
    {G:PoweredGadget F} {price ε:ℝ} {S:AtomSchedule} {k age z degree wire hist p : ℕ}
    (R:Reached W G price ε S k age z degree wire hist)
local notation "H" => S.hostSize age
local notation "A" => R.placement

def physicalName : R.V↪Fin H :=
  R.vertex.trans (Fin.castLEEmb R.valid.host)

def neighbors (i : Fin H) : Finset (Fin H) :=
  if h:∃v,R.physicalName v=i then ((A).near h.choose).map R.physicalName else ∅

theorem neighbor_at (v : R.V) : R.neighbors (R.physicalName v)=((A).near v).map R.physicalName := by
  unfold neighbors
  split
  · rename_i present
    exact congrArg (fun u => ((A).near u).map R.physicalName)
      (R.physicalName.injective present.choose_spec)
  · rename_i absent
    exact (absent ⟨v, rfl⟩).elim

theorem neighbor_count (i : Fin H) : (R.neighbors i).card≤(A).degree := by
  unfold neighbors
  split
  · simpa using (A).degreeBound _
  · simp

theorem near_edge (e : W.graph.Edge) :
    R.home (W.graph.dst e)∈R.neighbors (R.home (W.graph.src e)) ∧
    R.home (W.graph.src e)∈R.neighbors (R.home (W.graph.dst e)) := by
  let a:=(A).pos (W.graph.src e)
  let b:=(A).pos (W.graph.dst e)
  have project {u v:Fin (S.groupCount age)×R.V} (h:v∈groupedNear (A).near u) : v.2∈(A).near u.2 := by
    obtain ⟨x,hx,eqn⟩:=Finset.mem_map.mp h
    have hx':x=v.2:=congrArg Prod.snd eqn
    exact hx' ▸ hx
  change R.physicalName b.2∈R.neighbors (R.physicalName a.2) ∧ R.physicalName a.2∈R.neighbors (R.physicalName b.2)
  rw [R.neighbor_at,R.neighbor_at]
  exact ⟨Finset.mem_map_of_mem _ (project ((A).peers e).1),Finset.mem_map_of_mem _ (project ((A).peers e).2)⟩

theorem terminal_groups [Fintype P] (L : Order W.graph H p) (homes : L.home=R.home) :
    (∑i,(L.site i).groups)≤H*((A).degree+1) := by
  have edges : ∀e,L.home (W.graph.dst e)∈R.neighbors (L.home (W.graph.src e)) ∧
      L.home (W.graph.src e)∈R.neighbors (L.home (W.graph.dst e)) := by rw [homes];exact R.near_edge
  have one i:= (L.group_count R.neighbors edges i).trans (Nat.add_le_add_right (R.neighbor_count i) 1)
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>one i)

end
end Hierarchy.DescentSixParty.Reached

end OAI
