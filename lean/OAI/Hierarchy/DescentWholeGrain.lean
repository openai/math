import OAI.Hierarchy.DescentNetworkWorld
import OAI.Hierarchy.DescentCableUnbundling

namespace OAI
/-! # Routing all exterior and core bundles at one genuine positive width -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open Computability.BorderVNP.Crossing DescentCableUnbundling
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [Field F] {D : ℕ} {P : Type*} {bits : P→ℕ} (A : MarkedWorld F D P bits)
variable (count : A.graph.Edge→ℕ) (q : ℕ) (fit : ∀e,A.graph.width e=count e*q)

abbrev grains : Network D P bits where
  Site := A.graph.Site
  Edge := Σe : A.graph.Edge,Fin (count e)
  finiteSite := A.graph.finiteSite
  finiteEdge := inferInstance
  src p := A.graph.src p.1
  dst p := A.graph.dst p.1
  width _ := q
  attach := A.graph.attach
  position := A.graph.position
  in_ball := A.graph.in_ball

def grainTables : (grains A count q).Tables F := fun v wire pins=>
  A.tables v (fun e=>(splitWord (fit e.val)).symm (fun i=>wire ⟨⟨e.val,i⟩,e.property⟩)) pins

def granular : MarkedWorld F D P bits :=
  ⟨⟨grains A count q,grainTables A count q fit⟩,Finset.univ.filter (fun e=>e.1∈A.core)⟩

def grainAssignments : A.graph.Assignment ≃ (grains A count q).Assignment :=
  (Equiv.piCongrRight (fun e=>splitWord (fit e))).trans
    (Equiv.piCurry (fun (e : A.graph.Edge) (_ : Fin (count e)) => Fin q → Bool)).symm

set_option maxHeartbeats 1000000 in
theorem granular_value (x : Ports bits) : (granular A count q fit).value x=A.value x := by
  classical
  let : DecidableEq (grains A count q).Edge := Classical.decEq _
  unfold World.value Network.value
  let old := fun a : A.graph.Assignment => ∏v,A.graph.read A.tables a x v
  let new := fun z : (grains A count q).Assignment =>
    ∏v,(grains A count q).read (grainTables A count q fit) z x v
  have read (a : A.graph.Assignment) : new (grainAssignments A count q fit a)=old a := by
    apply Finset.prod_congr (by ext;simp)
    intro v _
    unfold Network.read grainTables
    congr 1
    funext e
    have lane (i : Fin (count e.val)) : (grainAssignments A count q fit) a ⟨e.val,i⟩ =
        splitWord (fit e.val) (a e.val) i := rfl
    change (splitWord (fit e.val)).symm (fun i=>(grainAssignments A count q fit) a ⟨e.val,i⟩)=_
    simp only [lane,Equiv.symm_apply_apply]
  calc
    _ = ∑z,new z := Finset.sum_congr (Finset.ext fun a=>⟨fun _=>Finset.mem_univ _,fun _=>Finset.mem_univ _⟩) (fun _ _=>Finset.prod_congr (Finset.ext fun v=>⟨fun _=>Finset.mem_univ _,fun _=>Finset.mem_univ _⟩) (fun _ _=>rfl))
    _ = ∑a,new (grainAssignments A count q fit a) := ((grainAssignments A count q fit).sum_comp new).symm
    _ = ∑a,old a := Finset.sum_congr rfl (fun a _=>read a)
    _ = _ := Finset.sum_congr (Finset.ext fun a=>⟨fun _=>Finset.mem_univ _,fun _=>Finset.mem_univ _⟩) (fun _ _=>Finset.prod_congr (Finset.ext fun v=>⟨fun _=>Finset.mem_univ _,fun _=>Finset.mem_univ _⟩) (fun _ _=>rfl))

include fit in
omit [Field F] in
private theorem grain_sum (mark : Finset A.graph.Edge) :
    (∑e : Σe : A.graph.Edge,Fin (count e),if e.1∈mark then q else 0)=∑e∈mark,A.graph.width e := by
  rw [Fintype.sum_sigma]
  calc
    _ = ∑e,if e∈mark then A.graph.width e else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases keep : e∈mark <;> simp [keep,fit,Nat.mul_comm]
    _ = _ := by simp []

omit [Field F] in
theorem granular_core : (granular A count q fit).liveWidth=A.liveWidth := by
  change (∑e∈Finset.univ.filter (fun e : Σe : A.graph.Edge,Fin (count e)=>e.1∈A.core),q)=_
  rw [Finset.sum_filter]
  exact grain_sum A count q fit A.core

omit [Field F] in
theorem granular_tether : (granular A count q fit).tetherWidth=A.tetherWidth := by
  have total : (∑e : (grains A count q).Edge,(grains A count q).width e)=∑e,A.graph.width e := by
    simpa using grain_sum A count q fit Finset.univ
  have c := granular_core A count q fit
  have l := Finset.sum_add_sum_compl (granular A count q fit).core (granular A count q fit).graph.width
  have r := Finset.sum_add_sum_compl A.core A.graph.width
  change (granular A count q fit).liveWidth+(granular A count q fit).tetherWidth=
    ∑e : (grains A count q).Edge,(grains A count q).width e at l
  change A.liveWidth+A.tetherWidth=_ at r
  omega

omit [Field F] in
theorem granular_width (e : (granular A count q fit).graph.Edge) :
    (granular A count q fit).graph.width e=q := rfl

/-- The load and placement algorithms use the number of equal-width items in
each old cable. The code tensor of the installed router uses granular above. -/
def countWorld : MarkedWorld F D P bits :=
  ⟨⟨{ A.graph with width := count },fun _ _ _=>0⟩,A.core⟩

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
