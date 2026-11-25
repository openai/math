import OAI.Hierarchy.DescentNetworkWorld

namespace OAI
/-! # Renumbering an old network with its physical site and edge permutations -/

namespace Hierarchy.DescentSixParty.PhysicalRename
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {D : ℕ} {P : Type*} {bits : P→ℕ} {F : Type*}

/-- Site and edge carriers keep their finite enumeration. Each stored name now
identifies the original row selected by its physical ordinal. -/
def graph (N : Network D P bits) (s : Equiv.Perm N.Site) (e : Equiv.Perm N.Edge) : Network D P bits where
  Site := N.Site
  Edge := N.Edge
  finiteSite := N.finiteSite
  finiteEdge := N.finiteEdge
  src i := s (N.src (e.symm i))
  dst i := s (N.dst (e.symm i))
  width i := N.width (e.symm i)
  attach p := s (N.attach p)
  position v := N.position (s.symm v)
  in_ball _v := N.in_ball _

variable (N : Network D P bits) (s : Equiv.Perm N.Site) (e : Equiv.Perm N.Edge)

@[simp] theorem src (i : N.Edge) : (graph N s e).src (e i)=s (N.src i) := by simp [graph]
@[simp] theorem dst (i : N.Edge) : (graph N s e).dst (e i)=s (N.dst i) := by simp [graph]
@[simp] theorem width (i : N.Edge) : (graph N s e).width (e i)=N.width i := by simp [graph]
@[simp] theorem attach (p : P) : (graph N s e).attach p=s (N.attach p) := rfl
@[simp] theorem position (v : N.Site) : (graph N s e).position (s v)=N.position v := by simp [graph]

def assignment : N.Assignment ≃ (graph N s e).Assignment :=
  Equiv.piCongrLeft' (fun a : N.Edge=>Fin (N.width a)→Bool) e

/-- The old local function receives precisely its old incident wires and its
original external ports, including loops and repeated parallel cables. -/
def tables (T : N.Tables F) : (graph N s e).Tables F := fun v wire pin =>
  T (s.symm v) (fun i j => wire ⟨e i.val,by
    rcases i.property with h|h
    · exact Or.inl ((src N s e i.val).trans ((congrArg s h).trans (s.apply_symm_apply v)))
    · exact Or.inr ((dst N s e i.val).trans ((congrArg s h).trans (s.apply_symm_apply v)))⟩
    (Fin.cast (width N s e i.val).symm j))
    (fun p => pin ⟨p.val,(congrArg s p.property).trans (s.apply_symm_apply v)⟩)

theorem read (T : N.Tables F) (a : N.Assignment) (x : Ports bits) (v : N.Site) :
    (graph N s e).read (tables N s e T) (assignment N s e a) x v = N.read T a x (s.symm v) := by
  unfold Network.read tables
  apply congrArg (fun wires=>T (s.symm v) wires (fun p=>x p.val))
  funext i j
  have transport {b c : N.Edge} (eqn : b=c) (t : Fin (N.width c)) :
      a b (Fin.cast (congrArg N.width eqn).symm t)=a c t := by subst b; rfl
  exact transport (e.symm_apply_apply i.val) j

theorem contraction [CommSemiring F] (T : N.Tables F) (x : Ports bits) :
    (graph N s e).value (tables N s e T) x=N.value T x := by
  symm
  unfold Network.value
  apply Fintype.sum_equiv (assignment N s e)
  intro a
  apply Fintype.prod_equiv s
  intro v
  rw [read,s.symm_apply_apply]

theorem cost : (graph N s e).cost=N.cost := by
  symm
  unfold Network.cost
  apply Fintype.sum_equiv e
  intro i
  simp only [width,src,dst,position]

theorem placed (place : P→EuclideanSpace ℝ (Fin D)) : (graph N s e).PlacedAt place ↔ N.PlacedAt place := by
  simp only [Network.PlacedAt,attach,position]

variable (A : MarkedWorld F D P bits) (site : Equiv.Perm A.graph.Site) (edge : Equiv.Perm A.graph.Edge)

def world : MarkedWorld F D P bits :=
  ⟨⟨graph A.graph site edge,tables A.graph site edge A.tables⟩,A.core.map edge.toEmbedding⟩

@[simp] theorem core_mem (a : A.graph.Edge) : edge a∈(world A site edge).core ↔ a∈A.core := by
  change edge.toEmbedding a∈A.core.map edge.toEmbedding ↔ _
  exact Finset.mem_map' edge.toEmbedding

theorem value [Field F] : (world A site edge).value=A.value := funext (contraction A.graph site edge A.tables)

theorem liveWidth : (world A site edge).liveWidth=A.liveWidth := by
  change (∑i∈A.core.map edge.toEmbedding,A.graph.width (edge.symm i))=∑i∈A.core,A.graph.width i
  simp only [Finset.sum_map,Equiv.coe_toEmbedding,Equiv.symm_apply_apply]

theorem tetherWidth : (world A site edge).tetherWidth=A.tetherWidth := by
  change (∑i∈(A.core.map edge.toEmbedding)ᶜ,A.graph.width (edge.symm i))=∑i∈A.coreᶜ,A.graph.width i
  have complement : (A.core.map edge.toEmbedding)ᶜ=A.coreᶜ.map edge.toEmbedding := by
    ext i
    simp only [Finset.mem_compl,Finset.mem_map_equiv]
  rw [complement,Finset.sum_map]
  simp only [Equiv.coe_toEmbedding,Equiv.symm_apply_apply]

end
end Hierarchy.DescentSixParty.PhysicalRename

end OAI
