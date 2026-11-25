import OAI.LinearAlgebra.SpectralBooks.PortWiring
import OAI.LinearAlgebra.SpectralBooks.CrossingWireClass
import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct

/-! # The tensor class of an arbitrary finite port wiring -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph

open SiteTensor
open scoped Classical BigOperators

variable {V E : Type} (G : PortGraph V E) (K : Type*) [Field K] [Fintype V] [Nonempty V]
    [Fintype E] (A : E → Type) [∀ e, Fintype (A e)]

/-- One leg per vertex records exactly the wire values at all of its ports. -/
def rawWiring : Raw.{0} V K where
  Leg := G.State A
  finiteLeg _ := inferInstance
  coeff := G.wiring A

/-- An individual wire is the common-label diagonal on its two endpoints. -/
def edgeRaw (e : E) : Raw.{0} V K :=
  (Raw.diagonal (Fin 2) K (A e)).group ![G.tail e, G.head e]

private def endBit (j : Fin 2) : Bool := j != 0

private def endIndex : Bool → Fin 2
  | false => 0
  | true => 1

private theorem bit_index (b : Bool) : endBit (endIndex b) = b := by cases b <;> rfl

private theorem index_bit (j : Fin 2) : endIndex (endBit j) = j := by fin_cases j <;> rfl

omit [Fintype V] [Nonempty V] [Fintype E] in
private theorem vertex_bit (e : E) (j : Fin 2) :
    G.vertex e (endBit j) = ![G.tail e, G.head e] j := by fin_cases j <;> rfl

private def splitPorts (v : V) : G.State A v ≃ ((e : E) → (G.edgeRaw K A e).Leg v) where
  toFun x e j := x ⟨(e,endBit j.val),(G.vertex_bit e j.val).trans j.property⟩
  invFun y p := y p.val.1 ⟨endIndex p.val.2, by
    rw [← G.vertex_bit, bit_index]; exact p.property⟩
  left_inv x := by
    funext ⟨⟨e,b⟩,h⟩
    cases b <;> rfl
  right_inv x := by
    funext e j
    dsimp
    exact congrArg (x e) (Subtype.ext (index_bit _))

omit [Fintype V] [Nonempty V] [Fintype E] in
private theorem edgeRaw_split_coeff (x : (i : V) → G.State A i) (e : E) :
    (G.edgeRaw K A e).coeff (fun i => G.splitPorts K A i (x i) e) =
      if x (G.tail e) ⟨(e,false),rfl⟩ = x (G.head e) ⟨(e,true),rfl⟩ then 1 else 0 := by
  let s : Fin 2 → A e := ![x (G.tail e) ⟨(e,false),rfl⟩, x (G.head e) ⟨(e,true),rfl⟩]
  have he : (G.edgeRaw K A e).coeff (fun i => G.splitPorts K A i (x i) e) =
      (Raw.diagonal (Fin 2) K (A e)).coeff s := by
    apply congrArg (Raw.diagonal (Fin 2) K (A e)).coeff
    funext i
    fin_cases i <;> rfl
  rw [he, Raw.diagonal_coeff_at (0 : Fin 2)]
  simp [s, Fin.forall_fin_two, eq_comm]

/-- The local port test tensor is exactly the tensor product of the independent
wires, including loops and parallel edges. -/
theorem ofRaw_rawWiring :
    ofRaw (G.rawWiring K A) = ∏ e, ofRaw (G.edgeRaw K A e) := by
  let j := (Fintype.equivFin E).symm
  rw [← Equiv.prod_comp j (fun e => ofRaw (G.edgeRaw K A e)), ← ofRaw_finProduct]
  apply ofRaw_eq_iff.mpr
  let eqv (v : V) := (G.splitPorts K A v).trans (Equiv.piCongrLeft' _ j.symm)
  apply Raw.reindex_equivalent (X := G.rawWiring K A)
    (Y := Raw.finProduct (fun i => G.edgeRaw K A (j i))) eqv
  intro (x : (i : V) → G.State A i)
  change G.wiring A x = ∏ i, (G.edgeRaw K A (j i)).coeff (fun v => G.splitPorts K A v (x v) (j i))
  simp_rw [edgeRaw_split_coeff]
  rw [Equiv.prod_comp j (fun e => if x (G.tail e) ⟨(e,false),rfl⟩ = x (G.head e) ⟨(e,true),rfl⟩ then (1:K) else 0)]
  simp only [wiring, Fintype.prod_boole]
  split_ifs <;> trivial

end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
