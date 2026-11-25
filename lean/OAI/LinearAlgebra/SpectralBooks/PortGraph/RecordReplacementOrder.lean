import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPatchRecord
import OAI.LinearAlgebra.SpectralBooks.PortGraph.BoundedPatchReplacementClosure
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentStubNames
import OAI.LinearAlgebra.SpectralBooks.UniformDecorations.UniformDecorations

/-! # Numbered old patch inputs and the stub names in polygon order -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.PatchShape

open UniformDecorations

variable {K : ℕ} (R : PatchShape K)

abbrev LocalPorts (v : R.Vertex) := R.toPiece.graph.Port v ⊕ {s : R.Stub // R.toPiece.attach s = v}

/-- Each numbered old port is either an internal paired port or its named boundary stub. -/
def slotEquiv (v : R.Vertex) : R.LocalPorts v ≃ Fin (R.typeAt v).degree.val := by
  let owner (u : (R.Wire × Bool) ⊕ R.Stub) := u.elim (fun p => R.toPiece.graph.vertex p.1 p.2) R.toPiece.attach
  let f : R.LocalPorts v ≃ {u // owner u = v} := (Equiv.subtypeSum (p:=fun u => owner u = v)).symm
  let g : {u // owner u = v} ≃ {p : R.Dart // p.1 = v} := R.endEquiv.subtypeEquiv (by
    rintro (⟨e,b⟩ | s)
    · cases b <;> rfl
    · rfl)
  exact (f.trans g).trans
    { toFun := fun ⟨⟨u,i⟩,h⟩ => Fin.cast (congrArg (fun j => (R.typeAt j).degree.val) h) i
      invFun := fun i => ⟨⟨v,i⟩,rfl⟩
      left_inv := by rintro ⟨⟨u,i⟩,rfl⟩; rfl
      right_inv := fun _ => rfl }

theorem total_degree (v : R.Vertex) :
    Fintype.card (R.toPiece.graph.Port v) + Fintype.card {s // R.toPiece.attach s = v} =
      (R.typeAt v).degree.val := by
  simpa only [LocalPorts, Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr (R.slotEquiv v)

theorem total_degree_le (v : R.Vertex) :
    Fintype.card (R.toPiece.graph.Port v) + Fintype.card {s // R.toPiece.attach s = v} ≤ 4 :=
  (R.total_degree v).le.trans (Nat.le_of_lt_succ (R.typeAt v).degree.isLt)

/-- Read a literal address in the old shared tables from the two parts of a
local state. Repeated occurrences of the same address use the same variable. -/
def oldAddress {w : ℕ} (v : R.Vertex) (x : R.toPiece.graph.Port v → Bits w)
    (y : {s // R.toPiece.attach s = v} → Bits w) : Address w :=
  ⟨R.typeAt v, Sum.elim x y ∘ (R.slotEquiv v).symm⟩

@[simp] theorem slotEquiv_internal_val {v : R.Vertex} (p : R.toPiece.graph.Port v) :
    (R.slotEquiv v (.inl p)).val = (R.read (.inl p.val)).2.val := by rfl

@[simp] theorem slotEquiv_stub_val {v : R.Vertex} (p : {s // R.toPiece.attach s = v}) :
    (R.slotEquiv v (.inr p)).val = p.val.val.2.val := by rfl

/-- Restrict shared old tables to the ports and boundary stubs saved in this record. -/
def oldTable {A : Type*} {w : ℕ} (U : Tables A w) :
    R.toPiece.graph.StubTable R.toPiece.attach (Bits w) A :=
  fun v a s => let j := R.oldAddress v a s; U j.1 j.2

def oldValue {A : Type*} [CommSemiring A] {w : ℕ} (U : Tables A w) (x : R.Stub → Bits w) : A :=
  R.toPiece.graph.openValue R.toPiece.attach (R.oldTable U) x

/-- The distinguished output is the last stub. Reading the remaining polygon
sites in order omits the ordinary vertices. -/
theorem labels_cons_root {V B : Type*} [Fintype B] {n : ℕ}
    (order : V ⊕ B ≃ Fin (n+1)) (out : B) (hroot : order (.inr out) = Fin.last n)
    {l : List B} (hl : l = (List.finRange n).filterMap (fun i => stubLabel order i.castSucc)) :
    (out :: l).Nodup ∧ ∀ s, s ∈ out :: l := by
  have full := stubOrder_complete order
  have last : stubLabel order (Fin.last n) = some out := by simp [← hroot, stubLabel]
  dsimp only at full
  rw [List.finRange_succ_last, List.filterMap_append, List.filterMap_map] at full
  have h : (l ++ [out]).Nodup ∧ ∀ s, s ∈ l ++ [out] := by
    simpa only [hl, Function.comp_def, List.filterMap_cons, last, List.filterMap_nil] using
      And.intro full.1 full.2.1
  exact ⟨List.perm_append_comm.nodup_iff.mp h.1,
    fun s => by simpa only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, false_or, or_comm] using h.2 s⟩

end PortGraph.PatchShape

end

end SpectralBooks
end LinearAlgebra
end OAI
