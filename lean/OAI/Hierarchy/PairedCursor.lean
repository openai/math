import OAI.ThreeFlat.Diagonal.HistoryContraction
import OAI.ThreeFlat.Diagonal.LaneCursorNetwork

namespace OAI
/-! # Paired-input cursor rows as a network of local scalar factors -/

namespace Hierarchy.PairedCursor

open LinearAlgebra.SpectralBooks ThreeFlat
open Diagonal Diagonal.LaneCursor Diagonal.LaneCursor.RowLayout Diagonal.HistoryContraction
open scoped BigOperators Classical
noncomputable section

abbrev Site (n : ℕ) := Fin n × Lane n
abbrev Edge (n copies : ℕ) := (Fin n × Fin ((copies+1)*2)) × Lane n

def shape {k : ℕ} (hk : 2 ≤ k+1) (low offsets slots copies : ℕ) : Shape where
  Site := Site (k+1)
  Edge := Edge (k+1) copies
  Label _ := Fin offsets × PayloadAddress low slots → Bool
  graph := {
    tail := fun e => (e.1.1,e.2)
    head := fun e => let z := ((graph hk (copies+1)).actualTarget e); (z.1.1,z.2)
  }

variable {F : Type} [CommSemiring F] {n k low offsets slots : ℕ}
variable {N : BitNetwork F n} (P : RowLayout N (k+1) low offsets slots)
variable (hk : 2 ≤ k+1) (copies : ℕ)


/-- Bind each outgoing port to its source slot, and each incoming port to the inverse image
of its target slot. This also handles parallel physical arcs. -/
def seed (pin : Fin n → Bool) : (shape hk low offsets slots copies).Factors F :=
  fun v a => portTensor P.mask (P.localTensor pin) v.1 v.2
    (fun s => a ⟨(((v.1,s),v.2),false),rfl⟩)
    (fun s => a ⟨(((graph hk (copies+1)).actualTarget.symm ((v.1,s),v.2)),true),by
      change (((graph hk (copies+1)).actualTarget _).1.1, ((graph hk (copies+1)).actualTarget _).2)=v
      rw [Equiv.apply_symm_apply]; rfl⟩)

/-- Only the cursor-zero site of the bucket holding its row can see this input pin. -/
def owner (j : Fin n) : Site (k+1) := (0,(splitRow _ _ (P.pinRow j)).1)

theorem seed_local (v : Site (k+1)) (a b : Fin n → Bool)
    (agree : ∀ j, owner P j=v → a j=b j) :
    seed P hk copies a v = seed P hk copies b v := by
  by_cases h : v.1=0
  · have same : P.localTensor a v.2=P.localTensor b v.2 := P.localTensor_pins a b _ fun j hj =>
      agree j (Prod.ext h.symm hj)
    funext x
    simp only [seed,portTensor,same]
  · funext x
    simp only [seed,portTensor,h,ite_false]

private def fieldEquiv : (shape hk low offsets slots copies).Boundary ≃
    Fields (k+1) copies (Fin offsets) (PayloadAddress low slots) where
  toFun a i s l := a ((i,s),l)
  invFun a e := a e.1.1 e.1.2 e.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem contract_seed (pin : Fin n → Bool) :
    (shape hk low offsets slots copies).contract (seed P hk copies pin) = N.eval pin := by
  rw [← P.eval_cursor_graph (r:=copies) hk pin]
  unfold Shape.contract PortGraph.contraction
  apply Fintype.sum_equiv (fieldEquiv (low:=low) (offsets:=offsets) (slots:=slots) hk copies)
  intro a
  change (∏ v : Site (k+1), _) = _
  rw [Fintype.prod_prod_type]
  rfl

end
end Hierarchy.PairedCursor

end OAI
