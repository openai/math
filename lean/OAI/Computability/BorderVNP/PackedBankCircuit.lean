import OAI.Computability.BorderVNP.PackedPoolCircuit
import OAI.Computability.BorderVNP.ShortenStaticRowsAccess

/-! # Writing the public cable rectangle for each paid profile bank

Only the three cable-width formulas depend on the matched size and histogram.
The row number and both site names are fixed arithmetic addresses in the rectangles
reserved by the combining step. All four columns are emitted on the same Boolean frame.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankCircuit

open Word ParseBatchSort VPVNP.VerifierNetwork Shortening Shortening.StaticRows

/-- The four word columns of a bank cable in the public directory. -/
inductive Column where
  | row | source | destination | width
  deriving DecidableEq

instance : Fintype Column :=
  ⟨{.row,.source,.destination,.width}, by intro c; cases c <;> simp⟩

variable {D m : ℕ} {K : Type*} [Field K] (e : Crossing.PaidIdentity K D m)

/-- Input field and fixed multiplier for a cable-width computation. The absent field
is the number of matched blocks; a present field is a particular histogram count. -/
def operand : TemplateEdge e → Option (Fin e.count) × ℕ
  | .inl _ => (none,Nat.clog 2 e.count)
  | .inr (.inl (a,_)) => (some a,m)
  | .inr (.inr ⟨a,z⟩) => (some a,(e.net a).width z)

variable {A : Type*} (seed : A → ℕ) (oldSites oldEdges : ℕ)

private noncomputable def siteAddress (a : A) (v : TemplateSite e) : ℕ :=
  oldSites + ((Fintype.equivFin (TemplateSite e) v).val + Fintype.card (TemplateSite e) * seed a)

private noncomputable def edgeAddress (a : A) (u : TemplateEdge e) : ℕ :=
  let r := oldEdges * (2*D+1)
  (r+r) + (r + ((Fintype.equivFin (TemplateEdge e) u).val + Fintype.card (TemplateEdge e)*seed a))

/-- The public name, endpoints and width of one bank edge. -/
noncomputable def read (a : A) (u : TemplateEdge e) (fields : Option (Fin e.count) → ℕ) : Column → ℕ
  | .row => edgeAddress e seed oldEdges a u
  | .source => siteAddress e seed oldSites a (templateSrc e u)
  | .destination => siteAddress e seed oldSites a (templateDst e u)
  | .width => templateWidth e (fields none) (fun t => fields (some t)) u

private noncomputable def expression (a : A) (u : TemplateEdge e) : Column → WidthExpr (Option (Fin e.count))
  | .row => .const (edgeAddress e seed oldEdges a u)
  | .source => .const (siteAddress e seed oldSites a (templateSrc e u))
  | .destination => .const (siteAddress e seed oldSites a (templateDst e u))
  | .width => PoolCircuit.scaleExpr (operand e u).1 (operand e u).2

private theorem product_width (u : TemplateEdge e) (x : Option (Fin e.count) → ℕ) :
    (operand e u).2 * x (operand e u).1 = templateWidth e (x none) (fun t => x (some t)) u := by
  rcases u with _ | ⟨_,_⟩ | ⟨_,_⟩ <;> exact Nat.mul_comm _ _

private theorem expression_eval (a : A) (u : TemplateEdge e) (c : Column) (x : Option (Fin e.count) → ℕ) :
    (expression e seed oldSites oldEdges a u c).eval x = read e seed oldSites oldEdges a u x c := by
  cases c <;> first | rfl | exact (PoolCircuit.scale_eval _ _ _).trans (product_width e u x)

private theorem expression_fits (a : A) (u : TemplateEdge e) (c : Column) (w : ℕ)
    (x : Option (Fin e.count) → ℕ) (hx : ∀ i, x i < 2^w) (hc : read e seed oldSites oldEdges a u x c < 2^w) :
    (expression e seed oldSites oldEdges a u c).Fits w x := by
  cases c <;> first | exact hc | exact PoolCircuit.scale_fits w x _ _ (hx _) ((product_width e u x).trans_lt hc)

/-- Static bound for the arithmetic expression of each output column. -/
def nodeBudget (u : TemplateEdge e) : ℕ :=
  (PoolCircuit.scaleExpr (operand e u).1 (operand e u).2).nodes + 1

private theorem expression_nodes (a : A) (u : TemplateEdge e) (c : Column) :
    (expression e seed oldSites oldEdges a u c).nodes ≤ nodeBudget e u := by
  cases c <;> dsimp only [expression,nodeBudget,WidthExpr.nodes] <;> omega

/-- All seeds share the producing frame. Its gates are paid once, and the remaining
gate count is linear in the number of seeds and quadratic in the binary word width.
The coefficient is determined by the fixed paid identity. -/
theorem exists_bankFrame [Fintype A] {σ : Type*} [Fintype σ] (w : ℕ)
    (source : Frame σ (A × Option (Fin e.count) × Fin w)) :
    ∃ f : Frame σ (A × TemplateEdge e × Column × Fin w),
      f.size ≤ source.size + 1 + Fintype.card A *
        (4 * (∑ u : TemplateEdge e, nodeBudget e u) * (100*(w+1)^2)) ∧
      ∀ (x : σ → Bool) (a : A) (u : TemplateEdge e) (c : Column),
        let fields := fun i => value (fun j => source.eval x (a,i,j))
        read e seed oldSites oldEdges a u fields c < 2^w →
        value (fun j => f.eval x (a,u,c,j)) = read e seed oldSites oldEdges a u fields c := by
  classical
  let localFrame (t : A × TemplateEdge e × Column) :=
    ((expression e seed oldSites oldEdges t.1 t.2.1 t.2.2).frame w).subst
      (Frame.initial (fun i : Option (Fin e.count) × Fin w => (t.1,i)))
  obtain ⟨joint,hs,he⟩ := Crossing.exists_parallelFrames localFrame
  let pins (i : A × TemplateEdge e × Column × Fin w) : Σ _ : A × TemplateEdge e × Column, Fin w :=
    ⟨(i.1,i.2.1,i.2.2.1),i.2.2.2⟩
  refine ⟨(joint.select pins).subst source, ?_, ?_⟩
  · have hl (t : A × TemplateEdge e × Column) : (localFrame t).size ≤ nodeBudget e t.2.1 * (100*(w+1)^2) := by
      simp only [localFrame,Frame.subst_size,Frame.initial_size,zero_add]
      exact ((expression e seed oldSites oldEdges t.1 t.2.1 t.2.2).frame_size w).trans
        (Nat.mul_le_mul_right _ (expression_nodes e seed oldSites oldEdges _ _ _))
    have hcard : Fintype.card Column = 4 := by decide
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hl t)
    have hreshape : (∑ t : A × TemplateEdge e × Column, nodeBudget e t.2.1 * (100*(w+1)^2)) =
        Fintype.card A * (4 * (∑ u : TemplateEdge e, nodeBudget e u) * (100*(w+1)^2)) := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]
      rw [← Finset.mul_sum, ← Finset.sum_mul, Nat.mul_assoc 4]
      simp
    rw [hreshape] at hsum
    simp only [Frame.subst_size,Frame.select_size]
    exact (Nat.add_le_add_left (hs.trans (Nat.add_le_add_left hsum 1)) _).trans_eq (by omega)
  · intro x a u c fields h
    let z := fun i : Option (Fin e.count) × Fin w => source.eval x (a,i)
    have hf : (expression e seed oldSites oldEdges a u c).Fits w fields :=
      expression_fits e seed oldSites oldEdges a u c w fields (fun _ => value_lt _) h
    have hx : (fun j => ((joint.select pins).subst source).eval x (a,u,c,j)) =
        ((expression e seed oldSites oldEdges a u c).frame w).eval z := by
      funext j
      simp [Frame.subst_eval,pins,he,localFrame,z]
      congr 1
      funext i
      simp
    rw [hx]
    exact ((expression e seed oldSites oldEdges a u c).frame_value w z hf).trans
      (expression_eval e seed oldSites oldEdges a u c fields)

end Packing.BankCircuit

end BorderVNP
end Computability
end OAI
