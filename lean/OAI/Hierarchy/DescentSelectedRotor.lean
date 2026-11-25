import OAI.Hierarchy.DescentGoodBase
import OAI.Hierarchy.DescentRotorHost
import OAI.Hierarchy.DescentRotorROM

namespace OAI
/-! # Retaining the fixed permutation-menu selector at every active rotor layer -/

namespace Hierarchy.DescentRotor
open LinearAlgebra.SpectralBooks ThreeFlat
open RouteUnits
open scoped BigOperators Classical
noncomputable section
variable {K : Type*} [Field K] {Y : ℕ} {c : Fin Y → Fin Y → ℕ} {C w : ℕ}

def fixedTable (menu : ∀ π : Equiv.Perm (Fin Y), Configures K c C w π)
    (π : Equiv.Perm (Fin Y)) := (menu π).choose

/-- Evaluate any concrete layer controller which routes the true packet endpoints. -/
theorem routed_layers {E : Type*} [Fintype E] [NeZero Y]
    (menu : ∀ π : Equiv.Perm (Fin Y), Configures K c C w π) (source target : E → Fin Y) (L : ℕ)
    (color : E → Fin (2*L+1)) (π : Fin (2*L+1) → Equiv.Perm (Fin Y))
    (valid : ∀e,π (color e) (source e)=target e)
    (unique : ∀e f,color e=color f → source e=source f → e=f)
    (u : ℕ) (x y : E → Fin u → Fin (2^w)) :
    (∏r, attachedLayer (fixedTable menu (π r)) u
      (fun v=>fillRows 0 (fun e=>(color e,source e)) x (r,v))
      (fun v=>fillRows 0 (fun e=>(color e,target e)) y (r,v))) =
      if ∀e,x e=y e then 1 else 0 := by
  have terms (r : Fin (2*L+1)) := (menu (π r)).choose_spec u
    (fun v=> fillRows 0 (fun e=>(color e,source e)) x (r,v))
    (fun v=> fillRows 0 (fun e=>(color e,target e)) y (r,v))
  simp_rw [attachedLayer_eq,fixedTable,terms]
  have routed := fillRows_routes (0 : Fin u → Fin (2^w)) source target color π valid unique x y
  by_cases equal : ∀e,x e=y e
  · simp [routed.mpr equal,equal]
  · have denied := mt routed.mp equal
    push Not at denied
    obtain ⟨r,v,fail⟩ := denied
    rw [ite_eq_right equal]
    exact Finset.prod_eq_zero (Finset.mem_univ r) (ite_eq_right (fun all=>fail (all v)))

/-- The selector is retained as data. A fixed table chosen once per permutation,
common at all bundle powers and across all layers and bases, supplies the values. -/
theorem selected_layers {E : Type*} [Fintype E] [NeZero Y]
    (menu : ∀ π : Equiv.Perm (Fin Y), Configures K c C w π) (source target : E → Fin Y) (L : ℕ)
    (row : ∀ v, (Finset.univ.filter fun e => source e=v).card≤L)
    (col : ∀ v, (Finset.univ.filter fun e => target e=v).card≤L) :
    ∃ color : E → Fin (2*L+1), ∃ π : Fin (2*L+1) → Equiv.Perm (Fin Y),
      ∀ (u : ℕ) (x y : E → Fin u → Fin (2^w)),
      (∏r, attachedLayer (fixedTable menu (π r)) u
        (fun v=>fillRows 0 (fun e=>(color e,source e)) x (r,v))
        (fun v=>fillRows 0 (fun e=>(color e,target e)) y (r,v))) =
        if ∀e,x e=y e then 1 else 0 := by
  obtain ⟨color,π,valid,unique⟩ := permutation_layers source target L row col
  exact ⟨color,π,routed_layers menu source target L color π valid unique⟩

end
end Hierarchy.DescentRotor

end OAI
