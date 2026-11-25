import OAI.Computability.BorderVNP.PackedGridInitialFactors

/-! # Reading the original private rows after equality subdivision -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing CellSparse Diagonal.CellEntries
open scoped Classical

variable {D : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits) (routes : N.WireRoutes)

/-- At an original site, find the incident endpoint hop of each original lane. A
loop reads its source hop, as in the physical subdivision table. -/
noncomputable def endpointLane (v : N.Site) :
    CellBox.Lane N v → CellBox.Lane (N.subdivide routes) (.inl v)
  | .inl ⟨e,k⟩ =>
    if h : N.src e.val = v then .inl ⟨⟨⟨e.val,0⟩,Or.inl (congrArg Sum.inl h)⟩,k⟩
    else .inl ⟨⟨⟨e.val,Fin.last _⟩,Or.inr (by simp [Network.subdivide,e.property.resolve_left h])⟩,k⟩
  | .inr ⟨p,k⟩ => .inr ⟨⟨p.val, congrArg Sum.inl p.property⟩,k⟩

/-- The unchanged original descriptor follows its endpoint hops. At an inserted site
a truth table compares the two adjacent hop words bit for bit. -/
noncomputable def routedRule (original : ∀ v, Rule N v) :
    ∀ v, Rule (N.subdivide routes) v
  | .inl v =>
    match original v with
    | .truth f => .truth (fun b => f (b ∘ endpointLane N routes v))
    | .unary l report => .unary (endpointLane N routes v l) report
  | .inr j => .truth (fun b => decide (∀ k : Fin (N.width j.1),
      b (.inl ⟨⟨⟨j.1,j.2.castSucc⟩,Or.inr (by simp [Network.subdivide])⟩,k⟩) =
        b (.inl ⟨⟨⟨j.1,j.2.succ⟩,Or.inl (by simp [Network.subdivide])⟩,k⟩)))

variable {R : Type*} [Zero R] [One R]

/-- Turn the private rule's physical Boolean response into a guard over any zero-one
coefficient type. Reports are supplied once from the exterior use-bit directory. -/
noncomputable def guardedTable (original : ∀ v, Rule N v) (use : Port → Bool) : N.Tables R :=
  fun v a x => if (original v).passes (fun
    | .inl ⟨e,i⟩ => a e i
    | .inr ⟨p,i⟩ => x p i) use then 1 else 0

/-- The actual table computed by the routed one-copy descriptors agrees at every
local entry with the paper's equality subdivision of the original guarded rows. -/
theorem guarded_routed (original : ∀ v, Rule N v) (use : Port → Bool) :
    guardedTable (R := R) (N.subdivide routes) (routedRule N routes original) use =
      N.subdivideTables routes (guardedTable N original use) := by
  funext v a x
  cases v with
  | inl v =>
    cases hr : original v with
    | truth f =>
      simp only [guardedTable,routedRule,hr,Rule.passes,Network.subdivideTables,Function.comp_def]
      apply congrArg (fun b => if f b then (1:R) else 0)
      funext l
      rcases l with ⟨e,i⟩ | ⟨p,i⟩
      · by_cases h : N.src e.val = v <;> simp [endpointLane,h]
      · rfl
    | unary l report =>
      simp only [guardedTable,routedRule,hr,Rule.passes,Network.subdivideTables]
      apply congrArg (fun b => if b == use report then (1:R) else 0)
      rcases l with ⟨e,i⟩ | ⟨p,i⟩
      · by_cases h : N.src e.val = v <;> simp [endpointLane,h]
      · rfl
  | inr j =>
    simp only [guardedTable,routedRule,Rule.passes,Network.subdivideTables,decide_eq_true_eq]
    split <;> rename_i he
    · exact (ite_eq_left (funext he)).symm
    · exact (ite_eq_right (fun h => he (congrFun h))).symm

end Packing.GridBoxes

end BorderVNP
end Computability
end OAI
