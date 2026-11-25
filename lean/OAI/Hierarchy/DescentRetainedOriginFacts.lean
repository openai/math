import OAI.Hierarchy.DescentDatedOriginCodes
import OAI.Hierarchy.DescentTerminalPointerDigits

namespace OAI
/-! # Original signed lookup in the two wings of an incident edge -/
namespace Hierarchy.DescentTerminalSignedGrainWord
open DescentSharedCableNames DescentTerminalPointerDigits
open scoped Classical Fin.CommRing
noncomputable section
variable {D cap : ℕ}
@[simp] theorem point_project (x : Option (Stage.Live D cap)) :
    point D cap (project D cap (DescentSignedCableCodec.encode x))=x.map grain := by
  rw [point,project,Packed.token_back,DescentSignedCableCodec.decode_encode]
  cases x with
  | none => rfl
  | some u =>
    exact congrArg (fun p : Fin (D*cap) × Fin cap => some (p.1.val,p.2.val))
      (finProdFinEquiv.symm_apply_apply (first u,u.within))

end
end Hierarchy.DescentTerminalSignedGrainWord

namespace Hierarchy.DescentOperandPriorIncidence
open DescentSixParty DescentSharedCableNames
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {T : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W T q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
  (ready : A.StateBounds S i) (v : W.graph.Site)
local notation "home" => Stage.home A v
local notation "ports" => A.CellPorts (home).1.1 (home).1.2 (home).2
local notation "signed" => Stage.signed A native S ready (home).1 (home).2

theorem sign_real (p : ports) : sign A.cap (signed p)=Stage.signedBit A home p := by
  unfold sign Stage.signed
  exact congrArg Prod.fst (Equiv.symm_apply_apply finProdFinEquiv _)

theorem seek_exact {cap : ℕ} (row : Fin (2*cap)→Option (ℕ×ℕ)) (face : Fin 2) (x : ℕ×ℕ)
    (slot : Fin (2*cap)) (same : ∀j,sign cap j=face ∧ row j=some x ↔ j=slot) :
    seek row face x=some slot := by
  cases found : seek row face x with
  | none =>
    exact False.elim (List.find?_eq_none.mp found slot (List.mem_finRange slot)
      (decide_eq_true ((same slot).2 rfl)))
  | some s =>
    have picked := List.find?_some
      (p:=fun j : Fin (2*cap) => decide (sign cap j=face ∧ row j=some x))
      (l:=List.finRange (2*cap)) (a:=s) found
    exact congrArg some ((same s).1 (of_decide_eq_true picked))

theorem port_unique (p p' : ports) (eqn : Stage.recover A home p=Stage.recover A home p')
    (side : Stage.signedBit A home p=Stage.signedBit A home p') : p=p' := by
  cases p with
  | inl l =>
    cases p' with
    | inr r => exact False.elim (by simp [Stage.signedBit] at side)
    | inl r =>
      rcases l with ⟨⟨e,ep,eb⟩,j⟩
      rcases r with ⟨⟨e',ep',eb'⟩,j'⟩
      change (Sigma.mk e j : Stage.Grain A) = ⟨e',j'⟩ at eqn
      cases eqn
      rfl
  | inr l =>
    cases p' with
    | inl r => exact False.elim (by simp [Stage.signedBit] at side)
    | inr r =>
      rcases l with ⟨⟨e,ep,eb⟩,j⟩
      rcases r with ⟨⟨e',ep',eb'⟩,j'⟩
      change (Sigma.mk e j : Stage.Grain A) = ⟨e',j'⟩ at eqn
      cases eqn
      rfl

end
end Hierarchy.DescentOperandPriorIncidence

end OAI
