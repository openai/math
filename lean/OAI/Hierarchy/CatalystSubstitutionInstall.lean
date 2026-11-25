import OAI.Hierarchy.CatalystSubstitutionResidual

namespace OAI
/-! # Physical installation and exact hardware counts for heterogeneous calls -/

noncomputable section
namespace Hierarchy.CatalystSubstitution
open Catalyst ThreeFlat Routing
open scoped Classical BigOperators

variable {F : Type*} [Field F] {k p : ℕ}

def cutContext (o : Occurrence F k) (os : List (Occurrence F k))
    (C : Host F k p (Sockets (o::os))) : Context F k p o.arity :=
  ⟨C.width,TypedWiring.localTable (fun x : Port p C.width ⊕ Fin o.arity → Bool =>
    ∑ t : Sockets os → Bool, C.coeff (x ∘ Sum.inl) (Sum.elim (x ∘ Sum.inr) t) * exactWeight os t)⟩

private theorem cut_coeff (o : Occurrence F k) (os : List (Occurrence F k))
    (C : Host F k p (Sockets (o::os))) (x : Port p C.width → Bool) (h : Fin o.arity → Bool) :
    (cutContext o os C).coeff x h =
      ∑ t : Sockets os → Bool, C.coeff x (Sum.elim h t) * exactWeight os t := by
  unfold Context.coeff cutContext
  rw [TypedWiring.localTable_value]; rfl

theorem exact_cut (o : Occurrence F k) (os : List (Occurrence F k))
    (C : Host F k p (Sockets (o::os))) :
    Agrees (tableApprox C.width (exactValue (o::os) C)) (exactPlug (cutContext o os C) o.target) := by
  let : DecidableEq (Fin o.arity ⊕ Sockets os) := Classical.decEq _
  refine ⟨rfl,fun x => ?_⟩
  change Port p C.width → Bool at x
  change (tableApprox C.width (exactValue (o::os) C)).coeff x =
    (exactPlug (cutContext o os C) o.target).coeff x
  erw [tableApprox_coeff,exactPlug_coeff]
  simp only [cut_coeff o os C,Finset.sum_mul]
  unfold exactValue
  change (∑ h : Fin o.arity ⊕ Sockets os → Bool, C.coeff x h *
    (o.target (h ∘ Sum.inl) * exactWeight os (h ∘ Sum.inr))) = _
  erw [← (Equiv.sumArrowEquivProdArrow (Fin o.arity) (Sockets os) Bool).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro t _
  change C.coeff x (Sum.elim h t) * (o.target h * exactWeight os t) = _
  ring

theorem approximate_cut (o : Occurrence F k) (os : List (Occurrence F k))
    (C : Host F k p (Sockets (o::os))) :
    Agrees (approxPlug (cutContext o os C) o.replacement)
      (tableApprox (residual C o.replacement).width (exactValue os (residual C o.replacement))) := by
  refine ⟨rfl,fun x => ?_⟩
  change Port p (fun j => C.width j+o.replacement.width j) → Bool at x
  change (approxPlug (cutContext o os C) o.replacement).coeff x =
    (tableApprox (residual C o.replacement).width (exactValue os (residual C o.replacement))).coeff x
  erw [approxPlug_coeff,tableApprox_coeff]
  unfold exactValue
  simp only [residual_coeff C o.replacement,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  erw [cut_coeff o os C _ t,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  exact mul_right_comm _ _ _

theorem empty_cut (C : Host F k p (Sockets [])) :
    Agrees (tableApprox C.width (exactValue [] C)) (finish C) := by
  refine ⟨rfl,fun x => ?_⟩
  change Port p C.width → Bool at x
  change (tableApprox C.width (exactValue [] C)).coeff x = (finish C).coeff x
  erw [tableApprox_coeff,finish_coeff]
  let : IsEmpty (Sockets ([] : List (Occurrence F k))) := inferInstanceAs (IsEmpty Empty)
  unfold exactValue
  erw [Fintype.sum_unique]
  simp only [exactWeight,mul_one]; exact congrArg (C.coeff x) (Subsingleton.elim _ _)

/-- Construct the final physical approximation by gluing one occurrence at a time. -/
def install : (os : List (Occurrence F k)) → (C : Host F k p (Sockets os)) → Approximation F k p
  | [], C => finish C
  | o::os, C => install os (residual C o.replacement)

omit [Field F] in
/-- Native cell count is exactly the original cells plus all replacement cells. -/
theorem install_cells (os : List (Occurrence F k)) (C : Host F k p (Sockets os)) :
    (install os C).network.cells = C.network.cells + (os.map (·.replacement.network.cells)).sum := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    let rest := (os.map (fun x => x.replacement.network.cells)).sum
    calc
      _ = (residual C o.replacement).network.cells + rest := ih _
      _ = (C.network.cells + o.replacement.network.cells) + rest :=
        congrArg (fun n => n + rest) (residual_cells C o.replacement)
      _ = _ := Nat.add_assoc ..

omit [Field F] in
/-- The glued data sockets become internal bits, in addition to the host and
replacement internals. All catalyst slots remain external. -/
theorem install_internal (os : List (Occurrence F k)) (C : Host F k p (Sockets os)) :
    (install os C).network.internal = C.network.internal +
      (os.map (fun o => o.arity + o.replacement.network.internal)).sum := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    let rest := (os.map (fun x => x.arity + x.replacement.network.internal)).sum
    calc
      _ = (residual C o.replacement).network.internal + rest := ih _
      _ = (o.arity + (C.network.internal + o.replacement.network.internal)) + rest :=
        congrArg (fun n => n + rest) (residual_internal C o.replacement)
      _ = _ := by change _ = C.network.internal + ((o.arity + o.replacement.network.internal) + rest); omega

omit [Field F] in
theorem install_width (os : List (Occurrence F k)) (C : Host F k p (Sockets os)) (j : Fin k) :
    (install os C).width j = C.width j + (os.map (fun o => o.replacement.width j)).sum := by
  induction os with
  | nil => simp [install,finish]
  | cons o os ih => rw [install,ih]; simp [residual,Nat.add_assoc]

omit [Field F] in
private theorem residual_size {H : Type} [Fintype H] {q : ℕ}
    (C : Host F k p (Fin q ⊕ H)) (X : Approximation F k q) :
    hostSize (residual C X) + q = hostSize C + X.size := by
  have pack := (Fintype.card_congr (portEquiv (p:=p) C.width X.width)).symm
  rw [Fintype.card_sum (α:=Port p C.width) (β:=Wire X.width × Bool)] at pack
  change (residual C X).network.cells + (residual C X).network.internal +
    Fintype.card (Port p (fun j => C.width j+X.width j) ⊕ H) + q =
    C.network.cells + C.network.internal + Fintype.card (Port p C.width ⊕ (Fin q ⊕ H)) +
      (X.network.cells + X.network.internal + Fintype.card (Fin q ⊕ Wire X.width × Bool))
  rw [residual_cells,residual_internal]
  have finalPorts := Fintype.card_sum (α:=Port p (fun j => C.width j+X.width j)) (β:=H)
  have oldPorts := Fintype.card_sum (α:=Port p C.width) (β:=Fin q ⊕ H)
  have oldSockets := Fintype.card_sum (α:=Fin q) (β:=H)
  have newPorts := Fintype.card_sum (α:=Fin q) (β:=Wire X.width × Bool)
  have callArity := Fintype.card_fin q
  omega

omit [Field F] in
/-- Complete physical accounting, including all open catalyst endpoints. -/
theorem install_size (os : List (Occurrence F k)) (C : Host F k p (Sockets os)) :
    (install os C).size + (os.map (·.arity)).sum =
      hostSize C + (os.map (·.replacement.size)).sum := by
  induction os with
  | nil =>
    change C.network.cells + C.network.internal + Fintype.card (Port p C.width) =
      C.network.cells + C.network.internal + Fintype.card (Port p C.width ⊕ Empty)
    exact congrArg (fun n => C.network.cells + C.network.internal + n)
      (Fintype.card_congr (Equiv.sumEmpty (Port p C.width) Empty)).symm
  | cons o os ih =>
    let head : Host F k p (Fin o.arity ⊕ Sockets os) := C
    change (install os (residual head o.replacement)).size + (o.arity + (os.map (·.arity)).sum) =
      hostSize head + (o.replacement.size + (os.map (·.replacement.size)).sum)
    have step := residual_size head o.replacement
    have tail := ih (residual head o.replacement)
    omega

end Hierarchy.CatalystSubstitution

end
end OAI
