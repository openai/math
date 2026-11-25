import OAI.Computability.MultitapeWeakETH.IncidenceRouting

/-! # Unique Boolean flows through the successive stages of a permutation -/

namespace OAI.Computability.MultitapeWeakETH.SwitchFlow

open NearSquareRoot.Benes
open scoped Classical

variable {m : ℕ} {A : Type} (p : Fin (m+1) → Equiv.Perm A)

/-- The permutation from the input bank to the input of a given stage. -/
def partialPerm : (i : Fin (m+1)) → Equiv.Perm A :=
  Fin.induction (Equiv.refl _) fun i previous => previous.trans (p i.castSucc)

def finish := (partialPerm p (Fin.last m)).trans (p (Fin.last m))

/-- At every interior interface the received bit is forwarded. The final
stage has external output, which is read at the same physical sites as input. -/
def Continuous (z : Fin (m+1) → A → Bool) :=
  ∀ (i : Fin m) (x : A), z i.succ (p i.castSucc x) = z i.castSucc x

def lift (input : A → Bool) (i : Fin (m+1)) : A → Bool := input ∘ (partialPerm p i).symm

theorem lift_continuous (input : A → Bool) : Continuous p (lift p input) := by
  intro i x
  simp [lift,partialPerm]

theorem continuous_eq {z : Fin (m+1) → A → Bool} (h : Continuous p z) :
    z = lift p (z 0) := by
  funext i x
  induction i using Fin.induction generalizing x with
  | zero => simp [lift,partialPerm]
  | succ i ih =>
    have eq := h i ((p i.castSucc).symm x)
    rw [Equiv.apply_symm_apply] at eq
    rw [eq,ih]
    simp [lift,partialPerm]

/-- Summing over continuous paths contributes exactly one extension per
initial register bank, independent of the number of padding lanes. -/
def flowEquiv : (A → Bool) ≃ {z // Continuous p z} where
  toFun x := ⟨lift p x,lift_continuous p x⟩
  invFun z := z.val 0
  left_inv x := by funext i; simp [lift,partialPerm]
  right_inv z := Subtype.ext (continuous_eq p z.property).symm

theorem last_output (input : A → Bool) (x : A) :
    lift p input (Fin.last m) ((p (Fin.last m)).symm x) = input ((finish p).symm x) := rfl

private theorem partialPerm_fold (i : Fin (m+1)) (x : A) :
    partialPerm p i x = (List.ofFn (fun j : Fin i.val => p ⟨j.val,by omega⟩)).foldl (fun w f => f w) x := by
  induction i using Fin.induction with
  | zero => simp [partialPerm]
  | succ j ih =>
    change _ = (List.ofFn (fun i : Fin (j.val+1) => p ⟨i.val,by omega⟩)).foldl _ _
    rw [List.ofFn_succ',List.concat_eq_append,List.foldl_append]
    simp only [partialPerm,Fin.induction_succ,Equiv.trans_apply,List.foldl_cons,List.foldl_nil]
    exact congrArg (p j.castSucc) ih

theorem finish_fold (x : A) : finish p x = (List.ofFn p).foldl (fun w f => f w) x := by
  rw [List.ofFn_succ',List.concat_eq_append,List.foldl_append]
  simp only [finish,Equiv.trans_apply,List.foldl_cons,List.foldl_nil]
  exact congrArg (p (Fin.last m)) (partialPerm_fold p (Fin.last m) x)

/-- Plug the physical switch schedule into the generic flow, including
both ascending and descending halves of the Beneš execution order. -/
theorem finish_benes {d : ℕ} (t : RawTable) (permutation : Equiv.Perm (Word d))
    (repr : RawRepresents permutation t) (stages : Fin (m+1) → Bool × ℕ)
    (order : List.ofFn stages = executionOrder d) (x : Word d) :
    finish (fun i => stagePerm t (stages i).1 (stages i).2) x = permutation x := by
  rw [finish_fold]
  have mapped := congrArg (List.map (fun a : Bool × ℕ => stagePerm (d:=d) t a.1 a.2)) order
  rw [List.map_ofFn] at mapped
  rw [show List.ofFn (fun i => stagePerm (d:=d) t (stages i).1 (stages i).2) = _ from mapped]
  exact (List.foldl_map ..).trans (stagesPerm_run permutation t repr x)

end OAI.Computability.MultitapeWeakETH.SwitchFlow
