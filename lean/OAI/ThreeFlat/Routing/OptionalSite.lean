import Mathlib.Tactic
import OAI.ThreeFlat.BitNetworkGlue
import OAI.ThreeFlat.LocalTableNetwork

namespace OAI
/-! # An optional local tensor factor at each public slot

The flag chooses whether the local exchange factor is present. In an unmatched
slot the hidden variables are fixed to zero before contraction. Thus unused
copies contribute exactly one over any semiring.
-/

noncomputable section
namespace ThreeFlat.Routing.OptionalSite

open scoped Classical BigOperators
open TableCompiler

variable {F : Type*} [CommSemiring F] {p : ℕ} (N : BitNetwork F p)

private abbrev Gate := Fin N.cells ⊕ Fin N.internal

private abbrev arity : Gate N → ℕ := Sum.elim (fun _ => 4) (fun _ => 2)

private def check : (g : Gate N) → (Fin (arity N g) → Bool) → F
  | .inl i => fun (x : Fin 4 → Bool) => if x 0 then N.table i (fun j => x j.succ) else 1
  | .inr _ => fun (x : Fin 2 → Bool) => if x 0 = true ∨ x 1 = false then 1 else 0

private def lift : BitSource N.internal p → BitSource N.internal (p+1)
  | .constant b => .constant b
  | .hidden j => .hidden j
  | .pin i => .pin i.succ

private def wire : (g : Gate N) → Fin (arity N g) → BitSource N.internal (p+1)
  | .inl i => Fin.cons (.pin 0) (fun j => lift N (N.source i j))
  | .inr i => ![.pin 0,.hidden i]

def network : BitNetwork F (p+1) :=
  BitNetwork.glue (fun g => localTableNetwork (check N g)) (wire N)

theorem eval (flag : Bool) (pin : Fin p → Bool) :
    (network N).eval (Fin.cons flag pin) = if flag then N.eval pin else 1 := by
  have reads (h : Fin N.internal → Bool) (v : BitSource N.internal p) :
      (lift N v).read h (Fin.cons flag pin) = v.read h pin := by
    cases v <;> simp [lift,BitSource.read]
  have row (h : Fin N.internal → Bool) (i : Fin N.cells) :
      check N (.inl i) (fun k => (wire N (.inl i) k).read h (Fin.cons flag pin)) =
        if flag then N.factor pin h i else 1 := by
    have base : (wire N (.inl i) (0 : Fin 4)).read h (Fin.cons flag pin) = flag := rfl
    have follow (j : Fin 3) : (wire N (.inl i) j.succ).read h (Fin.cons flag pin) =
        (N.source i j).read h pin := reads h (N.source i j)
    change (if (wire N (.inl i) (0 : Fin 4)).read h (Fin.cons flag pin) then
        N.table i (fun j => (wire N (.inl i) j.succ).read h (Fin.cons flag pin)) else 1) = _
    simp only [base,follow,BitNetwork.factor]
  have hidden (h : Fin N.internal → Bool) (i : Fin N.internal) :
      check N (.inr i) (fun k => (wire N (.inr i) k).read h (Fin.cons flag pin)) =
        if flag = true ∨ h i = false then 1 else 0 := by simp [check,wire,BitSource.read]
  simp only [network,BitNetwork.glue_eval,localTableNetwork_eval,Fintype.prod_sum_type,row,hidden]
  cases flag with
  | true => simp [BitNetwork.eval,BitNetwork.weight]
  | false =>
    have zero (h : Fin N.internal → Bool) : (∀ i, h i = false) ↔ h = fun _ => false :=
      ⟨funext, fun e _ => congrFun e _⟩
    simp [Fintype.prod_boole,zero]

theorem size :
    (network N).cells + (network N).internal = 176*N.cells+29*N.internal := by
  unfold network
  rw [BitNetwork.glue_cells,BitNetwork.glue_internal]
  simp only [Fintype.sum_sum_type,localTableNetwork_cells,localTableNetwork_internal]
  norm_num [arity]; omega

end ThreeFlat.Routing.OptionalSite

end
end OAI
