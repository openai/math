import OAI.ThreeFlat.BitNetwork
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
/-! # Rectangular hidden-address banks with canonical unused slots -/

namespace ThreeFlat.BitNetwork.Rectangular

open scoped Classical BigOperators

variable {F : Type*} [CommSemiring F] {p n H : ℕ}

/-- A random-access partial inverse identifies the actual owner-local variable
in a physical slot. Out-of-range slots have the unique value `false`. -/
structure Address (n H : ℕ) where
  put : Fin n → Fin H
  get : Fin H → Option (Fin n)
  get_put : ∀ x, get (put x) = some x
  put_get : ∀ i x, get i = some x → put x = i

variable (N : BitNetwork F p) (A : Address N.internal H)

def move : BitSource N.internal p → BitSource H p
  | .pin j => .pin j
  | .constant b => .constant b
  | .hidden i => .hidden (A.put i)

def isHole (q : Fin H) := (A.get q).isNone

def checkSource (q : Fin H) : Fin 3 → BitSource H p := fun _ => .hidden q

def network : BitNetwork F p where
  internal := H
  cells := N.cells+H
  source := Fin.append (fun c j => move N A (N.source c j)) (checkSource (p:=p))
  table := Fin.append N.table (fun q z => if isHole N A q = true ∧ z 0 = true then 0 else 1)

private def expand (v : Fin N.internal → Bool) (q : Fin H) := ((A.get q).map v).getD false

omit [CommSemiring F] in
private theorem expand_put (v : Fin N.internal → Bool) (i : Fin N.internal) :
    expand N A v (A.put i) = v i := by simp [expand,A.get_put]

omit [CommSemiring F] in
private theorem expand_injective : Function.Injective (expand N A) := by
  intro f g h
  funext i
  simpa only [expand_put] using congrFun h (A.put i)

omit [CommSemiring F] in
private theorem move_read (s : BitSource N.internal p) (g : Fin H → Bool) (pin : Fin p → Bool) :
    (move N A s).read g pin = s.read (g ∘ A.put) pin := by cases s <;> rfl

private theorem weight_eq (g : Fin H → Bool) (pin : Fin p → Bool) :
    (network N A).weight pin g =
      if expand N A (g ∘ A.put) = g then N.weight pin (g ∘ A.put) else 0 := by
  change (∏ c : Fin (N.cells+H), (network N A).factor pin g c) = _
  refine (Fin.prod_univ_add (fun c : Fin (N.cells+H) => (network N A).factor pin g c)).trans ?_
  have rows (c : Fin N.cells) : (network N A).factor pin g (c.castAdd H) = N.factor pin (g ∘ A.put) c := by
    simp only [network,factor,Fin.append_left,move_read]
  have checks (q : Fin H) : (network N A).factor pin g (Fin.natAdd N.cells q) =
      if isHole N A q = true ∧ g q = true then 0 else 1 := by
    simp only [network,factor,Fin.append_right,checkSource,BitSource.read]
  simp only [rows,checks]
  by_cases ok : expand N A (g ∘ A.put) = g
  · have good (q : Fin H) : ¬(isHole N A q = true ∧ g q = true) := by
      rintro ⟨hq,yes⟩
      cases e : A.get q with
      | some x => simp [isHole,e] at hq
      | none => simpa [expand,e,yes] using congrFun ok q
    simp [ok,good,weight]
  · obtain ⟨q,hq⟩ := Function.ne_iff.mp ok
    have hole : isHole N A q = true ∧ g q = true := by
      cases e : A.get q with
      | some x => simp [expand,e,Function.comp_apply,A.put_get q x e] at hq
      | none => simpa [expand,isHole,e] using hq
    have zero : (∏ t : Fin H, if isHole N A t = true ∧ g t = true then (0:F) else 1) = 0 :=
      Finset.prod_eq_zero (f:=fun t => if isHole N A t = true ∧ g t = true then (0:F) else 1)
        (Finset.mem_univ q) (ite_eq_left hole)
    rw [zero,mul_zero,ite_eq_right ok]

theorem eval (pin : Fin p → Bool) : (network N A).eval pin = N.eval pin := by
  classical
  change (∑ g : Fin H → Bool, (network N A).weight pin g) = ∑ v, N.weight pin v
  simp only [weight_eq]
  have support : ∀ g, expand N A (g ∘ A.put) = g ↔ g ∈ Set.range (expand N A) := fun g => by
    constructor
    · intro h; exact ⟨_,h⟩
    · rintro ⟨v,rfl⟩
      congr 1
      funext i
      exact expand_put N A v i
  rw [← Fintype.sum_subtype_add_sum_subtype (fun g => g ∈ Set.range (expand N A))]
  have zero : (∑ g : {g // g ∉ Set.range (expand N A)},
      if expand N A (g.val ∘ A.put) = g.val then N.weight pin (g.val ∘ A.put) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro g _
    exact ite_eq_right (fun h => g.property ((support _).1 h))
  rw [zero,add_zero]
  let E := Equiv.ofInjective (expand N A) (expand_injective N A)
  apply Fintype.sum_equiv E.symm
  intro g
  obtain ⟨v,hv⟩ := E.surjective g
  subst g
  rw [ite_eq_left ((support _).2 (E v).property),Equiv.symm_apply_apply]
  apply congrArg (N.weight pin)
  funext i
  exact expand_put N A v i

end ThreeFlat.BitNetwork.Rectangular

end OAI
