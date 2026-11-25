import OAI.Hierarchy.TaggedGuard
import OAI.ThreeFlat.Routing.TypedWiring

namespace OAI
/-! # Guarding a row check with an already exposed record flag -/

namespace Hierarchy.Tagged.Guard
open ThreeFlat Routing
open scoped Classical
noncomputable section

private def phase {F : Type*} [Zero F] [One F] {p : ℕ} (active : Bool) (N : BitNetwork F p) :=
  if active then network N else flip (network N) 0

def onPin {F P : Type*} [Fintype P] [Zero F] [One F] (pin : P) (active : Bool)
    (N : BitNetwork F (Fintype.card P)) : BitNetwork F (Fintype.card P) :=
  rename (phase active N) (Fin.cases (.inl (Fintype.equivFin _ pin)) Sum.inl)

theorem onPin_eval {F P : Type*} [Fintype P] [CommSemiring F] (pin : P) (active : Bool)
    (N : BitNetwork F (Fintype.card P)) (x : P → Bool) :
    TypedWiring.value (onPin pin active N) x = if x pin = active then TypedWiring.value N x else 1 := by
  let b := x ∘ (Fintype.equivFin _).symm
  change (onPin pin active N).eval b = if x pin = active then N.eval b else 1
  rw [onPin, rename_value]
  have port : Sum.elim b id ∘ Fin.cases (Sum.inl (Fintype.equivFin _ pin)) Sum.inl = Fin.cases (x pin) b := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [b]
  rw [port]
  cases active
  · simp only [phase, Bool.false_eq_true, ite_false, flip_eval]
    have neg : (fun i => if i = 0 then !(Fin.cases (x pin) b i) else Fin.cases (x pin) b i) =
      Fin.cases (!(x pin)) b := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [neg, value]
    cases x pin <;> rfl
  · simp only [phase, ite_true, value]

theorem onPin_size {F P : Type*} [Fintype P] [Zero F] [One F] (pin : P) (active : Bool)
    (N : BitNetwork F (Fintype.card P)) :
    (onPin pin active N).cells+(onPin pin active N).internal ≤ 177*(N.cells+N.internal) := by
  have h := size N
  cases active <;> simp only [onPin, phase, rename, flip, Bool.false_eq_true, ite_false, ite_true] <;> omega

end
end Hierarchy.Tagged.Guard

end OAI
