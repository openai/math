import OAI.Computability.VPVNP.GrassmannCompletion
import OAI.Computability.VPVNP.GrassmannFrames
import OAI.Computability.VPVNP.GrassmannFrameValue
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Independence of the original columns and their completion

The equality case of Lemma 5.3 first makes an observable on two completed
block spans independent of the choice of completion. Moving an original column
then preserves the observable as well: a common completion containing the
difference of the two columns gives identical completed block spans.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open Set Function Relation GrassmannFrames

variable {K V Y : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem independent_append {n s : ℕ} {v : Fin n → V} {w : Fin s → V} :
    LinearIndependent K (Sum.elim v w) ↔ LinearIndependent K (Fin.append v w) :=
  linearIndependent_equiv' finSumFinEquiv Fin.append_comp_sumElim

private theorem completion_invariant {n s : ℕ} (hd : n + s < Module.finrank K V)
    (E : (Fin n → V) → (Fin s → V) → Y)
    (move : ∀ (v : Fin n → V) (w : Fin s → V) (i : Fin s) (x : V),
      LinearIndependent K (Sum.elim v (Fin.snoc w x)) → E v w = E v (update w i x))
    (v : Fin n → V) (w w' : Fin s → V)
    (h : LinearIndependent K (Sum.elim v w)) (h' : LinearIndependent K (Sum.elim v w')) :
    E v w = E v w' := by
  let observable (p : Fin (n + s) → V) := E (p ∘ Fin.castAdd s) (p ∘ Fin.natAdd n)
  have eval (a : Fin n → V) (b : Fin s → V) : observable (Fin.append a b) = E a b := by
    simp [observable, Function.comp_def]
  rw [← eval v w, ← eval v w']
  apply GrassmannFrames.invariant (f := observable) _ hd
    (independent_append.mp h) (independent_append.mp h')
  · intro i hi
    cases i using Fin.addCases with
    | left i => simp
    | right i => simp at hi
  · intro p q step
    obtain ⟨j, x, hj, hx, rfl⟩ := step
    cases j using Fin.addCases with
    | left j => exact (Nat.not_le_of_lt j.isLt hj).elim
    | right j =>
      let a := p ∘ Fin.castAdd s
      let b := p ∘ Fin.natAdd n
      have hab : Fin.append a b = p := Fin.append_castAdd_natAdd
      have hind : LinearIndependent K (Sum.elim a (Fin.snoc b x)) := by
        rw [independent_append, Fin.append_snoc, hab]
        exact hx
      have heq : update p (Fin.natAdd n j) x = Fin.append a (update b j x) := by
        funext i
        cases i using Fin.addCases with
        | left i =>
          have hne : Fin.castAdd s i ≠ Fin.natAdd n j := by
            intro h
            have := congrArg Fin.val h
            simp only [Fin.val_castAdd, Fin.val_natAdd] at this
            omega
          simp [a, hne]
        | right i =>
          by_cases hji : i = j
          · subst i
            simp
          · have hne : Fin.natAdd n i ≠ Fin.natAdd n j := by simpa using hji
            simp [b, hne, hji]
      rw [heq, eval]
      exact move a b j x hind

/-- If replacing a completion column outside the total span preserves the
observable, its value is the same on all pairs of completed blocks of the
given sizes. This holds over every field, including the binary one. -/
theorem completed_blocks_rigid [FiniteDimensional K V] {n s : ℕ} (hs : 0 < s)
    (hd : n + s < Module.finrank K V) (A B : Set (Fin n))
    (D : Submodule K V → Submodule K V → Y)
    (move : ∀ (v : Fin n → V) (w : Fin s → V) (i : Fin s) (x : V),
      LinearIndependent K (Sum.elim v (Fin.snoc w x)) →
        D (completedBlock v w A) (completedBlock v w B) =
        D (completedBlock v (update w i x) A) (completedBlock v (update w i x) B))
    {v v' : Fin n → V} {w w' : Fin s → V}
    (h : LinearIndependent K (Sum.elim v w)) (h' : LinearIndependent K (Sum.elim v' w')) :
    D (completedBlock v w A) (completedBlock v w B) =
    D (completedBlock v' w' A) (completedBlock v' w' B) := by
  let E (u : Fin n → V) (t : Fin s → V) := D (completedBlock u t A) (completedBlock u t B)
  have same := completion_invariant hd E move
  have chain {u u' : Fin n → V} (path : ReflTransGen (OutsideStep K 0) u u') :
      ∀ {t t' : Fin s → V}, LinearIndependent K (Sum.elim u t) →
        LinearIndependent K (Sum.elim u' t') → E u t = E u' t' := by
    induction path with
    | refl => exact fun {t t'} ht ht' => same u t t' ht ht'
    | @tail b c path step ih =>
      intro t t' ht ht'
      rcases step with ⟨i, z, _, hz, rfl⟩
      obtain ⟨u₁, _, hu₁, hu₂, span_eq⟩ :=
        adjacent_commonCompletion (linearIndependent_finSnoc.mp hz).1 i z
          (linearIndependent_finSnoc.mp hz).2 hs (by simpa using hd.le)
      have hval : E b u₁ = E (update b i z) u₁ := congrArg₂ D (span_eq A) (span_eq B)
      exact (ih ht hu₁).trans (hval.trans (same _ u₁ t' hu₂ ht'))
  apply chain (connected_of_prefix (k := 0) (Nat.zero_le n) (by omega)
    (h.comp Sum.inl Sum.inl_injective) (h'.comp Sum.inl Sum.inl_injective) (by simp))
  · exact h
  · exact h'

end Grassmann

end VPVNP
end Computability
end OAI
