import OAI.Computability.BorderVNP.PackedBottomBankWitness

/-! # Physical reading criteria for the forced part of a padded private slab -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

/-- The actual equalities on a copy's five address intervals. All the bit
addresses are relative to the start of that copy. -/
def Slab.Checks (s : Slab) (read : ℕ → Bool) (u : Fin s.supplied → Bool)
    (x : Fin s.incoming → Bool) (use : Fin s.used → Bool) : Prop :=
  (∀ k : Fin s.supplied, read (s.guessed+k.val) = u k) ∧
  (∀ k < s.capFine-(s.guessed+s.supplied), read (s.guessed+s.supplied+k) = false) ∧
  (∀ k : Fin s.incoming, read (s.capFine+k.val) = x k) ∧
  (∀ k : Fin s.used, read (s.orig+k.val) = use k) ∧
  ∀ k < s.capReport-s.used, read (s.orig+s.used+k) = false

/-- Physical prefix, input and padding checks are equivalent to the typed lane
condition of the complete work-bank bijection, including empty ranges. -/
theorem Slab.checks_iff (s : Slab) (read : ℕ → Bool) (u x use) :
    s.Checks read u x use ↔ s.Lanes u x use (fun k => read k.val) := by
  have hf := s.fineFits
  have hr := s.reportFits
  have he : s.stride = s.orig+s.capReport := rfl
  have ho : s.orig = s.capFine+s.incoming := rfl
  constructor
  · rintro ⟨hu,hz,hx,hm,hp⟩
    refine ⟨fun k j hk => (congrArg read hk).trans (hu j),?_,fun k j hk => (congrArg read hk).trans (hx j),fun k j hk => (congrArg read hk).trans (hm j),?_⟩
    · intro k h1 h2
      have hz' := hz (k.val-(s.guessed+s.supplied)) (by omega)
      simpa only [Nat.add_sub_of_le h1] using hz'
    · intro k h1
      have hk := k.isLt
      have hp' := hp (k.val-(s.orig+s.used)) (by omega)
      simpa only [Nat.add_sub_of_le h1] using hp'
  · rintro ⟨hu,hz,hx,hm,hp⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro j
      exact hu ⟨s.guessed+j.val,by have := j.isLt; omega⟩ j rfl
    · intro k hk
      exact hz ⟨s.guessed+s.supplied+k,by omega⟩ (by dsimp only; omega) (by dsimp only; omega)
    · intro j
      exact hx ⟨s.capFine+j.val,by have := j.isLt; omega⟩ j rfl
    · intro j
      exact hm ⟨s.orig+j.val,by have := j.isLt; omega⟩ j rfl
    · intro k hk
      exact hp ⟨s.orig+s.used+k,by omega⟩ (by dsimp only; omega)

/-- The genuine initial wire guesses biject with work assignments passing all
physical address constraints. Each represented copy still has independent wires. -/
noncomputable def Slab.checkedGuessEquiv (s : Slab) (b : ℕ) (u : Fin b → Fin s.supplied → Bool)
    (x : Fin b → Fin s.incoming → Bool) (use : Fin b → Fin s.used → Bool) :
    (Fin b → Fin s.guessed → Bool) ≃
      {bank : Fin (b*s.stride) → Bool // ∀ c : Fin b, s.Checks
        (fun j => if h : j < s.stride then bank (finProdFinEquiv (c,⟨j,h⟩)) else false) (u c) (x c) (use c)} :=
  (s.bundleGuessEquiv b u x use).trans (Equiv.subtypeEquivRight (fun bank => by
    apply forall_congr'
    intro c
    rw [s.checks_iff]
    simp only [Fin.is_lt,dite_true,Fin.eta]))

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
