import OAI.Hierarchy.GridDyadicScale

namespace OAI
/-! # Cofinal machine-width matching and simultaneous selections -/

namespace Hierarchy.GridNativeShape
open Filter
open scoped Classical

/-- Cofinal widths on which the original physical key compiler and the
64-word-width convention use exactly the same machine word. -/
theorem physical_ages : ∃ᶠ w : ℕ in atTop, ∃ t : ℕ,5120≤t ∧ 64*w=16*t^10 ∧ Even w := by
  apply frequently_atTop.2
  intro N
  let z:=N+5120
  have lo : N≤z^10 := (show N≤z by dsimp [z];omega).trans (Nat.le_self_pow (by decide) z)
  exact ⟨256*z^10,by omega,2*z,by dsimp [z];omega,by rw [Nat.mul_pow];ring,128*z^10,by ring⟩

/-- Turns an eventual native construction on the physical subsequence into
a frequent assertion at the original volume parameter. -/
theorem at_physical_ages {P : ℕ→Prop}
    (exec : ∀ᶠ w : ℕ in atTop, ∀ t : ℕ,5120≤t→64*w=16*t^10→Even w→P w) :
    ∃ᶠ w : ℕ in atTop,P w := (physical_ages.and_eventually exec).mono fun _ h=>by
  obtain ⟨⟨t,age,word,even⟩,run⟩:=h
  exact run t age word even

/-- The compiler may choose the copy count from the exposed approximation at
each age. Proving distribution eventually along every such choice gives the
simultaneous `∀ v` at cofinally many ages required in the finite-field proof. -/
theorem frequent_all {α : ℕ→Type*} (P : ∀ n,α n→Prop)
    (choose : ∀ x : ∀ n,Option (α n), (∀ᶠ n : ℕ in atTop,(x n).isSome) →
      ∃ᶠ n : ℕ in atTop, ∀ y,x n=some y→P n y) :
    ∃ᶠ n : ℕ in atTop,∀ y,P n y := by
  classical
  by_contra fail
  have no : ∀ᶠ n : ℕ in atTop,∃ y,¬P n y :=
    (Filter.not_frequently.mp fail).mono fun _ h=>Classical.not_forall.mp h
  let x : ∀ n,Option (α n) := fun n=>if h : ∃ y,¬P n y then some h.choose else none
  have live : ∀ᶠ n : ℕ in atTop,(x n).isSome := no.mono fun n h=>by simp [x,h]
  obtain ⟨n,bad,good⟩ := ((choose x live).and_eventually no).exists
  exact good.choose_spec (bad good.choose (by simp [x,good]))

end Hierarchy.GridNativeShape

end OAI
