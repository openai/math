import OAI.Geometry.Hirsch.Tags

noncomputable section

namespace OAI.Geometry.Hirsch.Layer

def PaletteTheorem : Prop :=
  ∀ m : ℕ, 0 < m → ∀ threshold : ℕ, ∃ b D : ℕ, 2 ≤ b ∧ threshold ≤ b ∧
    ∀ k, 0 < k → Nonempty ((World.free (b^m*(k+2))).Emissions (Fin b) D)

theorem numerical_of_palette (input : PaletteTheorem) : NumericalLayers := by
  intro rate
  let r := 3*rate
  let X := Player (2^r)
  obtain ⟨b,D,hb,ht,hs⟩ := input (r+1) (by omega) (2*Fintype.card X*factor X r)
  let V := Fintype.card (Labels (Fin b) X r b)
  have he : V = b * (Fintype.card X * (factor X r * b)) := by simp [V]
  have hv : 0 < V := by
    have hi : 0 < Fintype.card X := Fintype.card_pos
    rw [he]
    unfold factor
    positivity
  have hh : 2*V ≤ b^3 := by
    calc
      _ = (2*Fintype.card X*factor X r)*b^2 := by rw [he]; ring
      _ ≤ b*b^2 := Nat.mul_le_mul_right _ ht
      _ = _ := by ring
  have hr : (2*V)^rate ≤ b^(r+1) := by
    apply (Nat.pow_le_pow_left hh rate).trans
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (Nat.le_succ _)
  let code := tagCode (Fin b) (arena (2^r)) (show b^(r+1) ≤ b^(r+1) from le_rfl)
  refine ⟨b^(r+1),V,(2*(D+1)+1)^V,hb.trans (Nat.le_self_pow (by omega) _),hv,hr,code,fun k hk => ?_⟩
  obtain ⟨p⟩ := hs k hk
  exact Bundles.sequence (tag_separates _ _) p (World.full_free _)

end OAI.Geometry.Hirsch.Layer
