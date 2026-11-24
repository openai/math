import OAI.Computability.VPVNP.SlotOtherEnd

/-!
# Old positions at each packed site

In either layout of §7.2 each new site receives exactly `K = 2^c d` old
positions. Half are thick and stay at their site. For thin positions the tag
offset and the chosen side of the bundle permute the ports. Each of the new
site's ports therefore receives the thin half of one old color-word fiber.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

variable {V H Tag L : Type*} {d c : ℕ}
variable (P : PackingData V H Tag L d c)

/-- Recover the old site and slot from a routed port. The only free field
at that port is the bit word with its prescribed old color bit. -/
private def positionBitFiber
    (e : Site V Tag L × H ≃ Site V Tag L × Fin d) (s : Site V Tag L) (b : ZMod 2) :
    {x : Position V H Tag L c // x.2.1 (P.color x.1.1) = b ∧ (e (x.1,x.2.2)).1 = s} ≃
      Σ i : Fin d, {w : BitWord c // w (P.color (e.symm (s,i)).1.1) = b} := by
  have recover (p : Site V Tag L × H) (hp : (e p).1 = s) : e.symm (s,(e p).2) = p := by
    rw [← hp]
    exact e.symm_apply_apply p
  exact {
    toFun := fun x ↦ ⟨(e (x.1.1,x.1.2.2)).2, x.1.2.1, by
      rw [recover _ x.2.2]; exact x.2.1⟩
    invFun := fun z ↦ ⟨((e.symm (s,z.1)).1,z.2.1,(e.symm (s,z.1)).2), z.2.2, by simp⟩
    left_inv := fun x ↦ Subtype.ext (by simp [recover _ x.2.2])
    right_inv := fun z ↦ by
      obtain ⟨i,w,hw⟩ := z
      apply Sigma.ext
      · simp
      · exact (Subtype.heq_iff_coe_eq (by simp)).mpr rfl }

variable [Fintype V] [Fintype Tag] [Fintype L] [Fintype H]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

private theorem card_positionBitFiber
    (e : Site V Tag L × H ≃ Site V Tag L × Fin d) (s : Site V Tag L) (b : ZMod 2) :
    Fintype.card {x : Position V H Tag L c //
      x.2.1 (P.color x.1.1) = b ∧ (e (x.1,x.2.2)).1 = s} = d * 2 ^ (c - 1) := by
  rw [Fintype.card_congr (P.positionBitFiber e s b), Fintype.card_sigma]
  simp [SlotPacking.card_oneBit]

variable [AddCommGroup Tag] [AddCommGroup L]

/-- Every new position has exactly `K` immediate old positions in its history,
for either common layout. -/
theorem card_placement (hc : 0 < c) (layout : Bool) (s : Site V Tag L) :
    Fintype.card {x : Position V H Tag L c // P.placement layout x = s} = 2 ^ c * d := by
  let keep := (Equiv.refl (Site V Tag L)).prodCongr P.slotLabel
  let route := (P.offsetSite.prodCongr P.slotLabel).trans (P.layoutPorts layout)
  let kept := fun x : Position V H Tag L c ↦ x.2.1 (P.color x.1.1) = 1 ∧ (keep (x.1,x.2.2)).1 = s
  let moved := fun x : Position V H Tag L c ↦ x.2.1 (P.color x.1.1) = 0 ∧ (route (x.1,x.2.2)).1 = s
  have hcases (x : Position V H Tag L c) : P.placement layout x = s ↔ kept x ∨ moved x := by
    have hbit : x.2.1 (P.color x.1.1) = 0 ∨ x.2.1 (P.color x.1.1) = 1 :=
      (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) _
    rcases hbit with h | h <;> cases layout <;>
      simp [placement, thick, keep, kept, moved, route, layoutPorts, assignedBundle, h]
  have hdisj : Disjoint kept moved := fun _ h₁ h₂ x hx ↦ by
    exact one_ne_zero ((h₁ x hx).1.symm.trans (h₂ x hx).1)
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hcases),
    Fintype.card_subtype_or_disjoint kept moved hdisj,
    P.card_positionBitFiber keep s 1, P.card_positionBitFiber route s 0]
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hc)
  simp only [Nat.succ_sub_one, pow_succ]
  ring

end Compression.PackingData

end VPVNP
end Computability
end OAI
