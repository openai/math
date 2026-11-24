import OAI.Computability.VPVNP.SlotBundleCount

/-!
# Placements of the D endpoint

At any site in either layout, D can arise at the thick end of a mixed wire
in either direction, or at the destination of an old thin–thin wire. Each
of these three cases contributes `d*K/4` incidences. In the last case the
bundle used to place D is its own bundle, which can differ from C's.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

variable {V H Tag L : Type*} {d c : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- Send a thin endpoint's assigned bundle to its chosen side, retaining
that side's local slot number. -/
def layoutPorts (layout : Bool) : Equiv.Perm (Site V Tag L × Fin d) :=
  if layout then P.siteGraph.target else Equiv.refl _

private abbrev srcThick (a : Arc V H Tag L d c) := P.thick (sourcePosition a)

omit [AddCommGroup H] in
private theorem place_thin (l : Bool) (a : Arc V H Tag L d c) (h : ¬ P.srcThick a) :
    P.placement l (sourcePosition a) =
      (P.layoutPorts l (P.assignedBundle (sourcePosition a))).1 := by
  cases l <;> simp [placement, layoutPorts, srcThick] at h ⊢ <;> simp [h]

private theorem place_source (l : Bool) (m : P.Motif) (h : P.srcThick m.val) :
    P.roleD l m = m.val.1.1 := by
  unfold roleD D
  rw [ite_eq_left h]
  unfold placement
  rw [ite_eq_left h]
  rfl

private theorem place_target (l : Bool) (m : P.Motif) (hs : ¬ P.srcThick m.val)
    (ht : P.srcThick (P.actual m.val)) : P.roleD l m = (P.actual m.val).1.1 := by
  unfold roleD D
  rw [ite_eq_right hs]
  unfold placement
  rw [ite_eq_left ht]
  rfl

private def dCases (l : Bool) (s : Site V Tag L) :
    {m : P.Motif // P.roleD l m = s} ≃
      {a : Arc V H Tag L d c // (P.srcThick a ∧ ¬ P.srcThick (P.actual a)) ∧ a.1.1 = s} ⊕
      {a : Arc V H Tag L d c // (¬ P.srcThick a ∧ P.srcThick (P.actual a)) ∧
        (P.actual a).1.1 = s} ⊕
      {a : Arc V H Tag L d c // (¬ P.srcThick a ∧ ¬ P.srcThick (P.actual a)) ∧
        (P.layoutPorts l (P.assignedBundle (sourcePosition (P.actual a)))).1 = s} where
  toFun m :=
    if hs : P.srcThick m.1.1 then .inl ⟨m.1.1, ⟨hs, fun ht ↦ m.1.2 ⟨hs,ht⟩⟩,
      (P.place_source l m.1 hs).symm.trans m.2⟩
    else if ht : P.srcThick (P.actual m.1.1) then .inr (.inl ⟨m.1.1, ⟨hs, ht⟩,
      (P.place_target l m.1 hs ht).symm.trans m.2⟩)
    else .inr (.inr ⟨m.1.1, ⟨hs, ht⟩, by
      simpa [roleD, D, hs, P.place_thin l _ ht] using m.2⟩)
  invFun
    | .inl a =>
      let m : P.Motif := ⟨a.1, fun h ↦ a.2.1.2 h.2⟩
      ⟨m, (P.place_source l m a.2.1.1).trans a.2.2⟩
    | .inr (.inl a) =>
      let m : P.Motif := ⟨a.1, fun h ↦ a.2.1.1 h.1⟩
      ⟨m, (P.place_target l m a.2.1.1 a.2.1.2).trans a.2.2⟩
    | .inr (.inr a) => ⟨⟨a.1, fun h ↦ a.2.1.1 h.1⟩, by
        simpa [roleD, D, a.2.1.1, P.place_thin l _ a.2.1.2] using a.2.2⟩
  left_inv m := by
    by_cases hs : P.srcThick m.1.1 <;> by_cases ht : P.srcThick (P.actual m.1.1) <;> simp [hs, ht]
  right_inv a := by
    rcases a with a | (a | a) <;> simp [a.2.1.1, a.2.1.2]

private def bySlot {A S : Type*} (port : A → S × Fin d) (p : A → Prop) (s : S) :
    {a : A // p a ∧ (port a).1 = s} ≃ Σ i : Fin d, {a : A // p a ∧ port a = (s,i)} where
  toFun a := ⟨(port a.1).2, a.1, a.2.1, Prod.ext a.2.2 rfl⟩
  invFun z := ⟨z.2.1, z.2.2.1, congrArg Prod.fst z.2.2.2⟩
  left_inv _ := rfl
  right_inv z := by
    obtain ⟨i, a, ha, he⟩ := z
    have hi : (port a).2 = i := congrArg Prod.snd he
    subst i
    rfl

private theorem count_bySlot {A S : Type*} [Fintype A] (port : A → S × Fin d) (p : A → Prop)
    [DecidablePred p] [DecidableEq S]
    (s : S) (k : ℕ) (h : ∀ b, Fintype.card {a : A // p a ∧ port a = b} = k) :
    Fintype.card {a : A // p a ∧ (port a).1 = s} = d * k := by
  rw [Fintype.card_congr (bySlot port p s), Fintype.card_sigma]
  simp [h]

private theorem bit_ne_one (v : ZMod 2) : v ≠ 1 ↔ v = 0 :=
  (by decide : ∀ v : ZMod 2, v ≠ 1 ↔ v = 0) v

variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable [Fintype V] [Fintype Tag] [Fintype H] [Fintype L]

private theorem count_mixedOut (hc : 2 ≤ c) (b : Site V Tag L × Fin d) :
    Fintype.card {a : Arc V H Tag L d c // (P.srcThick a ∧ ¬ P.srcThick (P.actual a)) ∧
      a.1 = b} = 2 ^ c * d / 4 := by
  have e := Equiv.subtypeEquivRight (p := fun a : Arc V H Tag L d c ↦
      (P.srcThick a ∧ ¬ P.srcThick (P.actual a)) ∧ a.1 = b)
    (q := fun a ↦ a.1 = b ∧ P.arcBit a = 1 ∧ P.arcBit (P.actual a) = 0)
    (fun a ↦ by change (_ ∧ P.arcBit (P.actual a) ≠ 1) ∧ _ ↔ _; rw [bit_ne_one]; tauto)
  exact (Fintype.card_congr e).trans (P.card_bundle_types hc b 1 0)

private theorem count_mixedIn (hc : 2 ≤ c) (b : Site V Tag L × Fin d) :
    Fintype.card {a : Arc V H Tag L d c // (¬ P.srcThick a ∧ P.srcThick (P.actual a)) ∧
      (P.actual a).1 = b} = 2 ^ c * d / 4 := by
  have e := Equiv.subtypeEquivRight (p := fun a : Arc V H Tag L d c ↦
      (¬ P.srcThick a ∧ P.srcThick (P.actual a)) ∧ (P.actual a).1 = b)
    (q := fun a ↦ a.1 = P.siteGraph.target.symm b ∧ P.arcBit a = 0 ∧ P.arcBit (P.actual a) = 1)
    (fun a ↦ by
      change (P.arcBit a ≠ 1 ∧ _) ∧ P.siteGraph.target a.1 = b ↔ _
      rw [bit_ne_one, ← Equiv.eq_symm_apply]
      tauto)
  exact (Fintype.card_congr e).trans (P.card_bundle_types hc _ 0 1)

private theorem count_thinIn (l : Bool) (b : Site V Tag L × Fin d) :
    Fintype.card {a : Arc V H Tag L d c // (¬ P.srcThick a ∧ ¬ P.srcThick (P.actual a)) ∧
      P.layoutPorts l (P.assignedBundle (sourcePosition (P.actual a))) = b} =
      d * 2 ^ (c - 2) := by
  let b' := (P.layoutPorts l).symm b
  let p := fun a : Arc V H Tag L d c ↦ ¬ P.srcThick (P.actual.symm a) ∧ ¬ P.srcThick a
  have e := P.actual.subtypeEquiv (p := fun a ↦ (¬ P.srcThick a ∧ ¬ P.srcThick (P.actual a)) ∧
      P.layoutPorts l (P.assignedBundle (sourcePosition (P.actual a))) = b)
    (q := fun a ↦ p a ∧ P.assignedBundle (sourcePosition a) = b') (fun a ↦ by
      simp only [p, b', Equiv.symm_apply_apply, ← Equiv.eq_symm_apply])
  rw [Fintype.card_congr (e.trans (P.assignedArcEquiv b' p)), Fintype.card_sigma]
  have count (i : Fin d) : Fintype.card {w : BitWord c // p (P.arcAtBundle b' i w)} =
      2 ^ (c - 2) := by
    let old := P.slots.target.symm (b'.1.1, i)
    have hne : P.color old.1 ≠ P.color b'.1.1 := by simpa [old] using P.proper old
    change Fintype.card {w : BitWord c //
      w (P.color old.1) - P.bitShift old (P.color old.1) ≠ 1 ∧ w (P.color b'.1.1) ≠ 1} = _
    simpa only [sub_eq_add_neg, add_zero, bit_ne_one, Fintype.card_fin] using
      SlotPacking.card_translatedBits hne (-P.bitShift old (P.color old.1)) 0 0 0
  simp [count]

/-- Both layouts give exactly `dQ` occurrences of D at every new position. -/
theorem card_roleD (hc : 2 ≤ c) (l : Bool) (s : Site V Tag L) :
    Fintype.card {m : P.Motif // P.roleD l m = s} = d * (3 * (2 ^ c * d) / 4) := by
  rw [Fintype.card_congr (P.dCases l s), Fintype.card_sum, Fintype.card_sum]
  rw [count_bySlot (fun a : Arc V H Tag L d c ↦ a.1)
        (fun a ↦ P.srcThick a ∧ ¬ P.srcThick (P.actual a)) s _ (P.count_mixedOut hc),
      count_bySlot (fun a : Arc V H Tag L d c ↦ (P.actual a).1)
        (fun a ↦ ¬ P.srcThick a ∧ P.srcThick (P.actual a)) s _ (P.count_mixedIn hc),
      count_bySlot (fun a ↦ P.layoutPorts l (P.assignedBundle (sourcePosition (P.actual a))))
        (fun a ↦ ¬ P.srcThick a ∧ ¬ P.srcThick (P.actual a)) s _ (P.count_thinIn l)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hc
  rw [pow_add, Nat.add_sub_cancel_left]
  have h : (2:ℕ) ^ 2 * 2 ^ k * d = 4 * (d * 2 ^ k) := by ring
  rw [h]
  have ht : 3 * (4 * (d * 2 ^ k)) / 4 = 3 * (d * 2 ^ k) := by omega
  rw [ht, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
  ring

end Compression.PackingData

end VPVNP
end Computability
end OAI
