import OAI.ThreeFlat.Diagonal.CompressorIncidences

namespace OAI
/-! # Uniform number of thin-wire demands assigned to each bundle -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression
open scoped Classical BigOperators

variable {c d : ℕ} {V H Tag L : Type*}

private theorem not_one_iff_zero (x : ZMod 2) : x ≠ 1 ↔ x = 0 :=
  (by decide : ∀ y : Fin 2, y ≠ 1 ↔ y = 0) x

/-- Erasing the single prescribed color leaves all remaining bits free. -/
def eraseColor (i : Fin c) (a : ZMod 2) : {w : BitWord c // w i = a} ≃
    ({t : Fin c // t ≠ i} → ZMod 2) where
  toFun w t := w.val t.val
  invFun f := ⟨fun t => if h : t = i then a else f ⟨t,h⟩, by simp⟩
  left_inv w := by
    apply Subtype.ext
    funext t
    by_cases hi : t = i
    · subst t
      simpa using w.property.symm
    · simp [hi]
  right_inv f := by funext t; simp [t.property]

theorem one_bit_count (i : Fin c) (a : ZMod 2) :
    Fintype.card {w : BitWord c // w i = a} = 2 ^ (c - 1) := by
  rw [Fintype.card_congr (eraseColor i a), Fintype.card_fun, ZMod.card,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]

variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

omit [AddCommGroup H] [AddCommGroup L] in
theorem outgoing_count (p : Site V Tag L × Fin d) (i : Fin d) :
    Fintype.card {w : BitWord c // ¬P.thick (sourcePosition (center P p i w))} =
      2 ^ (c - 1) := by
  let e : {w : BitWord c // ¬P.thick (sourcePosition (center P p i w))} ≃
      {w : BitWord c // w (P.color p.1.1) = 0} :=
    Equiv.subtypeEquivRight (fun w => not_one_iff_zero _)
  exact (Fintype.card_congr e).trans (one_bit_count _ _)

theorem incoming_count (p : Site V Tag L × Fin d) (i : Fin d) :
    Fintype.card {w : BitWord c // ¬P.thick (sourcePosition (center P p i w)) ∧
      P.thick (sourcePosition (P.actual.symm (center P p i w)))} = 2 ^ (c - 2) := by
  let src := P.slots.target.symm (p.1.1,i)
  have proper : P.color p.1.1 ≠ P.color src.1 := by
    simpa only [src, Equiv.apply_symm_apply] using (P.proper src).symm
  let bit := P.bitShift src (P.color src.1)
  let e : {w : BitWord c // ¬P.thick (sourcePosition (center P p i w)) ∧
        P.thick (sourcePosition (P.actual.symm (center P p i w)))} ≃
      {w : BitWord c // w (P.color p.1.1) = 0 ∧ w (P.color src.1) = 1 + bit} :=
    Equiv.subtypeEquivRight fun w => by
      change (w (P.color p.1.1) ≠ 1 ∧ w (P.color src.1) - bit = 1) ↔ _
      rw [not_one_iff_zero, sub_eq_iff_eq_add]
  exact (Fintype.card_congr e).trans (fixed_bit_count _ _ proper _ _)

section
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]

/-- The demand motifs in every bundle consist of `d` half-size outgoing
fibers and `d` quarter-size incoming fibers. -/
theorem bundle_count (p : Site V Tag L × Fin d) :
    Fintype.card {m : P.Motif // P.bundle m = p} = d * 2 ^ (c - 1) + d * 2 ^ (c - 2) := by
  rw [Fintype.card_congr (bundleFiberEquiv P p)]
  change Fintype.card (_ ⊕ _) = _
  simp only [Fintype.card_sum, Fintype.card_sigma, outgoing_count, incoming_count,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- In the compressor's prescribed number of colors, this equals three
quarters of the initial number of color-word and slot-label pairs. -/
theorem bundle_three_quarters (p : Site V Tag L × Fin d) (hc : 2 ≤ c) :
    Fintype.card {m : P.Motif // P.bundle m = p} = 3 * (2 ^ c * d) / 4 := by
  have e₁ : c - 1 = (c - 2) + 1 := by omega
  have e₂ : c = (c - 2) + 2 := by omega
  rw [bundle_count, e₁, Nat.pow_succ]
  conv_rhs => rw [e₂, Nat.pow_add]
  set n := 2 ^ (c - 2)
  have h : 3 * (n * 2 ^ 2 * d) = (d * (n * 2) + d * n) * 4 := by ring
  rw [h]
  omega

/-- For either numbering of the bundle endpoints, exactly `d` bundles
have a prescribed site. -/
theorem endpoint_site_count {S : Type*} [Fintype S]
    (t : Equiv.Perm (S × Fin d)) (s : S) :
    Fintype.card {p : S × Fin d // (t p).1 = s} = d := by
  let e : {p : S × Fin d // p.1 = s} ≃ Fin d := {
    toFun p := p.val.2
    invFun i := ⟨(s,i),rfl⟩
    left_inv := fun p => Subtype.ext (Prod.ext p.property.symm rfl)
    right_inv := fun _ => rfl }
  let u := t.subtypeEquiv (p := fun p => (t p).1 = s) (q := fun p => p.1 = s)
    (fun _ => Iff.rfl)
  exact (Fintype.card_congr (u.trans e)).trans (Fintype.card_fin d)

theorem role_count (t : Equiv.Perm (Site V Tag L × Fin d)) (s : Site V Tag L) (hc : 2 ≤ c) :
    Fintype.card {m : P.Motif // (t (P.bundle m)).1 = s} = d * (3 * (2 ^ c * d) / 4) := by
  let e := Equiv.sigmaSubtypeFiberEquivSubtype P.bundle
    (q := fun p => (t p).1 = s) (p := fun m => (t (P.bundle m)).1 = s)
    (fun _ => Iff.rfl)
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  simp only [bundle_three_quarters P _ hc, Finset.sum_const, Finset.card_univ,
    smul_eq_mul]
  apply congrArg (fun z : ℕ => z * (3*(2^c*d)/4))
  convert endpoint_site_count t s using 1; congr 1; apply Subsingleton.elim

theorem roleA_count (s : Site V Tag L) (hc : 2 ≤ c) :
    Fintype.card {m : P.Motif // P.roleA m = s} = d * (3 * (2 ^ c * d) / 4) :=
  role_count P (Equiv.refl _) s hc

theorem roleB_count (s : Site V Tag L) (hc : 2 ≤ c) :
    Fintype.card {m : P.Motif // P.roleB m = s} = d * (3 * (2 ^ c * d) / 4) :=
  role_count P P.siteGraph.target s hc

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
