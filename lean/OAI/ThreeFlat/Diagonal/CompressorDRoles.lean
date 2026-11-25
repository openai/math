import OAI.ThreeFlat.Diagonal.CompressorBundleCounts

namespace OAI
/-! # The three kinds of endpoint opposite the assigned thin end

A thick source opposite a thin destination stays at its packed site. A
thick destination opposite a thin source does as well. The destination
of a thin--thin edge uses its assigned bundle in the chosen layout.
-/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression
open scoped Classical BigOperators
variable {c d : ℕ} {V H Tag L : Type*}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- A thick source, a thick destination, or a thin destination. The latter
two use the incoming slot numbering of the old base. -/
abbrev DForm :=
  {x : Arc V H Tag L d c // P.thick (sourcePosition x) ∧
    ¬P.thick (sourcePosition (P.actual x))} ⊕
  {y : Arc V H Tag L d c // P.thick (sourcePosition y) ∧
    ¬P.thick (sourcePosition (P.actual.symm y))} ⊕
  {y : Arc V H Tag L d c // ¬P.thick (sourcePosition y) ∧
    ¬P.thick (sourcePosition (P.actual.symm y))}

def dEquiv : P.Motif ≃ DForm P where
  toFun m := if hs : P.thick (sourcePosition m.val) then
      .inl ⟨m.val, hs, fun ht => m.property ⟨hs,ht⟩⟩
    else if ht : P.thick (sourcePosition (P.actual m.val)) then
      .inr (.inl ⟨P.actual m.val, ht, by simpa using hs⟩)
    else .inr (.inr ⟨P.actual m.val, ht, by simpa using hs⟩)
  invFun
    | .inl x => ⟨x.val, fun both => x.property.2 both.2⟩
    | .inr (.inl y) => ⟨P.actual.symm y.val, fun both => y.property.2 both.1⟩
    | .inr (.inr y) => ⟨P.actual.symm y.val, fun both => y.property.2 both.1⟩
  left_inv m := by
    by_cases hs : P.thick (sourcePosition m.val)
    · simp [hs]
    · by_cases ht : P.thick (sourcePosition (P.actual m.val)) <;> simp [hs, ht]
  right_inv t := by
    rcases t with x | y | y
    · simp [x.property.1]
    · simp [y.property.2, y.property.1]
    · simp [y.property.2, y.property.1]

def placementPerm (layout : Bool) : Equiv.Perm (Site V Tag L × Fin d) :=
  if layout then P.siteGraph.target else Equiv.refl _

def dSite (layout : Bool) : DForm P → Site V Tag L
  | .inl x => x.val.1.1
  | .inr (.inl y) => y.val.1.1
  | .inr (.inr y) => (placementPerm P layout (P.assignedBundle (sourcePosition y.val))).1

theorem dSite_eq (layout : Bool) (m : P.Motif) :
    dSite P layout (dEquiv P m) = P.roleD layout m := by
  by_cases hs : P.thick (sourcePosition m.val)
  · simp [dSite, dEquiv, PackingData.roleD, PackingData.D, PackingData.placement, hs]
    rfl
  · by_cases ht : P.thick (sourcePosition (P.actual m.val))
    · simp [dSite, dEquiv, PackingData.roleD, PackingData.D, PackingData.placement, hs, ht]
      rfl
    · cases layout <;>
        simp [dSite, dEquiv, PackingData.roleD, PackingData.D, PackingData.placement, hs, ht, placementPerm]

/-- Restricting the new endpoint type to a given site preserves the actual
fiber of `PackingData.roleD`. -/
def dFiber (layout : Bool) (s : Site V Tag L) :
    {m : P.Motif // P.roleD layout m = s} ≃ {t : DForm P // dSite P layout t = s} :=
  (dEquiv P).subtypeEquiv fun m => by rw [dSite_eq]

private def siteFiber (test : Arc V H Tag L d c → Prop) (s : Site V Tag L) :
    {a : Subtype test // a.val.1.1 = s} ≃ Σ i : Fin d,
      {q : BitWord c × H // test ((s,i),q)} where
  toFun a := ⟨a.val.val.1.2, a.val.val.2, by
    obtain ⟨⟨⟨⟨t,i⟩,q⟩, h⟩, ht⟩ := a
    change t = s at ht
    subst t
    exact h⟩
  invFun u := ⟨⟨((s,u.1),u.2.val),u.2.property⟩,rfl⟩
  left_inv := by rintro ⟨⟨⟨⟨_,i⟩,q⟩,h⟩,rfl⟩; rfl
  right_inv := by rintro ⟨i,⟨q,h⟩⟩; rfl

private def assignedFiber (test : Arc V H Tag L d c → Prop) (p : Site V Tag L × Fin d) :
    {a : Subtype test // P.assignedBundle (sourcePosition a.val) = p} ≃
      Σ i : Fin d, {w : BitWord c // test (center P p i w)} where
  toFun a := ⟨a.val.val.1.2, a.val.val.2.1, (center_eq P a.val.val p a.property).symm ▸ a.val.property⟩
  invFun q := ⟨⟨center P p q.1 q.2.val,q.2.property⟩,assigned_center P p q.1 q.2.val⟩
  left_inv a := Subtype.ext (Subtype.ext (center_eq P a.val.val p a.property))
  right_inv := by rintro ⟨i,⟨q,h⟩⟩; rfl

private abbrev outgoingMixed (a : Arc V H Tag L d c) :=
  P.thick (sourcePosition a) ∧ ¬P.thick (sourcePosition (P.actual a))

private abbrev incomingMixed (a : Arc V H Tag L d c) :=
  P.thick (sourcePosition a) ∧ ¬P.thick (sourcePosition (P.actual.symm a))

private abbrev incomingThin (a : Arc V H Tag L d c) :=
  ¬P.thick (sourcePosition a) ∧ ¬P.thick (sourcePosition (P.actual.symm a))

private theorem not_one (x : ZMod 2) : x ≠ 1 ↔ x = 0 :=
  (by decide : ∀ t : Fin 2, t ≠ 1 ↔ t = 0) x

private def incomingWord (p : Site V Tag L × Fin d) (a : ZMod 2) :
    {w : BitWord c // w (P.color p.1.1) = a ∧
      (w - P.bitShift (P.slots.target.symm (p.1.1,p.2)))
          (P.color (P.slots.target.symm (p.1.1,p.2)).1) ≠ 1} ≃
    {w : BitWord c // w (P.color p.1.1) = a ∧
      w (P.color (P.slots.target.symm (p.1.1,p.2)).1) =
        P.bitShift (P.slots.target.symm (p.1.1,p.2)) (P.color (P.slots.target.symm (p.1.1,p.2)).1)} :=
  Equiv.subtypeEquivRight fun w => by rw [not_one]; simp only [Pi.sub_apply, sub_eq_zero]

omit [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] in
private theorem proper_inv (s : Site V Tag L) (i : Fin d) :
    P.color s.1 ≠ P.color (P.slots.target.symm (s.1,i)).1 := by
  simpa only [Equiv.apply_symm_apply] using (P.proper (P.slots.target.symm (s.1,i))).symm

variable [Fintype H]

private theorem outgoing_mixed_count (s : Site V Tag L) (i : Fin d) :
    Fintype.card {q : BitWord c × H // outgoingMixed P ((s,i),q)} = 2 ^ (c - 2) * d := by
  let e : {q : BitWord c × H // outgoingMixed P ((s,i),q)} ≃ endpointFiber P (s,i) 1 0 :=
    Equiv.subtypeEquivRight fun q => and_congr_right fun _ => not_one _
  exact (Fintype.card_congr e).trans (endpoint_count P (s,i) 1 0)

private theorem incoming_mixed_count (s : Site V Tag L) (i : Fin d) :
    Fintype.card {q : BitWord c × H // incomingMixed P ((s,i),q)} = 2 ^ (c - 2) * d := by
  let p := (s,i)
  let W := {w : BitWord c // w (P.color s.1) = 1 ∧
      (w - P.bitShift (P.slots.target.symm (s.1,i))) (P.color (P.slots.target.symm (s.1,i)).1) ≠ 1}
  let e : {q : BitWord c × H // incomingMixed P ((s,i),q)} ≃ W × H := {
    toFun q := (⟨q.val.1,q.property⟩,q.val.2)
    invFun q := ⟨(q.1.val,q.2),q.1.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_congr (incomingWord P (s,i) 1),
    fixed_bit_count _ _ (proper_inv P s i), Fintype.card_congr P.slotLabel, Fintype.card_fin]

omit [Fintype H] in
private theorem incoming_thin_count (p : Site V Tag L × Fin d) (i : Fin d) :
    Fintype.card {w : BitWord c // incomingThin P (center P p i w)} = 2 ^ (c - 2) := by
  let s := P.offsetSite.symm p.1
  let W := {w : BitWord c // w (P.color s.1) = 0 ∧
      (w - P.bitShift (P.slots.target.symm (s.1,i))) (P.color (P.slots.target.symm (s.1,i)).1) ≠ 1}
  let e : {w : BitWord c // incomingThin P (center P p i w)} ≃ W :=
    Equiv.subtypeEquivRight fun w => and_congr_left fun _ => not_one _
  rw [Fintype.card_congr e, Fintype.card_congr (incomingWord P (s,i) 0),
    fixed_bit_count _ _ (proper_inv P s i)]

variable [Fintype V] [Fintype Tag] [Fintype L]

private theorem assigned_thin_count (p : Site V Tag L × Fin d) :
    Fintype.card {y : Subtype (incomingThin P) // P.assignedBundle (sourcePosition y.val) = p} =
      d * 2 ^ (c - 2) := by
  rw [Fintype.card_congr (assignedFiber P (incomingThin P) p), Fintype.card_sigma]
  simp only [incoming_thin_count, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

private theorem thin_site_count (t : Equiv.Perm (Site V Tag L × Fin d)) (s : Site V Tag L) :
    Fintype.card {y : Subtype (incomingThin P) // (t (P.assignedBundle (sourcePosition y.val))).1 = s} =
      d * (d * 2 ^ (c - 2)) := by
  let f := fun y : Subtype (incomingThin P) => P.assignedBundle (sourcePosition y.val)
  let e := Equiv.sigmaSubtypeFiberEquivSubtype f
    (q := fun p => (t p).1 = s) (p := fun m => (t (f m)).1 = s) (fun _ => Iff.rfl)
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  simp only [f, assigned_thin_count, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  apply congrArg (fun z : ℕ => z*(d*2^(c-2)))
  convert endpoint_site_count t s using 1; congr 1; apply Subsingleton.elim

private def splitTest {A B : Type*} (p : A ⊕ B → Prop) :
    Subtype p ≃ ({a : A // p (.inl a)} ⊕ {b : B // p (.inr b)}) where
  toFun x := match x with
    | ⟨.inl a,h⟩ => .inl ⟨a,h⟩
    | ⟨.inr b,h⟩ => .inr ⟨b,h⟩
  invFun
    | .inl a => ⟨.inl a.val,a.property⟩
    | .inr b => ⟨.inr b.val,b.property⟩
  left_inv := by rintro ⟨a | b,h⟩ <;> rfl
  right_inv := by rintro (⟨a,h⟩ | ⟨b,h⟩) <;> rfl

/-- Every site receives the same number of D maps in both layouts. The
three terms count the two kinds of mixed arcs and the thin--thin arcs. -/
theorem roleD_count (layout : Bool) (s : Site V Tag L) :
    Fintype.card {m : P.Motif // P.roleD layout m = s} = 3 * d ^ 2 * 2 ^ (c - 2) := by
  rw [Fintype.card_congr (dFiber P layout s)]
  rw [Fintype.card_congr (splitTest (fun t : DForm P => dSite P layout t = s)), Fintype.card_sum]
  rw [Fintype.card_congr (splitTest (fun t => dSite P layout (.inr t) = s)), Fintype.card_sum]
  change Fintype.card {x : Subtype (outgoingMixed P) // x.val.1.1 = s} +
    (Fintype.card {x : Subtype (incomingMixed P) // x.val.1.1 = s} + _) = _
  rw [Fintype.card_congr (siteFiber (outgoingMixed P) s),
    Fintype.card_congr (siteFiber (incomingMixed P) s)]
  simp only [Fintype.card_sigma, outgoing_mixed_count, incoming_mixed_count, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  calc
    _ = d * (2^(c-2)*d) + (d * (2^(c-2)*d) + d * (d * 2^(c-2))) := by
      apply congrArg (fun z : ℕ => d * (2^(c-2)*d) + (d * (2^(c-2)*d) + z))
      convert thin_site_count P (placementPerm P layout) s using 1; congr 1
    _ = _ := by ring

/-- The D-role count equals the same `dQ` used at A and B. -/
theorem roleD_count_uniform (layout : Bool) (s : Site V Tag L) (hc : 2 ≤ c) :
    Fintype.card {m : P.Motif // P.roleD layout m = s} = d * (3 * (2 ^ c * d) / 4) := by
  rw [roleD_count]
  have e : c = c - 2 + 2 := by omega
  conv_rhs => rw [e, Nat.pow_add]
  have h : 3 * (2 ^ (c - 2) * 2 ^ 2 * d) = (3 * 2 ^ (c - 2) * d) * 4 := by ring
  rw [h, Nat.mul_div_cancel _ (by decide : 0 < 4)]
  ring

end ThreeFlat.Diagonal.CompressorPacking

end OAI
