import OAI.Computability.VPVNP.CompressorSlotNetwork

/-!
# Numeric decoding of shrinking endpoint owners

The old CD arc, role-edge type, subdivision and absolute lane are recovered
by quotient and remainder before any endpoint lookup. This identifies which
entries of the two rectangular owner tables are real and which are holes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Slots

open Compression Compression.PackingData Compression.SurvivingSlots

variable {V H Tag L : Type*} {d c N J nL pad : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (subdiv : Fin 4 → ℕ)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)

/-- Cardinality of the old outgoing arc space with the remaining lane suppressed. -/
abbrev oldBaseArcCount (N J d c : ℕ) := N * (J * (d * (2 ^ c * d)))

private def digitPair {A B : Type*} {a b : ℕ} (f : A ≃ Fin a) (g : B ≃ Fin b) : A × B ≃ Fin (a*b) :=
  (f.prodCongr g).trans finProdFinEquiv

/-- Dense old arc index with the original absolute lane as the least significant digit. -/
def oldArcIndex : Arc V H Tag L d c ≃ Fin (oldBaseArcCount N J d c * nL) :=
  let reorder : Arc V H Tag L d c ≃ (V × Tag × Fin d × BitWord c × H) × L :=
    ⟨fun a ↦ ((a.1.1.1, a.1.1.2.1, a.1.2, a.2), a.1.1.2.2),
     fun ⟨⟨v, t, k, w, h⟩, g⟩ ↦ (((v,t,g),k),w,h), fun _ ↦ rfl, fun _ ↦ rfl⟩
  reorder.trans (digitPair (digitPair vertices (digitPair tags (digitPair (Equiv.refl (Fin d))
    (digitPair (bitWordFinEquiv c) P.slotLabel)))) lanes)

/-- Mixed-radix coordinates of a genuine candidate arc, consisting of edge type, old base arc,
subdivision, and absolute lane. -/
abbrev GenuineDigits (N J nL d c : ℕ) (subdiv : Fin 4 → ℕ) :=
  ((Fin 4 × Fin (oldBaseArcCount N J d c)) × Fin (∑ t, subdiv t)) × Fin nL

private def genuineIndex : GenuineDigits N J nL d c subdiv ≃ Fin (keyCount N J d c subdiv * nL) :=
  (digitPair (digitPair finProdFinEquiv (Equiv.refl (Fin (∑ t, subdiv t)))) (Equiv.refl (Fin nL))).trans
    (finCongr (by unfold keyCount oldBaseArcCount; ac_rfl))

/-- In order, the role-edge type, old base arc number, subdivision and absolute lane. -/
def genuineDigits (a : Fin (keyCount N J d c subdiv * nL)) : GenuineDigits N J nL d c subdiv :=
  (genuineIndex subdiv).symm a

theorem genuineDigits_val (a : Fin (keyCount N J d c subdiv * nL)) :
    let x := genuineDigits subdiv a
    let key := a.val / nL
    x.1.1.1.val = key / (∑ t, subdiv t) / oldBaseArcCount N J d c ∧
      x.1.1.2.val = key / (∑ t, subdiv t) % oldBaseArcCount N J d c ∧
      x.1.2.val = key % (∑ t, subdiv t) ∧ x.2.val = a.val % nL := ⟨rfl, rfl, rfl, rfl⟩

/-- Look up the original absolute old arc at the two decoded digits. -/
def digitArc (x : GenuineDigits N J nL d c subdiv) : Arc V H Tag L d c :=
  (oldArcIndex P vertices tags lanes).symm (finProdFinEquiv (x.1.1.2, x.2))

omit [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] in
theorem digitArc_index (x : GenuineDigits N J nL d c subdiv) :
    (oldArcIndex P vertices tags lanes (digitArc P subdiv vertices tags lanes x)).val =
      x.1.1.2.val * nL + x.2.val := by
  rw [digitArc, Equiv.apply_symm_apply]
  change x.2.val + nL * x.1.1.2.val = _
  ring

/-- CD validity test on an original directed arc, independent of subdivision and type. -/
abbrev isCD (a : Arc V H Tag L d c) :=
  ¬ (P.thick (sourcePosition a) ∧ P.thick (sourcePosition (P.actual a)))

private def encodeIdDigits (i : Id P.Motif subdiv) : GenuineDigits N J nL d c subdiv :=
  let p := finProdFinEquiv.symm (oldArcIndex P vertices tags lanes i.2.1.1)
  let bound := Finset.single_le_sum (fun t _ ↦ Nat.zero_le (subdiv t)) (Finset.mem_univ i.1)
  (((i.1, p.1), i.2.2.castLE bound), p.2)

private theorem encode_address (i : Id P.Motif subdiv) :
    arcAddress P subdiv vertices tags lanes pad (.inl i) =
      (genuineIndex subdiv (encodeIdDigits P subdiv vertices tags lanes i)).castAdd _ := by
  let f := digitPair vertices (digitPair tags (digitPair (Equiv.refl (Fin d))
    (digitPair (bitWordFinEquiv c) P.slotLabel)))
  let a := i.2.1.val
  let b := f (a.1.1.1, a.1.1.2.1, a.1.2, a.2)
  let l := lanes a.1.1.2.2
  have hp : finProdFinEquiv.symm (oldArcIndex P vertices tags lanes a) = (b,l) :=
    finProdFinEquiv.symm_apply_apply (b,l)
  change finProdFinEquiv.symm (oldArcIndex P vertices tags lanes i.2.1.val) = (b,l) at hp
  apply Fin.ext
  simp only [encodeIdDigits]
  rw [hp]
  change l.val + nL * (i.2.2.val + (∑ t, subdiv t) * b.val +
    (oldBaseArcCount N J d c * (∑ t, subdiv t)) * i.1.val) =
    l.val + nL * (i.2.2.val + (∑ t, subdiv t) * (b.val + oldBaseArcCount N J d c * i.1.val))
  ring

private def digitId (x : GenuineDigits N J nL d c subdiv) : Option (Id P.Motif subdiv) :=
  let a := digitArc P subdiv vertices tags lanes x
  if hj : x.1.2.val < subdiv x.1.1.1 then
    if hm : isCD P a then some ⟨x.1.1.1, ⟨a,hm⟩, ⟨x.1.2.val,hj⟩⟩ else none
  else none

private theorem digitId_encode (i : Id P.Motif subdiv) :
    digitId P subdiv vertices tags lanes (encodeIdDigits P subdiv vertices tags lanes i) = some i := by
  have ha : digitArc P subdiv vertices tags lanes (encodeIdDigits P subdiv vertices tags lanes i) = i.2.1.1 := by
    change (oldArcIndex P vertices tags lanes).symm (finProdFinEquiv (finProdFinEquiv.symm _)) = _
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  dsimp only [digitId]
  rw [ha]
  change (if hj : i.2.2.val < subdiv i.1 then if hm : isCD P i.2.1.1 then
    some ⟨i.1, ⟨i.2.1.1,hm⟩, ⟨i.2.2.val,hj⟩⟩ else none else none) = some i
  rw [dite_eq_left i.2.2.isLt, dite_eq_left i.2.1.prop]

private theorem encode_digitId (x : GenuineDigits N J nL d c subdiv) (i : Id P.Motif subdiv)
    (hi : digitId P subdiv vertices tags lanes x = some i) :
    encodeIdDigits P subdiv vertices tags lanes i = x := by
  dsimp only [digitId] at hi
  split at hi <;> try contradiction
  split at hi <;> try contradiction
  obtain rfl := Option.some.inj hi
  simp only [encodeIdDigits, digitArc, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  rfl

/-- Quotient/remainder decoding of a genuine-region candidate, including the
two reasons for an unoccupied address. -/
theorem decodeArc_genuine (a : Fin (keyCount N J d c subdiv * nL)) :
    let x := genuineDigits subdiv a
    let old := digitArc P subdiv vertices tags lanes x
    decodeArc P subdiv vertices tags lanes pad (a.castAdd _) =
      if hj : x.1.2.val < subdiv x.1.1.1 then
        if hm : isCD P old then some (.inl ⟨x.1.1.1, ⟨old,hm⟩, ⟨x.1.2.val,hj⟩⟩) else none
      else none := by
  intro x old
  have eqn : decodeArc P subdiv vertices tags lanes pad (a.castAdd _) =
      (digitId P subdiv vertices tags lanes x).map Sum.inl := by
    apply Option.ext
    intro i
    rw [decodeArc_eq_some, Option.map_eq_some_iff]
    rcases i with i | p
    · simp only [Sum.inl.injEq, exists_eq_right]
      rw [encode_address, Fin.ext_iff]
      change (genuineIndex subdiv (encodeIdDigits P subdiv vertices tags lanes i)).val = a.val ↔ _
      rw [← Fin.ext_iff, ← Equiv.eq_symm_apply]
      change encodeIdDigits P subdiv vertices tags lanes i = x ↔ _
      exact ⟨fun h ↦ h ▸ digitId_encode P subdiv vertices tags lanes i,
        fun h ↦ encode_digitId P subdiv vertices tags lanes x i h⟩
    · simp only [Sum.inl_ne_inr, and_false, exists_false, iff_false]
      intro h
      have hn := congrArg Fin.val h
      change keyCount N J d c subdiv * nL + _ = a.val at hn
      have := a.isLt
      omega
  rw [eqn]
  dsimp only [digitId]
  rw [show digitArc P subdiv vertices tags lanes x = old from rfl]
  by_cases hj : x.1.2.val < subdiv x.1.1.1
  · rw [dite_eq_left hj, dite_eq_left hj]
    by_cases hm : isCD P old
    · rw [dite_eq_left hm, dite_eq_left hm]; rfl
    · rw [dite_eq_right hm, dite_eq_right hm]; rfl
  · rw [dite_eq_right hj, dite_eq_right hj]; rfl

/-- Exactly the proper subdivisions of CD arcs have genuine endpoint owners. -/
theorem decodeArc_genuine_isSome (a : Fin (keyCount N J d c subdiv * nL)) :
    let x := genuineDigits subdiv a
    (decodeArc P subdiv vertices tags lanes pad (a.castAdd _)).isSome ↔
      x.1.2.val < subdiv x.1.1.1 ∧ isCD P (digitArc P subdiv vertices tags lanes x) := by
  intro x
  rw [decodeArc_genuine]
  rw [show genuineDigits subdiv a = x from rfl]
  by_cases hj : x.1.2.val < subdiv x.1.1.1
  · rw [dite_eq_left hj, and_iff_right hj]
    by_cases hm : isCD P (digitArc P subdiv vertices tags lanes x)
    · rw [dite_eq_left hm]; simpa using hm
    · rw [dite_eq_right hm]; simpa using hm
  · rw [dite_eq_right hj]
    exact iff_of_false Bool.false_ne_true (fun h ↦ hj h.1)

/-- Select the endpoint owner directly from the role-edge type and its old CD arc. -/
theorem decodeArc_genuine_end (a : Fin (keyCount N J d c subdiv * nL)) (layout side : Bool) :
    let x := genuineDigits subdiv a
    let old := digitArc P subdiv vertices tags lanes x
    (decodeArc P subdiv vertices tags lanes pad (a.castAdd _)).map (actualEnd P subdiv tags layout side) =
      if x.1.2.val < subdiv x.1.1.1 then
        if hm : isCD P old then some (P.survivingRole layout (endRole layout side x.1.1.1) ⟨old,hm⟩) else none
      else none := by
  intro x old
  rw [decodeArc_genuine]
  rw [show genuineDigits subdiv a = x from rfl, show digitArc P subdiv vertices tags lanes x = old from rfl]
  by_cases hj : x.1.2.val < subdiv x.1.1.1
  · rw [dite_eq_left hj, ite_eq_left hj]
    by_cases hm : isCD P old
    · rw [dite_eq_left hm, dite_eq_left hm]; rfl
    · rw [dite_eq_right hm, dite_eq_right hm]; rfl
  · rw [dite_eq_right hj, ite_eq_right hj]; rfl

/-- Read the source site and the local dummy number from the address offset
past the genuine interval. The site number is the quotient by the padding
degree and the dummy number is the remainder. -/
def dummySourceSite (a : Fin ((N * (J * nL)) * pad)) : Site V Tag L :=
  (SlotSchedule.siteIndex vertices tags lanes).symm a.divNat

theorem decodeArc_dummy (a : Fin ((N * (J * nL)) * pad)) :
    decodeArc P subdiv vertices tags lanes pad (a.natAdd (keyCount N J d c subdiv * nL)) =
      some (.inr (dummySourceSite vertices tags lanes a, a.modNat)) := by
  rw [decodeArc_eq_some]
  let site := SlotSchedule.siteIndex vertices tags lanes
  change finSumFinEquiv (.inr (finProdFinEquiv (site (site.symm a.divNat), a.modNat))) = _
  rw [site.apply_symm_apply, ← show finProdFinEquiv.symm a = (a.divNat,a.modNat) from rfl,
    finProdFinEquiv.apply_symm_apply, finSumFinEquiv_apply_right]

/-- In the dummy interval, the selected endpoint keeps the lane and applies
the tag cycle exactly for an incoming field. -/
theorem decodeArc_dummy_end (a : Fin ((N * (J * nL)) * pad)) (layout side : Bool) :
    (decodeArc P subdiv vertices tags lanes pad (a.natAdd (keyCount N J d c subdiv * nL))).map
      (actualEnd P subdiv tags layout side) = some (dummyEnd tags side (dummySourceSite vertices tags lanes a)) := by
  rw [decodeArc_dummy]; rfl

/-- The local dummy address for any member of the trailing interval. -/
def dummyOffset (a : Fin (RecordCount N J nL d c pad subdiv)) (h : keyCount N J d c subdiv * nL ≤ a.val) :
    Fin ((N * (J * nL)) * pad) :=
  ⟨a.val - keyCount N J d c subdiv * nL, by have := a.isLt; unfold RecordCount at this; omega⟩

theorem dummyOffset_natAdd (a : Fin (RecordCount N J nL d c pad subdiv)) (h : keyCount N J d c subdiv * nL ≤ a.val) :
    (dummyOffset subdiv a h).natAdd (keyCount N J d c subdiv * nL) = a := by
  apply Fin.ext
  change keyCount N J d c subdiv * nL + (a.val - keyCount N J d c subdiv * nL) = a.val
  omega

open SlotSchedule

/-- The field's two least-significant operations split off its orientation bit. -/
theorem endpoint_field_digits {n : ℕ} (a : Fin n) (s : Fin 2) :
    (finProdFinEquiv (a,s)).val / 2 = a.val ∧ (finProdFinEquiv (a,s)).val % 2 = s.val :=
  ⟨congrArg (fun z : Fin n × Fin 2 ↦ z.1.val) (finProdFinEquiv.symm_apply_apply (a,s)),
   congrArg (fun z : Fin n × Fin 2 ↦ z.2.val) (finProdFinEquiv.symm_apply_apply (a,s))⟩

/-- Numerical directory destination on the entire genuine-field interval.
Invalid addresses occupy distinct rows past all real endpoint owners. -/
theorem directory_genuine_destination (layout : Bool) (a : Fin (keyCount N J d c subdiv * nL)) (s : Fin 2) :
    let field := finProdFinEquiv (a.castAdd ((N * (J * nL)) * pad), s)
    let x := genuineDigits subdiv a
    let old := digitArc P subdiv vertices tags lanes x
    let hole := (N * (J * nL)) * 2 + field.val
    ((slotDirectory P subdiv vertices tags lanes layout).destination field).val =
      if x.1.2.val < subdiv x.1.1.1 then
        if hm : isCD P old then 2 * (siteIndex vertices tags lanes
          (P.survivingRole layout (endRole layout (decide (s=1)) x.1.1.1) ⟨old,hm⟩)).val + s.val
        else hole
      else hole := by
  intro field x old hole
  let D := slotDirectory P subdiv vertices tags lanes layout (pad := pad)
  have hd : D.decode field = (decodeArc P subdiv vertices tags lanes pad (a.castAdd _)).map (fun i ↦ (i,s)) := by
    simp only [D, field, slotDirectory, Equiv.symm_apply_apply]
  change (D.destination field).val = _
  rw [Directory.destination, hd, decodeArc_genuine]
  rw [show genuineDigits subdiv a = x from rfl, show digitArc P subdiv vertices tags lanes x = old from rfl]
  by_cases hj : x.1.2.val < subdiv x.1.1.1
  · rw [dite_eq_left hj, ite_eq_left hj]
    by_cases hm : isCD P old
    · rw [dite_eq_left hm, dite_eq_left hm]
      change s.val + 2 * _ = 2 * _ + s.val
      exact Nat.add_comm _ _
    · rw [dite_eq_right hm, dite_eq_right hm]; rfl
  · rw [dite_eq_right hj, ite_eq_right hj]; rfl

/-- Numerical destination of a dummy field in the second scan. The dummy
source index is the local field divided by two and then by the padding degree. -/
theorem directory_dummy_destination (layout : Bool) (a : Fin ((N * (J * nL)) * pad)) (s : Fin 2) :
    let field := finProdFinEquiv (a.natAdd (keyCount N J d c subdiv * nL), s)
    let localField := finProdFinEquiv (a,s)
    let site := siteIndex vertices tags lanes
    ((slotDirectory P subdiv vertices tags lanes layout).destination field).val =
      2 * (if s.val = 0 then localField.val / 2 / pad
        else (site (dummyEnd tags true (site.symm a.divNat))).val) + s.val := by
  intro field localField site
  let D := slotDirectory P subdiv vertices tags lanes layout (pad := pad)
  have hd : D.decode field = (decodeArc P subdiv vertices tags lanes pad (a.natAdd _)).map (fun i ↦ (i,s)) := by
    simp only [D, field, slotDirectory, Equiv.symm_apply_apply]
  change (D.destination field).val = _
  rw [Directory.destination, hd, decodeArc_dummy]
  change s.val + 2 * (site (dummyEnd tags (decide (s = 1)) (site.symm a.divNat))).val = _
  rw [Nat.add_comm s.val, (endpoint_field_digits a s).1]
  fin_cases s
  · change 2 * (site (site.symm a.divNat)).val + 0 = 2 * a.divNat.val + 0
    rw [site.apply_symm_apply]
  · rfl

end CompressorRecords.Slots

end VPVNP
end Computability
end OAI
