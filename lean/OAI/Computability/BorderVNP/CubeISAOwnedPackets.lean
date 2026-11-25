import OAI.Computability.BorderVNP.CubePhysicalDeclaration

/-! # Enumerating the packets assigned to a single unordered row

Fixing the two symbols at the grouping coordinate leaves one pair of symbols
at each other coordinate, an orientation, and a block. A numeric counter scans
those fields in mixed radix. Its only rejected counters have an equal or
decreasing symbol pair. Thus the scan cost uses just the remaining coordinates.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.Owned

/-- Number of counter positions scanned for one strict symbol row. -/
def packetTrials (n d blocks : ℕ) : ℕ := (d*d)^n * 2 * blocks

variable {n d blocks : ℕ}

/-- The explicit mixed-radix fields. The block is least significant, followed
by the orientation bit and the pairs at the other coordinates in order. -/
def packetDigits (n d blocks : ℕ) : Fin (packetTrials n d blocks) ≃
    ((Fin n → Fin d × Fin d) × Bool) × Fin blocks :=
  let pairs : Fin ((d*d)^n) ≃ (Fin n → Fin d × Fin d) :=
    finFunctionFinEquiv.symm.trans (Equiv.piCongrRight fun _ => finProdFinEquiv.symm)
  finProdFinEquiv.symm.trans
    ((finProdFinEquiv.symm.trans (pairs.prodCongr finTwoEquiv)).prodCongr (Equiv.refl _))

/-- Validity is checked on just the remaining coordinates. -/
def packetTrialValid (t : Fin (packetTrials n d blocks)) : Prop :=
  ∀ j, ((packetDigits n d blocks t).1.1 j).1 < ((packetDigits n d blocks t).1.1 j).2

instance (t : Fin (packetTrials n d blocks)) : Decidable (packetTrialValid t) :=
  inferInstanceAs (Decidable (∀ j, ((packetDigits n d blocks t).1.1 j).1 <
    ((packetDigits n d blocks t).1.1 j).2))

/-- The arithmetic readout for every field of the counter. -/
theorem packetDigits_values (t : Fin (packetTrials n d blocks)) :
    let x := packetDigits n d blocks t
    x.2.val = t.val % blocks ∧
    x.1.2 = decide (t.val / blocks % 2 = 1) ∧
    ∀ j : Fin n, let v := t.val / blocks / 2 / (d*d)^j.val % (d*d)
                 (x.1.1 j).1.val = v / d ∧ (x.1.1 j).2.val = v % d := by
  refine ⟨rfl, ?_, fun _ => ⟨rfl, rfl⟩⟩
  change ((_ : Fin 2) == 1) = _
  rw [Bool.eq_iff_iff]
  simp [Fin.ext_iff, Fin.modNat, Fin.divNat]

/-- Valid counter positions correspond bijectively to packets whose grouping
coordinate is the designated strict pair. The inverse removes that coordinate
and encodes the remaining digits. -/
def packetRowEquiv (i : Fin (n+1)) (s : Symbols d) :
    {t : Fin (packetTrials n d blocks) // packetTrialValid t} ≃
      {p : Packet n d blocks // p.1.1 i = s} where
  toFun t :=
    let x := packetDigits n d blocks t.val
    ⟨((i.insertNth (α := fun _ => Symbols d) s (fun j => ⟨x.1.1 j, t.property j⟩), x.1.2), x.2),
      by simp only [Fin.insertNth_apply_same]⟩
  invFun p :=
    let x := (((fun j => (p.val.1.1 (i.succAbove j)).val), p.val.1.2), p.val.2)
    ⟨(packetDigits n d blocks).symm x, by
      intro j
      simp only [Equiv.apply_symm_apply]
      exact (p.val.1.1 (i.succAbove j)).property⟩
  left_inv t := by
    apply Subtype.ext
    apply (packetDigits n d blocks).injective
    simp only [Equiv.apply_symm_apply, Fin.insertNth_apply_succAbove]
  right_inv p := by
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    refine Prod.ext (Prod.ext ?_ rfl) rfl
    change i.insertNth (α := fun _ => Symbols d) s (i.removeNth p.val.1.1) = p.val.1.1
    exact (Fin.insertNth_eq_iff (α := fun _ => Symbols d)).mpr ⟨p.property.symm, rfl⟩

/-- The executable owned-row scan skips precisely the invalid digits. -/
def packetTrial (i : Fin (n+1)) (s : Symbols d) (t : Fin (packetTrials n d blocks)) :
    Option (Packet n d blocks) :=
  if h : packetTrialValid t then some (packetRowEquiv i s ⟨t,h⟩).val else none

/-- An unordered row test on a packet is the same as comparing its increasing
coordinate pair with the row's increasing representative. -/
theorem packet_itemRow_eq_iff {width : ℕ} (i : Fin (n+1)) (s : Symbols d)
    (p : Packet n d blocks) :
    itemRow i (.inl p : Item n d blocks width) = Sym2.mk s.val.1 s.val.2 ↔ p.1.1 i = s := by
  change Sym2.mk _ _ = Sym2.mk _ _ ↔ _
  rw [Sym2.eq_iff]
  constructor
  · rintro (h | ⟨h₁,h₂⟩)
    · exact Subtype.ext (Prod.ext h.1 h.2)
    · have h := (p.1.1 i).property
      rw [h₁, h₂] at h
      exact (s.property.not_gt h).elim
  · intro h
    exact Or.inl ⟨congrArg (fun v : Symbols d => v.val.1) h,
      congrArg (fun v : Symbols d => v.val.2) h⟩

/-- The scan returns each physical packet assigned to this row exactly once
and emits no packet from a different row. -/
theorem packetTrial_exactly_once {width : ℕ} (i : Fin (n+1)) (s : Symbols d)
    (p : Packet n d blocks) :
    (∃! t, packetTrial i s t = some p) ↔
      itemRow i (.inl p : Item n d blocks width) = Sym2.mk s.val.1 s.val.2 := by
  rw [packet_itemRow_eq_iff]
  constructor
  · rintro ⟨t,ht,_⟩
    unfold packetTrial at ht
    split at ht
    · exact (Option.some.inj ht) ▸ (packetRowEquiv i s ⟨t,‹_›⟩).property
    · contradiction
  · intro hp
    let u := (packetRowEquiv (blocks := blocks) i s).symm ⟨p,hp⟩
    have hu : packetRowEquiv i s u = ⟨p,hp⟩ := Equiv.apply_symm_apply ..
    refine ⟨u.val, ?_, ?_⟩
    · simp only [packetTrial, dite_eq_left u.property, hu]
    · intro t ht
      unfold packetTrial at ht
      split at ht
      · rename_i hv
        have he : packetRowEquiv i s ⟨t,hv⟩ = packetRowEquiv i s u :=
          hu ▸ Subtype.ext (Option.some.inj ht)
        exact congrArg Subtype.val ((packetRowEquiv i s).injective he)
      · contradiction

end Cube.Physical.Owned

end BorderVNP
end Computability
end OAI
