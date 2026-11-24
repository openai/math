import OAI.Computability.VPVNP.CompressorRecordSlots

/-!
# Scanning the address space for surviving slot records

The absolute arc record uses a mixed-radix word. Every address can be decoded
locally into an old arc, a role edge, a subdivision, and an absolute lane,
or into a dummy site and dummy number. Only thick–thick old arcs and subdivision
numbers outside their type's range leave holes in this space.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Slots

open Compression Compression.PackingData Compression.SurvivingSlots

variable {V H Tag L : Type*} {d c N J nL : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (subdiv : Fin 4 → ℕ)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL) (pad : ℕ)

/-- Identifier of a surviving arc, either a role edge and subdivision of a motif or a dummy
slot at a packed site. -/
abbrev ActualId := Id P.Motif subdiv ⊕ Site V Tag L × Fin pad

/-- Size of the address space for surviving slot records, including unused genuine candidate
addresses and all dummy slots. -/
abbrev RecordCount (N J nL d c pad : ℕ) (subdiv : Fin 4 → ℕ) :=
  keyCount N J d c subdiv * nL + (N * (J * nL)) * pad

private abbrev Candidate (V H Tag L : Type*) (d c pad m : ℕ) :=
  ((Fin 4 × ((V × Tag × Fin d × BitWord c × H) × Fin m)) × L) ⊕ Site V Tag L × Fin pad

private def pairCode {A B : Type*} {a b : ℕ} (f : A ≃ Fin a) (g : B ≃ Fin b) : A × B ≃ Fin (a * b) :=
  (f.prodCongr g).trans finProdFinEquiv

private def candidateIndex : Candidate V H Tag L d c pad (∑ t, subdiv t) ≃
    Fin (RecordCount N J nL d c pad subdiv) :=
  let old := pairCode vertices (pairCode tags (pairCode (Equiv.refl (Fin d))
    (pairCode (bitWordFinEquiv c) P.slotLabel)))
  let key := pairCode (Equiv.refl (Fin 4)) (pairCode old (Equiv.refl (Fin (∑ t, subdiv t))))
  let site := pairCode vertices (pairCode tags lanes)
  ((pairCode key lanes).sumCongr (pairCode site (Equiv.refl (Fin pad)))).trans finSumFinEquiv

private def toCandidate : ActualId P subdiv pad → Candidate V H Tag L d c pad (∑ t, subdiv t)
  | .inr x => .inr x
  | .inl ⟨t, m, j⟩ =>
    let a := m.val
    let h : subdiv t ≤ ∑ t, subdiv t :=
      Finset.single_le_sum (fun t _ ↦ Nat.zero_le (subdiv t)) (Finset.mem_univ _)
    .inl ((t, ((a.1.1.1, a.1.1.2.1, a.1.2, a.2), j.castLE h)), P.sourceLane m)

private def fromCandidate : Candidate V H Tag L d c pad (∑ t, subdiv t) → Option (ActualId P subdiv pad)
  | .inr x => some (.inr x)
  | .inl ((t, ((v, tag, slot, bits, h), j)), g) =>
    let a : Arc V H Tag L d c := (((v,tag,g),slot),bits,h)
    if hj : j.val < subdiv t then
      if hm : ¬ (P.thick (sourcePosition a) ∧ P.thick (sourcePosition (P.actual a))) then
        some (.inl ⟨t, ⟨a, hm⟩, ⟨j.val, hj⟩⟩)
      else none
    else none

private theorem from_to (e : ActualId P subdiv pad) :
    fromCandidate P subdiv pad (toCandidate P subdiv pad e) = some e := by
  rcases e with ⟨t,⟨⟨⟨⟨v, tag, g⟩, slot⟩, bits,h⟩, hm⟩, j⟩ | x
  · have hg : P.sourceLane ⟨(((v,tag,g),slot),bits,h), hm⟩ = g := rfl
    simp only [toCandidate, fromCandidate, hg, Fin.val_castLE, dite_eq_left j.isLt, dite_eq_left hm]
  · rfl

private theorem to_from {x : Candidate V H Tag L d c pad (∑ t, subdiv t)} {e : ActualId P subdiv pad}
    (h : fromCandidate P subdiv pad x = some e) : toCandidate P subdiv pad e = x := by
  rcases x with ⟨⟨t,⟨⟨v, tag, slot, bits,h'⟩, j⟩⟩, g⟩ | x
  · by_cases hj : j.val < subdiv t
    · let a : Arc V H Tag L d c := (((v, tag, g), slot), bits, h')
      by_cases hm : ¬ (P.thick (sourcePosition a) ∧ P.thick (sourcePosition (P.actual a)))
      · dsimp only [a] at hm
        simp only [fromCandidate, dite_eq_left hj, dite_eq_left hm, Option.some.injEq] at h
        rw [← h]; rfl
      · dsimp only [a] at hm
        simp only [fromCandidate, dite_eq_left hj, dite_eq_right hm, reduceCtorEq] at h
    · simp only [fromCandidate, dite_eq_right hj, reduceCtorEq] at h
  · cases h; rfl

/-- Random-access decode of one numeric arc address. -/
def decodeArc (a : Fin (RecordCount N J nL d c pad subdiv)) : Option (ActualId P subdiv pad) :=
  fromCandidate P subdiv pad ((candidateIndex P subdiv vertices tags lanes pad).symm a)

private theorem candidateIndex_actual (e : ActualId P subdiv pad) :
    candidateIndex P subdiv vertices tags lanes pad (toCandidate P subdiv pad e) =
      arcAddress P subdiv vertices tags lanes pad e := by
  rcases e with ⟨t, m, j⟩ | x <;> rfl

/-- Scanning numeric addresses visits every genuine or dummy arc exactly once. -/
theorem decodeArc_eq_some (a : Fin (RecordCount N J nL d c pad subdiv)) (e : ActualId P subdiv pad) :
    decodeArc P subdiv vertices tags lanes pad a = some e ↔ arcAddress P subdiv vertices tags lanes pad e = a := by
  let f := candidateIndex P subdiv vertices tags lanes pad
  rw [← candidateIndex_actual]
  change fromCandidate P subdiv pad (f.symm a) = some e ↔ f (toCandidate P subdiv pad e) = a
  constructor
  · intro h; rw [to_from P subdiv pad h, f.apply_symm_apply]
  · intro h; rw [← h, f.symm_apply_apply, from_to]

/-- The high-order component of a genuine arc address is the relative key,
and the low-order component is the absolute lane of its original CD arc. -/
theorem address_genuine_val (i : Id P.Motif subdiv) :
    (arcAddress P subdiv vertices tags lanes pad (.inl i)).val =
      (lanes (P.sourceLane i.2.1)).val + nL * (relativeKey P subdiv vertices tags i).val := rfl

/-- Taking the quotient of the absolute genuine record address recovers its
relative integer key directly. -/
theorem address_div_lane (i : Id P.Motif subdiv) :
    (arcAddress P subdiv vertices tags lanes pad (.inl i)).val / nL =
      (relativeKey P subdiv vertices tags i).val := by
  rw [address_genuine_val, Nat.add_mul_div_left _ _ (by have := (lanes (P.sourceLane i.2.1)).isLt; omega),
    Nat.div_eq_of_lt (lanes (P.sourceLane i.2.1)).isLt, Nat.zero_add]

end CompressorRecords.Slots

end VPVNP
end Computability
end OAI
