import OAI.Computability.BorderVNP.ShortenStaticRowsOccupancy

/-! # Reading unused positions in the three old-band rectangles

A public row is occupied exactly when its old cable exists and the band's
selection agrees with the rectangle. The padded presentation places every
other position at its reserved dummy site as a loop of width zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.StaticRows

open Crossing SeedIntervals CombiningStep
open scoped Classical

variable {D m nEdges nSeeds : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

private def withinBand (row : Fin nEdges) (b : Band D) : Fin (nEdges*(2*D+1)) :=
  finProdFinEquiv (row, bandRow D b)

private theorem withinBand_eq {r r' : Fin nEdges} {b b' : Band D}
    (h : (withinBand r b).val = (withinBand r' b').val) : r = r' ∧ b = b' := by
  have hp := finProdFinEquiv.injective (Fin.ext h : withinBand r b = withinBand r' b')
  exact ⟨congrArg Prod.fst hp, (bandRow D).injective (congrArg Prod.snd hp)⟩

/-- Candidate public row for an old band. Kinds zero and one name its two
hooks, and kind two names its retained cable. -/
def bandCandidate (nSeeds : ℕ) (kind : Fin 3) (row : Fin nEdges) (b : Band D) :
    Fin (edgeCapacity e nEdges nSeeds) :=
  ⟨kind.val*(nEdges*(2*D+1)) + (withinBand row b).val, by
    have h := (withinBand row b).isLt
    have hk : kind.val ≤ 2 := by omega
    have hmul := Nat.mul_le_mul_right (nEdges*(2*D+1)) hk
    dsimp only [edgeCapacity]
    omega⟩

/-- The public candidate number uses only the old row, the band number and the fixed stride. -/
theorem bandCandidate_val (kind : Fin 3) (row : Fin nEdges) (b : Band D) :
    (bandCandidate e nSeeds kind row b).val =
      kind.val*(nEdges*(2*D+1)) + ((bandRow D b).val + (2*D+1)*row.val) := rfl

variable [NeZero D] {P : Type*} {bits : P → ℕ} (p : Pack D P bits K) {A : Type} [Fintype A]
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
variable (old : p.layout.Edge ↪ Fin nEdges) (seed : A ↪ Fin nSeeds)

/-- The two hook names of every selected old band agree with their public candidates. -/
theorem hook_candidate (c : ↥((partition p.layout bin perm m).selected)) :
    edgeRows e p bin perm old seed (.inl (.inl c)) = bandCandidate e nSeeds 0 (old c.val.1) c.val.2 ∧
    edgeRows e p bin perm old seed (.inl (.inr c)) = bandCandidate e nSeeds 1 (old c.val.1) c.val.2 := by
  constructor <;> apply Fin.ext
  · simp only [bandCandidate, Fin.val_zero, zero_mul, zero_add]
    rfl
  · simp only [bandCandidate, Fin.val_one, one_mul]
    rfl

/-- Every unselected old band is named by its kind-two candidate. -/
theorem retained_candidate
    (c : {c : (layout p.layout bin perm m).Edge // c ∉ (partition p.layout bin perm m).selected}) :
    edgeRows e p bin perm old seed (.inr (.inl c)) = bandCandidate e nSeeds 2 (old c.val.1) c.val.2 := by
  apply Fin.ext
  rw [retainedRow, bandCandidate_val]
  simp only [bandAddress]
  omega

omit [NeZero D] in
private theorem candidate_inj {k k' : Fin 3} {r r' : Fin nEdges} {b b' : Band D}
    (hc : bandCandidate e nSeeds k r b = bandCandidate e nSeeds k' r' b') :
    k = k' ∧ r = r' ∧ b = b' := by
  have hval := congrArg Fin.val hc
  change k.val*(nEdges*(2*D+1)) + (withinBand r b).val =
    k'.val*(nEdges*(2*D+1)) + (withinBand r' b').val at hval
  have h := (withinBand r b).isLt
  have h' := (withinBand r' b').isLt
  have hk : k = k' := by
    fin_cases k <;> fin_cases k' <;> simp_all <;> omega
  subst k'
  exact ⟨rfl, withinBand_eq (Nat.add_left_cancel hval)⟩

/-- Occupancy of all three static rectangles, including old row names that
have no cable. The selected bands appear only in kinds zero and one. -/
theorem bandCandidate_mem_iff (k : Fin 3) (r : Fin nEdges) (b : Band D) :
    bandCandidate e nSeeds k r b ∈ Set.range (edgeRows e p bin perm old seed) ↔
      ∃ c : p.layout.Edge, old c = r ∧ ((c,b) ∈ (partition p.layout bin perm m).selected ↔ k.val < 2) := by
  constructor
  · rintro ⟨(u|u),hu⟩
    · rcases u with c | c
      · obtain ⟨hk,hr,hb⟩ := candidate_inj e ((hook_candidate e p bin perm old seed c).1.symm.trans hu)
        exact ⟨c.val.1,hr, by rw [← hb, ← hk]; exact iff_of_true c.property (by decide)⟩
      · obtain ⟨hk,hr,hb⟩ := candidate_inj e ((hook_candidate e p bin perm old seed c).2.symm.trans hu)
        exact ⟨c.val.1,hr, by rw [← hb, ← hk]; exact iff_of_true c.property (by decide)⟩
    · rcases u with c | ⟨a,c⟩
      · obtain ⟨hk,hr,hb⟩ := candidate_inj e ((retained_candidate e p bin perm old seed c).symm.trans hu)
        exact ⟨c.val.1,hr, by rw [← hb, ← hk]; exact iff_of_false c.property (by decide)⟩
      · have hx := congrArg Fin.val hu
        rw [bankRow] at hx
        change _ = k.val*(nEdges*(2*D+1)) + (withinBand r b).val at hx
        have hr := (withinBand r b).isLt
        have hmul := Nat.mul_le_mul_right (nEdges*(2*D+1)) (show k.val ≤ 2 by omega)
        omega
  · rintro ⟨c,rfl,hc⟩
    fin_cases k
    · let v : ↥((partition p.layout bin perm m).selected) := ⟨(c,b),hc.mpr (by decide)⟩
      exact ⟨.inl (.inl v),(hook_candidate e p bin perm old seed v).1⟩
    · let v : ↥((partition p.layout bin perm m).selected) := ⟨(c,b),hc.mpr (by decide)⟩
      exact ⟨.inl (.inr v),(hook_candidate e p bin perm old seed v).2⟩
    · let v : {z : (layout p.layout bin perm m).Edge // z ∉ (partition p.layout bin perm m).selected} :=
        ⟨(c,b),fun h => (by decide : ¬(2 : Fin 3).val < 2) (hc.mp h)⟩
      exact ⟨.inr (.inl v),retained_candidate e p bin perm old seed v⟩

/-- A missing input cable leaves all three candidate rectangles unoccupied. -/
theorem bandCandidate_missing (k : Fin 3) (r : Fin nEdges) (b : Band D) (hr : r ∉ Set.range old) :
    bandCandidate e nSeeds k r b ∉ Set.range (edgeRows e p bin perm old seed) := by
  intro h
  obtain ⟨c,hc,_⟩ := (bandCandidate_mem_iff e p bin perm old seed k r b).mp h
  exact hr ⟨c,hc⟩

/-- At an occupied old row, a rectangle of the wrong kind stays empty. -/
theorem bandCandidate_wrong_kind (k : Fin 3) (c : p.layout.Edge) (b : Band D)
    (wrong : ¬((c,b) ∈ (partition p.layout bin perm m).selected ↔ k.val < 2)) :
    bandCandidate e nSeeds k (old c) b ∉ Set.range (edgeRows e p bin perm old seed) := by
  intro h
  obtain ⟨u,hu,hkind⟩ := (bandCandidate_mem_iff e p bin perm old seed k (old c) b).mp h
  exact wrong (old.injective hu ▸ hkind)

/-- The real padded output gives dummy endpoints and width zero exactly as
required when the old row is missing or its band belongs in another rectangle. -/
theorem bandCandidate_hole (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    (dummy : Fin (edgeCapacity e nEdges nSeeds) → SiteShape e p A)
    (k : Fin 3) (r : Fin nEdges) (b : Band D)
    (hole : ¬∃ c : p.layout.Edge, old c = r ∧ ((c,b) ∈ (partition p.layout bin perm m).selected ↔ k.val < 2)) :
    let N := (output e p bin perm positive first q).layout
    let L := Packing.Names.layout N (outputRows e p bin perm positive first q old seed) dummy
    let i := Packing.Names.rowSlot (bandCandidate e nSeeds k r b)
    L.src i = dummy i ∧ L.dst i = dummy i ∧ L.width i = 0 :=
  Packing.Names.unused_row (output e p bin perm positive first q).layout
    (outputRows e p bin perm positive first q old seed) dummy (bandCandidate e nSeeds k r b)
    (fun h => hole ((bandCandidate_mem_iff e p bin perm old seed k r b).mp h))

end Shortening.StaticRows

end BorderVNP
end Computability
end OAI
