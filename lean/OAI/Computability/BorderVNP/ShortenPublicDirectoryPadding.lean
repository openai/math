import OAI.Computability.BorderVNP.PackedRoundSource
import OAI.Computability.BorderVNP.ShortenPublicSegmentStage

/-! # Concrete virtual sites for the old-band serializer

Each unused successor band row attaches to the source site of its old padded
cable. This is an existing physical site, including when the old row itself
is a hole. Its address is already present in the source-pointer column. A
seed-bank row uses its actual template source.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicDirectory

open Crossing SeedIntervals StaticRows PublicEndpoints PublicEndpoints.Successor Packing DirectoryCircuit
open scoped Classical

variable {D m V E nSeeds : ℕ} {K : Type*} [Field K] [NeZero D] (e : PaidIdentity K D m)
    {P : Type*} {bits : P → ℕ} (pack : Pack D P bits K) (rows : pack.layout.Edge ↪ Fin E)
    (oldDummy : Fin E → pack.layout.Site) {A : Type} [Fintype A] (seed : A ≃ Fin nSeeds)

private noncomputable def publicOrdinal (n : ℕ) : Fin n ≃ Fin n :=
  (Fintype.equivFin (Fin n)).trans (finCongr (Fintype.card_fin n))

private theorem publicOrdinal_slot {n : ℕ} (i : Fin n) : publicOrdinal n (Names.rowSlot i) = i :=
  (publicOrdinal n).apply_symm_apply _

/-- Chosen physical dummy site for every reserved successor cable slot. -/
noncomputable def nextDummy (i : Fin (edgeCapacity e E nSeeds)) : SiteShape e (densePack pack rows) A :=
  match (candidateEquiv e E seed).symm (publicOrdinal _ i) with
  | .inl r => .inl ((Names.layout pack.layout rows oldDummy).src (Names.rowSlot r.1))
  | .inr (a,u) => .inr ⟨a,templateSrc e u⟩

omit [NeZero D] [Fintype A] in
/-- The required padding pointer equals the genuine old source-pointer field, without any
test of occupancy or lookup in the expanded successor table. -/
theorem nextDummy_band (oldSite : pack.layout.Site ↪ Fin V) (r : Serializer.Row E D) :
    (siteRows e (densePack pack rows) oldSite seed.toEmbedding (nextDummy e pack rows oldDummy seed
      (Names.rowSlot (bandCandidate e nSeeds r.2.2 r.1 r.2.1)))).val =
      (storedSite pack.layout oldSite rows oldDummy r.1 true).val := by
  rw [← candidateEquiv_old e E seed r]
  simp only [nextDummy,publicOrdinal_slot,Equiv.symm_apply_apply]
  rfl

omit [NeZero D] [Fintype A] in
/-- A word large enough for the multiplied total old width works for every moved
bin and every next profile, including characteristic-dependent paid templates. -/
theorem bin_room {w S : ℕ} (bin : pack.layout.Edge → Option A)
    (total : (∑ c, pack.layout.width c) ≤ S)
    (word : Nat.clog 2 (widthMultiplier e*S+1) ≤ w) (a : A) :
    widthMultiplier e * count pack.layout bin a < 2^w := by
  have bound : count pack.layout bin a ≤ S := by
    rw [count_eq_sum]
    exact (Finset.sum_le_sum fun _ _ => by split <;> omega).trans total
  exact (Nat.lt_succ_of_le (Nat.mul_le_mul_left _ bound)).trans_le
    ((Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) word))

end Shortening.PublicDirectory

end BorderVNP
end Computability
end OAI
