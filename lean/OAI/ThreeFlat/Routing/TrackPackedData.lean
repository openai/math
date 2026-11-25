import OAI.ThreeFlat.Routing.StableCompactionRank
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI
/-! # Live prefixes of a rectangular array of edge fields -/

noncomputable section
namespace ThreeFlat.Routing.TrackData
open scoped BigOperators
open StableCompaction

variable {k d n : ℕ} (ord : Fin n ≃ Fin k × Fin d) (L : Fin k → ℕ) (fits : ∀ r, L r ≤ d)

/-- A fixed candidate row contributes exactly its selected prefix. -/
def mask (a : Fin n) : Bool := decide ((ord a).2.val < L (ord a).1)

/-- Zero-padded candidate data before stable compaction. -/
def padded (x : (r : Fin k) → Fin (L r) → Bool) (a : Fin n) : Bool :=
  if hj : (ord a).2.val < L (ord a).1 then x _ ⟨_,hj⟩ else false

private def activeEquiv : active (mask ord L) ≃ ((r : Fin k) × Fin (L r)) where
  toFun a := ⟨(ord a.val).1, (ord a.val).2.val, by
    simpa [mask] using mem_active.mp a.property⟩
  invFun z := ⟨ord.symm (z.1,Fin.castLE (fits z.1) z.2), by
    simp [mask,z.2.isLt]⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv z := by
    rcases z with ⟨r,j⟩
    simp
    exact (Fin.heq_ext_iff (by simp)).2 rfl

include fits in
theorem active_card : (active (mask ord L)).card = ∑ r, L r := by
  simpa only [Fintype.card_coe,Fintype.card_sigma,Fintype.card_fin] using
    Fintype.card_congr (activeEquiv ord L fits)

include fits in
/-- After the occupied prefix, stable compaction pins every bit to zero. -/
theorem compact_after (x : (r : Fin k) → Fin (L r) → Bool) (i : Fin n) (hi : ∑ r, L r ≤ i.val) :
    compact (mask ord L) (padded ord L x) i = false :=
  StableCompaction.compact_after _ _ _ ((active_card ord L fits).le.trans hi)

include ord fits in
private theorem width_le : ∑ r, L r ≤ n := by
  rw [← active_card ord L fits]
  exact (active (mask ord L)).card_le_univ.trans_eq (Fintype.card_fin n)

/-- The occupied prefix of the same compacted array used by the concrete network. -/
def stream (x : (r : Fin k) → Fin (L r) → Bool) (j : Fin (∑ r, L r)) : Bool :=
  compact (mask ord L) (padded ord L x) (Fin.castLE (width_le ord L fits) j)

theorem stream_injective : Function.Injective (stream ord L fits) := by
  intro x y h
  funext r j
  let a := ord.symm (r,Fin.castLE (fits r) j)
  have ha : mask ord L a = true := by simp [mask,a,j.isLt]
  have hk := (prefixCount_lt_card ha).trans_le (active_card ord L fits).le
  let z : Fin (∑ r, L r) := ⟨prefixCount (mask ord L) a,hk⟩
  have he := congrFun h z
  change compact _ _ _ = compact _ _ _ at he
  rw [compact_at_prefixCount _ _ ha (show _ = prefixCount _ a from rfl),
      compact_at_prefixCount _ _ ha (show _ = prefixCount _ a from rfl)] at he
  have read (f : (r : Fin k) → Fin (L r) → Bool) : padded ord L f a = f r j := by
    let atPair (z : Fin k × Fin d) := if hz : z.2.val < L z.1 then f z.1 ⟨z.2.val,hz⟩ else false
    change atPair (ord (ord.symm (r,Fin.castLE (fits r) j))) = _
    rw [Equiv.apply_symm_apply]
    exact dite_eq_left j.isLt
  rw [read,read] at he
  exact he

/-- Every bit string of the occupied length is the packed stream of some row assignment. -/
theorem stream_surjective : Function.Surjective (stream ord L fits) := by
  classical
  have hc : Fintype.card ((r : Fin k) → Fin (L r) → Bool) =
      Fintype.card (Fin (∑ r, L r) → Bool) := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fun, Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
  exact ((Fintype.bijective_iff_injective_and_card _).2 ⟨stream_injective ord L fits, hc⟩).2

end ThreeFlat.Routing.TrackData

end
end OAI
