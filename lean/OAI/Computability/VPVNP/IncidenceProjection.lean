import OAI.Computability.VPVNP.IncidencePasses
import OAI.Computability.VPVNP.IncidenceRecords
import OAI.Computability.VPVNP.IncidenceReindex

/-! # Exact-one weighted projections at prescribed lengths

Serialize each column once, interleaving its free selection bit with fixed
incidence data. The read-only control checks every row on this same input.
The unary program table depends only on the number of rows, while the data
occupy exactly `k * (m + 2) + 1` bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace IncidenceMachine

open UniversalMachine InterleavedPinning
open scoped Classical

private theorem correct (padded : Word) {m k : ℕ} (M : Fin m → Fin k → Bool)
    (x : Fin k → Bool) (ticks : ℕ)
    (ht : m * ((padded ++ (rowBits (records M x)).reverse).length +
        (rowBits (records M x)).length + 1) + 1 ≤ ticks) :
    paths (machine m) ticks (initial (machine m) (padded ++ (rowBits (records M x)).reverse)) =
      (exactOne M x).toNat := by
  have hs : 0 < (rowBits (records M x)).length := by rw [length_rowBits_records]; omega
  have h := check_rows padded (rowBits (records M x)) hs (fun r => rowHits r (records M x) = 1)
    (fun r f => by
      by_cases hr : rowHits r (records M x) = 1 <;>
        simpa [hr] using runRow padded [] (records M x) r f) ticks ht
  by_cases he : ∀ r, ∃! i, x i = true ∧ M r i = true <;>
    simpa [hits_records, exactOne, he] using h

/-- For fixed row count, the required source length is linear in the number of columns. -/
theorem weighted_projection {R V : Type*} [CommRing R] {m k : ℕ}
    (M : Fin m → Fin k → Bool) (w : Projection R (Fin k) V) (n : ℕ)
    (hn : 1000000 * (m + 1)^4 + k * (m + 2) + 1 ≤ n) :
    ∃ φ : Projection R (Fin n × Bool) V,
      φ.hom (MvPolynomial.map (Int.castRingHom R) (P n)) = weightedPredicate (exactOne M) w := by
  let pre := programPrefix (machine m)
  let pad := List.replicate (n - (pre.length + k*(m+2)+1)) false
  let padded := pre ++ pad
  let layout := recordLayout padded (fun i => List.ofFn (fun r => M r i))
  have hp : pre.length ≤ 1000000 * (m+1)^4 := programLength_le m
  have hlen : layout.length = n := by
    rw [show layout.length = _ from length_recordLayout padded M]
    simp only [padded, pad, List.length_append, List.length_replicate]
    omega
  have hpre : m+2 ≤ padded.length := by
    have hc : (machine m).extra = Fintype.card (State m) := rfl
    have hs : m+1 ≤ (machine m).extra := by rw [hc, card_state]; omega
    exact (queryPrefix_lower hs).trans (by simp [padded, pre])
  rw [← hlen]
  apply InterleavedPinning.weighted_projection layout.get (recordLayout_unique padded _) (exactOne M) w
  intro x
  have hf : List.ofFn (fill layout.get x) = padded ++ (rowBits (records M x)).reverse :=
    fill_records padded M x
  have hd : decode (padded ++ (rowBits (records M x)).reverse) = some (machine m) := by
    simp [padded, pre, List.append_assoc, decode_programPrefix]
  have hwhole : (padded ++ (rowBits (records M x)).reverse).length = layout.length := by
    simpa only [List.length_ofFn] using (congrArg List.length hf).symm
  have htime : m * ((padded ++ (rowBits (records M x)).reverse).length +
      (rowBits (records M x)).length + 1) + 1 ≤ layout.length ^ clockExponent := by
    rw [hwhole]
    apply querySteps_le_clock (ℓ := padded.length) _ hpre
    rw [← hwhole]
    simp
  simp only [acceptingCount, hf, hd]
  exact correct padded M x _ htime

end IncidenceMachine

end VPVNP
end Computability
end OAI
