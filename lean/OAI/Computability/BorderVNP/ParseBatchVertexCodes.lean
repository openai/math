import OAI.Computability.BorderVNP.ParseBatchVerifierCountWords
import OAI.Computability.BorderVNP.ParseFanoutBounds

/-! # Short names for vertices and their truth-table rows in Lemma 2.3 -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchVerifier

open ParseBatch ParseBatchCounts

/-- The volume bound of Lemma 2.3 permits a site and its at most three bits of
input to be addressed with only a fixed constant plus four logarithms. -/
theorem entry_address_capacity (m r : ℕ) :
    8 * (180000000 * (m*r) * (Nat.clog 2 (2*m*r)+3)^3) ≤
      2 ^ (38 + 4 * Nat.clog 2 (2*m*r)) := by
  let l := Nat.clog 2 (2*m*r)
  have hmr : m*r ≤ 2^l := (show m*r ≤ 2*m*r by nlinarith).trans (Nat.le_pow_clog (by decide) _)
  have hl : l + 3 ≤ 4 * 2^l := by have := l.lt_two_pow_self; have := Nat.two_pow_pos l; omega
  calc
    _ ≤ 8 * (180000000 * (2^l) * (4 * 2^l)^3) := by gcongr
    _ = (8*180000000*64) * (2^l)^4 := by ring
    _ ≤ (2^38) * (2^l)^4 := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by rw [pow_add, Nat.mul_comm 4 _, pow_mul]

/-- A truth-table row is a site with one Boolean value for each of its incident
endpoints. This includes external pins in the count. -/
abbrev Entry {X W T : Type} [Fintype X] [Fintype W] [Fintype T] (L : Layout X W T) :=
  Σ v : L.Site, {e : L.Endpoint // L.incident e = v} → Bool

open scoped Classical in
/-- A physical table entry has an injective binary identifier of logarithmic
length, including the arguments at the site, in every batch network satisfying
the proved volume and degree bounds. -/
theorem entry_encoding {X W T : Type} [Fintype X] [Fintype W] [Fintype T] (L : Layout X W T)
    (m r : ℕ) (hvol : Fintype.card L.Site ≤ 180000000*(m*r)*(Nat.clog 2 (2*m*r)+3)^3)
    (hdeg : ∀ v : L.Site, (Finset.univ.filter fun e : L.Endpoint => L.incident e = v).card ≤ 3) :
    Nonempty (Entry L ↪ (Fin (38 + 4*Nat.clog 2 (2*m*r)) → Bool)) := by
  classical
  let (v : L.Site) : Fintype {e : L.Endpoint // L.incident e = v} := Fintype.ofFinite _
  have hentry : Fintype.card (Entry L) ≤ 8 * Fintype.card L.Site := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _v : L.Site, 8 := by
        apply Finset.sum_le_sum
        intro v _
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype]
        exact (Nat.pow_le_pow_right (by decide : 0 < 2) (hdeg v)).trans_eq (by decide)
      _ = 8 * Fintype.card L.Site := by simp [Nat.mul_comm]
  have bound := hentry.trans ((Nat.mul_le_mul_left _ hvol).trans (entry_address_capacity m r))
  exact ⟨(Fintype.equivFin (Entry L)).toEmbedding.trans
    ((Fin.castLEEmb bound).trans (numberWords _).symm.toEmbedding)⟩

end ParseBatchVerifier

end BorderVNP
end Computability
end OAI
