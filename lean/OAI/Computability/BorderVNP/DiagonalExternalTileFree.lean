import OAI.Computability.BorderVNP.DiagonalExternalTileLookup

/-! # Convexity of the free literal and pin lanes within one initial block -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.TileRuns

variable {R r w link g : ℕ}
local notation "stride" => 2*w+R*link

private theorem free_outside (f : FreePort R r w) (p : Fin r) :
    (teamOrdinal (port R r w link g (.inl f))).val < p.val*stride+w ∨
    p.val*stride+w+R*link ≤ (teamOrdinal (port R r w link g (.inl f))).val := by
  obtain ⟨u,t,z⟩ := f
  have before (h : t < p) : (t.val+1)*stride ≤ p.val*stride :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h)
  have after (h : p < t) : (p.val+1)*stride ≤ t.val*stride :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h)
  rcases z with z | z
  · change (teamOrdinal (publicPortEquiv R r w link (.inl (u,t,.inl z)))).val < _ ∨ _ ≤ (teamOrdinal (publicPortEquiv R r w link (.inl (u,t,.inl z)))).val
    rw [publicPortEquiv_literal,teamOrdinal_val]
    dsimp only
    have hz := z.isLt
    rcases lt_trichotomy t p with h | rfl | h
    · have hb := before h; rw [Nat.succ_mul] at hb; omega
    · omega
    · have hb := after h; rw [Nat.succ_mul] at hb; omega
  · change (teamOrdinal (publicPortEquiv R r w link (.inl (u,t,.inr z)))).val < _ ∨ _ ≤ (teamOrdinal (publicPortEquiv R r w link (.inl (u,t,.inr z)))).val
    rw [publicPortEquiv_pin,teamOrdinal_val]
    dsimp only
    have hz := z.isLt
    rcases lt_trichotomy t p with h | rfl | h
    · have hb := before h; rw [Nat.succ_mul] at hb; omega
    · omega
    · have hb := after h; rw [Nat.succ_mul] at hb; omega

private theorem cable_inside (s : Bool) (c : Cables R r w link g) (j : Fin (cableWidth c)) :
    let a := (teamOrdinal (port R r w link g (.inr (s,⟨c,j⟩)))).val
    c.1.2.val*stride+w ≤ a ∧ a < c.1.2.val*stride+w+R*link := by
  change _ ≤ (teamOrdinal (publicPortEquiv R r w link (.inr (s,c.1.1,c.1.2,pieceOffset _ _ c j)))).val ∧
    (teamOrdinal (publicPortEquiv R r w link (.inr (s,c.1.1,c.1.2,pieceOffset _ _ c j)))).val < _
  rw [publicPortEquiv_exterior,teamOrdinal_val]
  have rank := Nat.mul_le_mul_right link (Nat.succ_le_of_lt (fieldRank c.1.1 s).isLt)
  rw [Nat.succ_mul] at rank
  have hj := (pieceOffset _ _ c j).isLt
  dsimp only
  omega

/-- Literal and pin ranges form at most one free run inside a tile no wider than a partner field.
The pin suffix of one processor and the literal prefix of the next use consecutive free lanes. -/
theorem free_between (small : g ≤ link) (u : Fin (R+1)) (tile : ℕ) {i j k : Fin g} (hi : i ≤ j) (hk : j ≤ k)
    (a b : FreePort R r w)
    (ha : lookup (link := link) u tile i = some (.inl a)) (hb : lookup (link := link) u tile k = some (.inl b)) :
    ∃ f : FreePort R r w, lookup (link := link) u tile j = some (.inl f) := by
  obtain ⟨_,eA⟩ := (lookup_some ..).mp ha
  obtain ⟨_,eB⟩ := (lookup_some ..).mp hb
  have hi' : i.val ≤ j.val := hi
  have hk' : j.val ≤ k.val := hk
  cases H : lookup (r := r) (w := w) (link := link) u tile j with
  | none =>
    have h := (lookup_none ..).mp H
    have hB := (teamOrdinal (port R r w link g (.inl b))).isLt
    omega
  | some f =>
    rcases f with f | ⟨s,c,t⟩
    · exact ⟨f,rfl⟩
    obtain ⟨_,eT⟩ := (lookup_some ..).mp H
    obtain ⟨t₁,t₂⟩ := cable_inside s c t
    obtain left | left := free_outside (link := link) (g := g) a c.1.2 <;>
      obtain right | right := free_outside (link := link) (g := g) b c.1.2
    all_goals
      have hR := (fieldRank c.1.1 s).isLt
      have cap := Nat.mul_le_mul_right link (show 1 ≤ R by omega)
      rw [Nat.one_mul] at cap
      have fit := k.isLt
      omega

end Diagonal.ExternalSew.TileRuns

end BorderVNP
end Computability
end OAI
