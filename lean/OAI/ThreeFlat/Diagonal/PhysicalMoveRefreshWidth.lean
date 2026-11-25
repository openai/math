import OAI.ThreeFlat.Diagonal.PhysicalStageBinary
import OAI.ThreeFlat.Diagonal.PhysicalStateWidth
import OAI.ThreeFlat.Diagonal.FixedMotifMaxWidth

namespace OAI
/-! # Maximum edge width of every physical refresh branch -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Expander Computability.VPVNP.Compression CompressorPacking RefreshTies
open scoped BigOperators Classical
noncomputable section

variable {F : Type} [Field F]

/-- The external concatenation has one term per old port. The other charge
is the histogram and selector bound of the fixed refresh table. -/
def refreshWidthFactor {m d₀ : ℕ} {c : Fin m → Fin m → ℕ} {H : ℝ}
    (T : RefreshMotif.Table F c d₀ H) : ℕ :=
  m + (FixedMotifMaxWidth.tile_bound T.base T.block 1).choose

private theorem numbered_width_le {V L : Type} [Fintype V] [Fintype L] {m h : ℕ}
    (c : Fin m → Fin m → ℕ) (rows : ∀ i, ∑ j, c i j=h) (pad : ℕ)
    (w : Address (V × L) m → ℕ) (v : V × L → Arc c → ℕ) (M K : ℕ)
    (hw : ∀ e, w e ≤ M) (hv : ∀ u e, v u e ≤ K*(1+M))
    (e : LiveSlot V L m (1+h+pad)) :
    freshWidth c rows (termWidth c w v) pad e ≤ (m+K)*(1+M) := by
  unfold freshWidth
  rcases (refreshSlots (numbering c rows) pad).symm e with (a | b)
  · rcases a with (⟨u,j⟩ | ⟨u,j⟩)
    · change (∑ i : Fin m, w (u,i,j)) ≤ _
      calc
        _ ≤ ∑ _i : Fin m, M := Finset.sum_le_sum (fun i _ => hw (u,i,j))
        _ = m*M := by simp
        _ ≤ _ := Nat.mul_le_mul (by omega) (by omega)
    · exact (hv u j).trans (Nat.mul_le_mul_right (1+M) (by omega))
  · exact Nat.zero_le _

section General

variable {m lanes hbits rem h pad : ℕ} {c : Fin m → Fin m → ℕ} {H γ : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) H) (A : State m lanes)
    (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
    (hm : 2 ≤ m) (hh : 0 < h) (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h)
    (zero : ∀ i, c i i=0) (conn : Bound (transition c h) ℝ γ)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem refreshMove_width (i : Fin (refreshMove T A u port hm hh sym rows zero conn).rules.count) :
    ((refreshMove T A u port hm hh sym rows zero conn).next i).maxWidth ≤ refreshWidthFactor T*(1+A.maxWidth) := by
  let G := changeLanes A.graph u
  let w := refreshInput A u port
  let cert := FixedMotifMaxWidth.tile_bound T.base T.block 1
  have old (a) : w a ≤ A.maxWidth := A.width_le_maxWidth ((StageAddress.refreshEdge u port).symm a)
  have localBound (z : refreshBranches T A u port) (v : A.Base × BitWord rem) (a : Arc c) :
      T.widths G port w z v a ≤ cert.choose*(1+A.maxWidth) := by
    have profile_le (e) : profile G port w v e ≤ 1*A.maxWidth := by
      simpa only [Nat.one_mul] using old (addr (arrival G port) v e)
    exact cert.choose_spec A.maxWidth (profile G port w v) profile_le (T.winner G port w v) (z v) a
  apply State.maxWidth_le
  intro e
  exact numbered_width_le c rows pad w (T.widths G port w _) A.maxWidth cert.choose old (localBound _) e

end General

section Binary

variable {s rem h pad : ℕ} {H γ : ℝ} {c : Fin (2^s) → Fin (2^s) → ℕ}
    (T : RefreshMotif.Table F c (1+h+pad) H) (A : State (2^s) (s+rem))
    (hm : 2 ≤ 2^s) (hh : 0 < h) (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h)
    (zero : ∀ i, c i i=0) (conn : Bound (transition c h) ℝ γ)

theorem refreshBinary_width (i : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count) :
    ((refreshBinary T A hm hh sym rows zero conn).next i).maxWidth ≤ refreshWidthFactor T*(1+A.maxWidth) :=
  refreshMove_width T A (splitWord s rem) (Native.tagOrdinal s).symm hm hh sym rows zero conn i

end Binary
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
