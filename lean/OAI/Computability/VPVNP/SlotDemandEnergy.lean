import OAI.Computability.VPVNP.SlotBundleCount
import OAI.Computability.VPVNP.WidthRounding
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Energy of the packed demand wires

The first inequality of §7.2 charges every actual wire exactly once. In a
thick–thick bundle the old payloads are concatenated and divided as evenly
as possible among its assigned motifs. Each remaining wire retains its old
width in the CD demand of its motif.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

variable {V H Tag L : Type*} {d c : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- The number Q of pieces in each concatenated payload. -/
abbrev pieceCount (d c : ℕ) := 3 * (2 ^ c * d) / 4

/-- Number the motifs assigned to each bundle in the common order used at A and B. -/
abbrev BundleNumbering :=
  ∀ b : Site V Tag L × Fin d, {m : P.Motif // P.bundle m = b} ≃ Fin (pieceCount d c)

/-- The original wires concatenated at A and B. -/
abbrev ThickWire := {a : Arc V H Tag L d c //
  P.thick (sourcePosition a) ∧ P.thick (sourcePosition (P.actual a))}

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

/-- Lemma C.1 supplies an ordering with exactly Q pieces in each bundle. -/
noncomputable def bundleNumbering (hc : 2 ≤ c) : P.BundleNumbering :=
  fun b ↦ Fintype.equivFinOfCardEq (P.card_motifs_bundle hc b)

/-- Total number of bits in the concatenation, before rounding. -/
def bundleWidth (w : Arc V H Tag L d c → ℕ) (b : Site V Tag L × Fin d) : ℕ :=
  ∑ a : {a : P.ThickWire // a.1.1 = b}, w a.1.1

/-- Width of the AB wire paired with the unchanged CD wire of a motif. -/
def abWidth (number : P.BundleNumbering) (w : Arc V H Tag L d c → ℕ) (m : P.Motif) : ℕ :=
  splitWidth (P.bundleWidth w (P.bundle m)) (pieceCount d c) (number (P.bundle m) ⟨m,rfl⟩)

private theorem abWidth_at (number : P.BundleNumbering) (w : Arc V H Tag L d c → ℕ)
    (b : Site V Tag L × Fin d) (m : {m : P.Motif // P.bundle m = b}) :
    P.abWidth number w m.1 = splitWidth (P.bundleWidth w b) (pieceCount d c) (number b m) := by
  rcases m with ⟨m, hm⟩
  subst b
  rfl

/-- Number of thick–thick wires over each original bundle. -/
theorem card_thick_fiber (hc : 2 ≤ c) (b : Site V Tag L × Fin d) :
    Fintype.card {a : P.ThickWire // a.1.1 = b} = 2 ^ c * d / 4 := by
  let e : {a : P.ThickWire // a.1.1 = b} ≃ {a : Arc V H Tag L d c //
    a.1 = b ∧ P.thick (sourcePosition a) ∧ P.thick (sourcePosition (P.actual a))} :=
    { toFun := fun a ↦ ⟨a.1.1, a.2, a.1.2⟩
      invFun := fun a ↦ ⟨⟨a.1,a.2.2⟩,a.2.1⟩ }
  exact (Fintype.card_congr e).trans (P.card_thick_bundle hc b)

private theorem pieces_arithmetic (hc : 2 ≤ c) (hd : 0 < d) :
    pieceCount d c = 3 * (2 ^ c * d / 4) ∧ 0 < pieceCount d c := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hc
  have h : 2 ^ (2 + n) * d = 4 * (2 ^ n * d) := by rw [pow_add]; ring
  have hp : 0 < 2 ^ n * d := Nat.mul_pos (pow_pos (by decide) _) hd
  simp only [pieceCount, h]
  omega

/-- Concatenation uses at most the number of bundled wires times the maximum old width. -/
theorem bundleWidth_le (hc : 2 ≤ c) (w : Arc V H Tag L d c → ℕ) {W : ℕ}
    (hw : ∀ a, w a ≤ W) (b : Site V Tag L × Fin d) :
    P.bundleWidth w b ≤ (2 ^ c * d / 4) * W := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun a : {a : P.ThickWire // a.1.1 = b} ↦ fun _ ↦ hw a.1.1)
  simpa [bundleWidth, P.card_thick_fiber hc] using h

/-- The individual AB pieces are no wider than the largest old wire. -/
theorem abWidth_le (hc : 2 ≤ c) (hd : 0 < d) (number : P.BundleNumbering)
    (w : Arc V H Tag L d c → ℕ) {W : ℕ} (hw : ∀ a, w a ≤ W) (m : P.Motif) :
    P.abWidth number w m ≤ W := by
  let b := P.bundleWidth w (P.bundle m)
  let q := pieceCount d c
  have hq : 0 < q := (pieces_arithmetic hc hd).2
  have hk : 2 ^ c * d / 4 ≤ q := by dsimp [q]; rw [(pieces_arithmetic hc hd).1]; omega
  have hb : b ≤ W * q := (P.bundleWidth_le hc w hw _).trans
    ((Nat.mul_le_mul_right W hk).trans_eq (Nat.mul_comm q W))
  change splitWidth b q _ ≤ W
  unfold splitWidth
  split_ifs with h
  · apply (Nat.div_lt_iff_lt_mul hq).mpr
    refine lt_of_le_of_ne hb ?_
    rintro he
    simp [he] at h
  · exact Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hb)

/-- Concatenation followed by the Q-way division preserves the payload width. -/
theorem sum_abWidth (hc : 2 ≤ c) (hd : 0 < d) (number : P.BundleNumbering)
    (w : Arc V H Tag L d c → ℕ) (b : Site V Tag L × Fin d) :
    ∑ m : {m : P.Motif // P.bundle m = b}, P.abWidth number w m.1 = P.bundleWidth w b := by
  simp_rw [P.abWidth_at number w b]
  rw [(number b).sum_comp]
  exact sum_splitWidth _ _ (pieces_arithmetic hc hd).2

/-- The bundle's perfect fractional division inherits the total old mass.
Integral division incurs at most Q/(4(p/3)) additional energy. -/
theorem bundle_energy_le (hc : 2 ≤ c) (hd : 0 < d) (number : P.BundleNumbering)
    (w : Arc V H Tag L d c → ℕ) {p : ℝ} (hp : 0 < p) (b : Site V Tag L × Fin d) :
    ∑ m : {m : P.Motif // P.bundle m = b}, (P.abWidth number w m.1 : ℝ) ^ 2 / (p / 3) ≤
      ∑ a : {a : P.ThickWire // a.1.1 = b}, (w a.1.1 : ℝ) ^ 2 / p +
        pieceCount d c / (4 * (p / 3)) := by
  have hs := Finset.sq_sum_div_le_sum_sq_div Finset.univ
    (fun a : {a : P.ThickWire // a.1.1 = b} ↦ (w a.1.1 : ℝ))
    (g := fun _ ↦ p) (fun _ _ ↦ hp)
  have hm : (pieceCount d c : ℝ) * (p / 3) = (↑(2 ^ c * d / 4 : ℕ) : ℝ) * p := by
    rw [(pieces_arithmetic hc hd).1, Nat.cast_mul, Nat.cast_ofNat]
    ring
  simp only [Finset.sum_const, Finset.card_univ, P.card_thick_fiber hc, nsmul_eq_mul] at hs
  simp_rw [P.abWidth_at number w b]
  rw [(number b).sum_comp (fun i ↦ (splitWidth (P.bundleWidth w b) (pieceCount d c) i : ℝ) ^ 2 /
    (p / 3))]
  calc
    _ ≤ (P.bundleWidth w b : ℝ) ^ 2 / (pieceCount d c * (p / 3)) +
        pieceCount d c / (4 * (p / 3)) :=
      splitWidth_energy_le _ _ (pieces_arithmetic hc hd).2 _ (by positivity)
    _ ≤ _ := by rw [hm]; exact add_le_add_left (by simpa [bundleWidth] using hs) _

/-- Total demand energy at the actual masses p/3 and p, before any supply
substitution. The last term is the per-bundle integral rounding cost. -/
theorem demand_energy_le (hc : 2 ≤ c) (hd : 0 < d) (number : P.BundleNumbering)
    (w : Arc V H Tag L d c → ℕ) {p : ℝ} (hp : 0 < p) :
    (∑ m : P.Motif, ((P.abWidth number w m : ℝ) ^ 2 / (p / 3) + (w m.1 : ℝ) ^ 2 / p)) ≤
      (∑ a : Arc V H Tag L d c, (w a : ℝ) ^ 2 / p) +
        Fintype.card (Site V Tag L × Fin d) * (pieceCount d c : ℝ) / (4 * (p / 3)) := by
  let E := fun a : Arc V H Tag L d c ↦ (w a : ℝ) ^ 2 / p
  have h := Finset.sum_le_sum (s := Finset.univ) (fun b _ ↦ P.bundle_energy_le hc hd number w hp b)
  rw [Fintype.sum_fiberwise P.bundle (fun m ↦ (P.abWidth number w m : ℝ) ^ 2 / (p / 3)),
    Finset.sum_add_distrib, Fintype.sum_fiberwise (fun a : P.ThickWire ↦ a.1.1)
      (fun a ↦ (w a.1 : ℝ) ^ 2 / p)] at h
  have hall : (∑ a : P.ThickWire, E a.1) + (∑ m : P.Motif, E m.1) = ∑ a, E a :=
    Fintype.sum_subtype_add_sum_subtype _ E
  rw [Finset.sum_add_distrib]
  change _ + (∑ m : P.Motif, E m.1) ≤ (∑ a, E a) + _
  rw [← hall, add_right_comm]
  apply add_le_add_left
  simpa [Finset.sum_const, mul_div_assoc] using h

end Compression.PackingData

end VPVNP
end Computability
end OAI
