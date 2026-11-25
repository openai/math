import OAI.Computability.BorderVNP.PackedDirectoryOccupiedRoom
import OAI.Computability.BorderVNP.ShortenPublicPaddedWords
import OAI.Computability.BorderVNP.PackedInitialLayout

/-! # Word width of the real native directory traversal

The public array bases lie in the allocated workspace. Private descriptions occupy
reserved processor tails, and the cell report address gap is at most quadratic in the
processor size. These bounds suffice at the logarithmic native word width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.ISA

open TeamScales

private theorem rounded_le_length {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : a ≤ 1) : width n a ≤ n := by
  apply Nat.floor_le_of_le
  exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) ha).trans_eq (Real.rpow_one _)

/-- The scalar room, including every original placement offset and live lookup,
follows from the actual rounded field lengths, the reserved directory tails, and the
two public workspace base addresses. -/
theorem directory_slot_word_room {slots : ℕ} {n r pb lb gap W : ℕ} {α ξ : ℝ} (dir : Layout) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hα : 0 ≤ α) (hξ : 0 ≤ ξ) (teams : dir.teams ≤ n) (proc : dir.processors = r)
    (fields : dir.fields ≤ 2) (lit : dir.literal = literal α n) (linkEq : dir.link = link ξ dir.teams n)
    (sites : r ≤ dir.sites) (cover : dir.sites ≤ r*n) (block : dir.block = Packing.blockWidth slots dir.sites)
    (posSlots : 0 < slots) (literalSlots : r*dir.literal ≤ slots) (slotCap : slots ≤ r*n)
    (desc : dir.description ≤ dir.literal/2) (entries : dir.entries ≤ dir.teams*dir.sites)
    (tails : dir.entries*dir.description ≤ dir.teams*r*(dir.literal/2))
    (bases : pb ≤ 2*r*n ∧ lb ≤ 2*r*n) (extra : gap ≤ n^2) (word : 16*(logWidth r n+2) ≤ W) :
    let extent := 3*(r*n)^2
    width n (1/5)+gap+dir.entries*dir.description ≤ extent ∧
      wordBound (placementBound dir pb lb extent) < 2^W := by
  intro extent
  let U := r*n
  have hu : 1 ≤ U := one_le_mul_of_one_le_of_one_le hr hn
  have nU : n ≤ U := Nat.le_mul_of_pos_left _ hr
  have u2 : U ≤ U^2 := by rw [sq]; exact Nat.le_mul_of_pos_right _ hu
  have n2 : n^2 ≤ U^2 := Nat.pow_le_pow_left nU _
  have literalBound : dir.literal ≤ n := lit ▸ rounded_le_length hn (by linarith : 1-α/3 ≤ 1)
  have descBound := desc.trans (Nat.div_le_self ..)
  have tailN := (Nat.div_le_self dir.literal 2).trans literalBound
  have linkBound : (dir.teams-1)*dir.link ≤ n := linkEq ▸
    (exterior_links_le ξ dir.teams n).trans (rounded_le_length hn (by linarith))
  have stride : dir.stride ≤ 3*U := by
    have h := Nat.mul_le_mul fields (literalBound.trans nU)
    change dir.fields*dir.literal+(dir.teams-1)*dir.link ≤ _
    omega
  have teamSites : dir.teams*dir.sites ≤ U^2 := by rw [sq]; exact Nat.mul_le_mul (teams.trans nU) cover
  have total : dir.entries*dir.description ≤ U^2 := by
    refine tails.trans ?_
    rw [Nat.mul_assoc,sq]
    exact Nat.mul_le_mul (teams.trans nU) (Nat.mul_le_mul_left r tailN)
  have sitesPos : 0 < dir.sites := hr.trans sites
  have blockBounds : 0 < dir.block ∧ dir.block ≤ U := by
    rw [block]
    have fits : slots ≤ dir.sites * Packing.blockWidth slots dir.sites := (ceilDiv_le_iff_le_mul sitesPos).mp le_rfl
    have pos : 0 < Packing.blockWidth slots dir.sites := by
      by_contra! h
      have : Packing.blockWidth slots dir.sites = 0 := by omega
      rw [this,Nat.mul_zero] at fits
      omega
    exact ⟨pos,(ceilDiv_le_iff_le_mul sitesPos).mpr (slotCap.trans (Nat.le_mul_of_pos_left _ sitesPos))⟩
  have candidate : dir.candidates ≤ 8*U^2 := by
    apply (dir.candidates_le blockBounds.1 fields ?_ (proc ▸ sites) entries).trans (Nat.mul_le_mul_left _ teamSites)
    rw [proc,block]
    exact literalSlots.trans ((ceilDiv_le_iff_le_mul sitesPos).mp le_rfl)
  have locals : width n (1/5)+gap+dir.entries*dir.description ≤ extent := by
    have wsmall := rounded_le_length hn (by norm_num : (1/5:ℝ) ≤ 1)
    change _ ≤ 3*U^2
    omega
  refine ⟨locals,?_⟩
  have bb : placementBound dir pb lb extent ≤ 32*U^2 := by
    dsimp only [placementBound]
    have hp : pb ≤ 2*U := by simpa only [U,Nat.mul_assoc] using bases.1
    have hl : lb ≤ 2*U := by simpa only [U,Nat.mul_assoc] using bases.2
    have ext : extent = 3*U^2 := rfl
    rw [ext]
    omega
  let L := logWidth r n
  have ul : U ≤ 2^L := by
    rw [show L = Nat.clog 2 (2*n*r) from Shortening.PublicCapacity.public_logWidth ..]
    exact (show U ≤ 2*n*r by dsimp [U]; nlinarith).trans (Nat.le_pow_clog (by decide) _)
  have small : placementBound dir pb lb extent < 2^(2*L+6) := by
    have square := Nat.pow_le_pow_left ul 2
    rw [←pow_mul,Nat.mul_comm L 2] at square
    rw [pow_add]
    norm_num
    have pos := Nat.two_pow_pos (2*L)
    omega
  exact placement_word_room small (by change 16*(L+2) ≤ W at word; omega)

/-- The full rectangular processor slot reservation also satisfies the native word bound. -/
theorem directory_word_room {n r pb lb gap W : ℕ} {α ξ : ℝ} (dir : Layout) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hα : 0 ≤ α) (hξ : 0 ≤ ξ) (teams : dir.teams ≤ n) (proc : dir.processors = r)
    (fields : dir.fields ≤ 2) (lit : dir.literal = literal α n) (linkEq : dir.link = link ξ dir.teams n)
    (sites : r ≤ dir.sites) (cover : dir.sites ≤ r*n) (block : dir.block = Packing.blockWidth (r*n) dir.sites)
    (desc : dir.description ≤ dir.literal/2) (entries : dir.entries ≤ dir.teams*dir.sites)
    (tails : dir.entries*dir.description ≤ dir.teams*r*(dir.literal/2))
    (bases : pb ≤ 2*r*n ∧ lb ≤ 2*r*n) (extra : gap ≤ n^2) (word : 16*(logWidth r n+2) ≤ W) :
    let extent := 3*(r*n)^2
    width n (1/5)+gap+dir.entries*dir.description ≤ extent ∧
      wordBound (placementBound dir pb lb extent) < 2^W := by
  have hLit : dir.literal ≤ n := lit ▸ rounded_le_length hn (by linarith : 1-α/3 ≤ 1)
  exact directory_slot_word_room dir hn hr hα hξ teams proc fields lit linkEq sites cover block
    (Nat.mul_pos hr hn) (Nat.mul_le_mul_left r hLit) le_rfl desc entries tails bases extra word

end Packing.Directory.ISA

end BorderVNP
end Computability
end OAI
