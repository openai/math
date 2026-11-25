import OAI.Computability.BorderVNP.CubeLabelDirectoryTicks
import OAI.Computability.BorderVNP.PackedDirectoryBits
import OAI.Computability.BorderVNP.PackedGridSlots
import OAI.Computability.BorderVNP.PackedGridRepeat
import OAI.Computability.BorderVNP.ShortenPublicPaddedCapacity

/-! # Counting all source slots, including holes, in the public label clock

The terminal internal cable array contains the reserved bands and bank templates at
every shortening step. The exterior layout reserves up to four intervals per original
team/site pair. Deliveries are the compacted nonempty candidates. The cost uses the
original grid size even when many terminal cells are empty.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open Crossing Shortening Shortening.PublicCapacity Packing TeamScales Filter

/-- A repeated directed Cayley grid uses a single public edge slot per neighbor
and site. Copy multiplicity enlarges widths inside these slots. -/
def gridShape (sites directions : ℕ) : Shape := ⟨sites,sites*directions⟩

/-- Exact site and cable rectangle sizes for the actual initial repeated host. -/
theorem gridShape_physical {D n : ℕ} {P G J : Type} [Group G] [Fintype G] [Fintype J]
    (position : G → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) (step : J → G)
    (input : P ≃ Fin n) (order : Fin (Fintype.card G) ≃ G) (bits : P → ℕ)
    (slots : ℕ) (room : n ≤ slots) (s h b : ℕ) :
    let N := (GridPlacement.publicGridSlots position step input order bits slots room s h).repeatGrid b
    gridShape (Fintype.card G) (Fintype.card J) = ⟨Fintype.card N.Site,Fintype.card N.Edge⟩ := by
  change gridShape (Fintype.card G) (Fintype.card J) = Shape.mk (Fintype.card G) (Fintype.card (G×J))
  simp [gridShape,Fintype.card_prod]

/-- Static public descriptors of one full producer configuration. The count is in
terms of initial tiles, not the number of occupied terminal cells. -/
theorem producer_count {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
    (fan rounds extra dirs bins T V : ℕ) (hf : 1 ≤ fan) (seeds : ℕ → ℕ → ℕ)
    (seed : ∀ t j, seeds t j ≤ V*bins) (d : Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (hb : 0 < d.block) (fields : d.fields ≤ 2) (room : d.processors*d.literal ≤ d.sites*d.block)
    (sites : d.processors ≤ d.sites) (entries : d.entries ≤ d.teams*d.sites) (grid : d.sites = V)
    (l : Layout) (cells : l.cells ≤ V) (ext : ℕ) (extBound : ext ≤ 4*d.teams*V)
    (cableRows : l.cableCount ≤ (epochRows e fan rounds extra seeds (gridShape V dirs) T).edges + ext)
    (del : l.deliveryCount = (d.directory pp lp).length) :
    let M := max ((epochFactor e fan rounds extra bins)^T) d.teams
    1+l.cells+l.cableCount+l.deliveryCount ≤ (dirs+16)*(V+1)*(M+1) := by
  intro M
  have hi := epochRows_le e hf rounds extra V bins seeds seed (gridShape V dirs) T
  have dat := (d.directory_length_le pp lp).trans (d.candidates_le hb fields room sites entries)
  rw [grid,← del] at dat
  let G := epochFactor e fan rounds extra bins
  have gM : G^T ≤ M := le_max_left ..
  have dM : d.teams ≤ M := le_max_right ..
  have hV : (gridShape V dirs).volume V ≤ (dirs+3)*(V+1) := by
    dsimp [gridShape,Shape.volume]; nlinarith
  have edges : (epochRows e fan rounds extra seeds (gridShape V dirs) T).edges ≤ M*((dirs+3)*(V+1)) :=
    (show _ ≤ (epochRows e fan rounds extra seeds (gridShape V dirs) T).volume V by
      unfold Shape.volume; omega).trans (hi.trans (Nat.mul_le_mul gM hV))
  have traffic : d.teams*V ≤ M*V := Nat.mul_le_mul_right V dM
  have all : 1+l.cells+l.cableCount+l.deliveryCount ≤ 1+V+M*((dirs+3)*(V+1))+12*(M*V) := by
    rw [Nat.mul_assoc 4] at extBound
    omega
  apply all.trans
  nlinarith only [Nat.zero_le M,Nat.zero_le V,Nat.zero_le dirs,Nat.zero_le (dirs*V)]

/-- A clock with global rectangle count charged against the *initial* grid,
allowing for compacted or vacant terminal cells. -/
theorem directoryTicks_le_initial (l : Layout) (m : ℕ → ℕ) (z B V M : ℕ) (hz : l.labels = z+1)
    (h : 1+l.cells+l.cableCount+l.deliveryCount ≤ B*(V+1)*(M+1)) :
    directoryTicks l z m ≤ MeanChoice.scanEnvelope (600*B) V M l.labels := by
  apply (directoryTicks_le l m z hz).trans
  have hh := Nat.mul_le_mul (Nat.mul_le_mul_left 600 h)
    (Nat.pow_le_pow_right (show 0 < l.labels+1 by omega) (show 3 ≤ 6 by decide))
  simpa only [MeanChoice.scanEnvelope,Nat.mul_assoc] using hh

/-- The maximal fixed-slot multiplicity per original tile obeys the sparse
power bound, for both shortening templates and exterior team copies. -/
theorem multiplicity_le {α τ : ℝ} {G K n : ℕ} (hn : 1 ≤ n) (hτ : 0 ≤ τ)
    (hα : α ≤ 1/1000) (hG : 1 ≤ G) (hK : 1 ≤ K)
    (growth : τ*Real.logb 2 G ≤ α/10) (fan : τ*Real.logb 2 K ≤ α) :
    ((max (G^epochs τ n) (teams α τ K n) : ℕ) : ℝ) ≤ (n:ℝ)^(1/100 : ℝ) := by
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have g := epoch_growth_le (show 1 ≤ (G:ℝ) by exact_mod_cast hG) hn hτ growth
  have k := teams_le hK hn hτ fan
  rw [Nat.cast_max]
  apply max_le
  · exact_mod_cast g.trans (Real.rpow_le_rpow_of_exponent_le hn' (show α/10 ≤ 1/100 by linarith))
  · exact k.trans (Real.rpow_le_rpow_of_exponent_le hn' (show 2*α ≤ 1/100 by linarith))

/-- The native clock of the rectangular source arrays, even before hole
compaction, is eventually strictly below the public §8.1 clock. -/
theorem eventually_producer_clock {α τ : ℝ} (hα : 0 < α) (a : ℕ) (small : α*a < 1/10^6)
    (hα' : α ≤ 1/1000) (hτ : 0 ≤ τ) (G K B : ℕ) (hG : 1 ≤ G) (hK : 1 ≤ K)
    (growth : τ*Real.logb 2 G ≤ α/10) (fan : τ*Real.logb 2 K ≤ α) :
    ∀ᶠ n : ℕ in atTop, ∀ (r V z : ℕ) (l : Layout) (m : ℕ → ℕ), 1 ≤ r →
      (V:ℝ) ≤ r*(n:ℝ)^(9/10 : ℝ) → l.labels = labelCount α a n → l.labels = z+1 →
      1+l.cells+l.cableCount+l.deliveryCount ≤ B*(V+1)*(max (G^epochs τ n) (teams α τ K n)+1) →
      (directoryTicks l z m : ℝ) < r*(n:ℝ)^(95/100 : ℝ) := by
  filter_upwards [MeanChoice.eventually_scanEnvelope hα a small (600*B) 1,eventually_ge_atTop 1] with n clk hn
  intro r V z l m hr hV Z hz h
  have b := directoryTicks_le_initial l m z B V _ hz h
  rw [Z] at b
  have top := clk r V _ hr (by simpa only [Nat.cast_one,one_mul] using hV)
    (multiplicity_le hn hτ hα' hG hK growth fan)
  apply lt_of_le_of_lt _ top
  exact_mod_cast b

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
