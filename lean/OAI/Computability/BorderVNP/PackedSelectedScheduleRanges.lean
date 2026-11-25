import OAI.Computability.BorderVNP.DiagonalEpochScales
import OAI.Computability.BorderVNP.PackedHistoryRectangles
import OAI.Computability.BorderVNP.ShortenPublicBottomCapacity
import OAI.Computability.BorderVNP.ShortenPublicWordRange
import OAI.Computability.BorderVNP.ShortenPublicSelectorWord
import OAI.Computability.BorderVNP.PackedRoundProfiles

/-! # Public ranges for the actual selected combining stages

The starting rectangle belongs to the repeated bottom grid, whose repetition
increases widths. Every subdivision and all copies at each combining node
then determine the successor rectangle. The fixed source path gives the
literal number of seeds at every stage, including both the absolute tile
address and the relative bin. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Cover.AddressCircuit Epoch Packing Shortening PublicCapacity Diagonal TeamScales Filter
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- Largest number of relative bins in the fixed source path. -/
noncomputable def bins := Finset.univ.sup fun i => Fintype.card (S.source.pattern i).bins.Bin

/-- Subdivision capacity for a route at the site's prescribed move budget. -/
noncomputable def interiors := ⌈S.budget/S.radius⌉₊

/-- The depth on the scheduled path just before stage number j. -/
noncomputable def stageLevel (start t j : ℕ) :=
  let word := fun i => (S.source.pattern i).word
  Adaptive.Levels.level word (terminalDepth word S.last start t) S.last j

/-- Number of rows in the full seed-by-bin directory at a combining stage. -/
noncomputable def seedCount (start t j : ℕ) : ℕ :=
  if h : j<S.rounds then Fintype.card (Cube D → Deck (stageLevel S start t (j+1)+1)) *
    Fintype.card (S.source.pattern ⟨j,h⟩).bins.Bin else 0

/-- Initial reserved sites and cables of the repeated public grid. -/
noncomputable def bottom (start : ℕ) := gridShape (CoverScale.sites (Cube D) start)
  (Fintype.card (DeckGrid.Direction (Fintype.card (Cube D))))

/-- The exact geometry rectangle of one child at a public combining node. -/
noncomputable def before (start t j : ℕ) :=
  let seeds := seedCount S start
  let incoming := epochRows e S.fanIn S.rounds (interiors S) seeds (bottom (D := D) start) t
  combineRows e S.fanIn (seeds t) (incoming.subdivide (interiors S)) j

/-- The next public rectangle follows the literal template allocation. -/
theorem before_next (start t j : ℕ) : before S start t (j+1) =
    ((before S start t j).parallel S.fanIn).sew e (seedCount S start t j) := rfl

/-- The actual relative bin cardinal at every tile fits the fixed source maximum. -/
theorem seeds_le (start : ℕ) (levels : ∀ (t : ℕ) (j : Fin S.rounds), stageLevel S start t (j.val+1)+1 ≤ start+1)
    (t j : ℕ) : seedCount S start t j ≤ CoverScale.sites (Cube D) start * bins S := by
  by_cases h : j<S.rounds
  · simp only [seedCount,dite_eq_left h]
    exact Nat.mul_le_mul (tiles_mono (Cube D) (levels t ⟨j,h⟩)) (Finset.le_sup (f := fun i => Fintype.card (S.source.pattern i).bins.Bin) (Finset.mem_univ (⟨j,h⟩ : Fin S.rounds)))
  · simp [seedCount,h]

/-- All padded identifiers and words needed by a selected kernel at its
actual scheduled rectangle, with one processor word for both pointers and scores. -/
structure Ranges (r n start t : ℕ) (j : Fin S.rounds) (den cut : ℕ) : Prop where
  /-- Admissible auxiliary depth and selector cutoff. -/
  depth : ∃ d : ℕ, 1≤d ∧ stageLevel S start t (j.val+1)+1 = d+2*(S.source.pattern j).word ∧
    (S.source.pattern j).floor ≤ stageLevel S start t (j.val+1) ∧ cut ≤ stageLevel S start t j.val+1
  /-- The incoming level is exactly two prepared word lengths above the output level. -/
  step : stageLevel S start t j.val = stageLevel S start t (j.val+1)+2*(S.source.pattern j).word
  /-- Score denominators, counts, site rows, seed rows and the two successor name spaces fit. -/
  words :
    let vol := CoverScale.sites (Cube D) (stageLevel S start t (j.val+1))
    let sub := (before S start t j).parallel S.fanIn
    let next := before S start t (j.val+1)
    let W := (2*n*r)^2
    let w := 60*logWidth r n
    let T := 2^w
    den<T ∧ S.fanIn*W<T ∧ packRunWidth vol den S.fanIn W ≤ w ∧
      sub.sites ≤ T ∧ sub.edges ≤ T ∧ seedCount S start t j ≤ T ∧ next.sites ≤ T ∧ next.edges ≤ T ∧
      Nat.clog 2 (DirectoryCircuit.widthMultiplier e*(S.fanIn*W)+1) ≤ w ∧
      w ≤ Nat.clog 2 (T+1) ∧ Nat.clog 2 (T+vol+2)+1 ≤ 63*logWidth r n
  /-- The tile rectangle at this stage is a quotient of the original one. -/
  tiles : CoverScale.sites (Cube D) (stageLevel S start t (j.val+1)) ≤ CoverScale.sites (Cube D) start

/-- The complete selector range holds at every internal node of every epoch
for all sufficiently large lengths, uniformly over the processor count. -/
theorem eventually_ranges {a x : ℕ} (s : EpochScales S a x) (den cut : Fin S.rounds → ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      (∀ t j, seedCount S start t j ≤ CoverScale.sites (Cube D) start * bins S) ∧
      ∀ t < epochs s.τ n, ∀ j : Fin S.rounds, Ranges S r n start t j (den j) (cut j) := by
  let word := fun i => (S.source.pattern i).word
  let lim := Finset.univ.sup fun i => cut i + (S.source.pattern i).floor + 2*word i + 2
  let dirs := Fintype.card (DeckGrid.Direction (Fintype.card (Cube D)))
  have ht : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have cover := s.rate (epochCoverLoss_pos S) (epochGrowth_bounds S x).2.2.1
  have cover' : (s.τ:ℝ)*Real.logb 2 ((CoverScale.factor (Cube D):ℝ)^S.drop) ≤ (s.α:ℝ)/10 := by
    simpa only [epochCoverLoss,Nat.cast_pow] using cover
  have small : (s.α:ℝ)/10 < 9/10 := by linarith [s.alpha_small]
  have stages := eventually_schedule_levels word S.last (Cube D) lim ht.le cover' small
  have rowRate := s.rate (epochFactor_pos e S.positiveFanIn S.rounds (interiors S) (bins S))
    (epochGrowth_bounds S x).2.2.2.2.1
  let A : ℝ := dirs+3
  have rowNames := eventually_row_names e S.positiveFanIn S.rounds (interiors S) (bins S)
    s.alpha_small ht.le rowRate A
  have large := ((tendsto_rpow_atTop (show 0 < (9/10 : ℝ) by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (CoverScale.sites (Cube D) 1 : ℝ)
  filter_upwards [stages,rowNames,large,eventually_ge_atTop 1,
    eventually_ge_atTop (Finset.univ.sup den),eventually_ge_atTop (bins S),
    eventually_ge_atTop (DirectoryCircuit.widthMultiplier e),eventually_ge_atTop S.fanIn,
    eventually_ge_atTop (sewFactor e (bins S))] with n stage rows base hn hden hbins hmul hk hsew
  intro r hr start
  let V := CoverScale.sites (Cube D) start
  obtain ⟨shallow,depth⟩ := stage r hr
  have tile (t : ℕ) (j : Fin S.rounds) : CoverScale.sites (Cube D) (stageLevel S start t (j.val+1)) ≤ V :=
    tiles_mono (Cube D) (shallow t j)
  have hs := seeds_le S start shallow
  refine ⟨hs,fun t ht' j => ?_⟩
  let lev := stageLevel S start t (j.val+1)
  let sub := (before S start t j).parallel S.fanIn
  let U := 2*n*r
  let L := logWidth r n
  have hu : 2 ≤ U := by dsimp [U]; nlinarith [Nat.mul_le_mul hn hr]
  have hnu : n ≤ U := by dsimp [U]; nlinarith [Nat.mul_le_mul_left n hr]
  have hl : 1 ≤ L := by
    rw [show L = Nat.clog 2 U from public_logWidth n r]
    exact (by decide : 1 ≤ Nat.clog 2 2).trans (Nat.clog_mono_right 2 hu)
  have hnR : 1 ≤ (r:ℝ) := by exact_mod_cast hr
  change (CoverScale.sites (Cube D) 1 : ℝ) ≤ (n:ℝ)^(9/10:ℝ) at base
  have scale := (CoverScale.initial_sites (Cube D) (r := r) (n := n)
    (base.trans (le_mul_of_one_le_left (by positivity) hnR))).2
  have initCap : ((bottom (D := D) start).volume V:ℝ) ≤ A*(r*(n:ℝ)^(9/10:ℝ)) := by
    have ini : ((bottom (D := D) start).volume V:ℝ) ≤ (dirs+3:ℝ)*V := by
      exact_mod_cast grid_volume (Fintype.card_pos : 1 ≤ V) dirs
    exact ini.trans (mul_le_mul_of_nonneg_left scale (by positivity))
  have rc : sub.volume V ≤ r*n := rows r V (seedCount S start) (bottom (D := D) start) hs initCap t ht' j.val j.isLt
  have rU : r*n ≤ U := by dsimp [U]; nlinarith
  have oldCap : sub.sites+sub.edges+V+1 ≤ U := (show sub.volume V ≤ U from rc.trans rU)
  have dcap := (Finset.le_sup (f := den) (Finset.mem_univ j)).trans (hden.trans hnu)
  let vol := CoverScale.sites (Cube D) lev
  have vcap := tile t j
  change vol ≤ V at vcap
  obtain ⟨dfit,_,run,edge,site,pad,log⟩ := selector_word_ranges n r vol (den j) S.fanIn (U^2)
    sub.edges sub.sites hn hr (by omega) dcap (hk.trans hnu) le_rfl (by omega) (by omega)
  have uPow : U ≤ 2^L := by rw [show L = Nat.clog 2 U from public_logWidth n r]; exact Nat.le_pow_clog (by decide) _
  have big : U^5 ≤ 2^(60*L) := by
    calc
      _ ≤ (2^L)^5 := Nat.pow_le_pow_left uPow _
      _ ≤ _ := by rw [←pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have score : DirectoryCircuit.widthMultiplier e * (S.fanIn*U^2)+1 ≤ 2^(60*L) := by
    have u4 : DirectoryCircuit.widthMultiplier e*(S.fanIn*U^2) ≤ U*(U*U^2) :=
      Nat.mul_le_mul (hmul.trans hnu) (Nat.mul_le_mul_right _ (hk.trans hnu))
    have inc : U^4+1 ≤ U^5 := by
      rw [show U^5=U^4*U by ring]
      have z := Nat.mul_le_mul_left (U^4) hu
      have p := Nat.one_le_pow 4 U (by omega)
      omega
    exact (Nat.succ_le_succ (u4.trans_eq (by ring))).trans (inc.trans big)
  have μ : 1 ≤ DirectoryCircuit.widthMultiplier e := by unfold DirectoryCircuit.widthMultiplier; omega
  have packed : S.fanIn*U^2 < 2^(60*L) := lt_of_lt_of_le
    (Nat.lt_succ_of_le (Nat.le_mul_of_pos_left _ μ)) score
  have successor := successorPointers_fit e sub V (seedCount S start t j) (bins S) r n hn hr rc (hs t j) hsew
  have lift : 2^(3*L) ≤ 2^(60*L) := Nat.pow_le_pow_right (by decide) (by omega)
  have square : U*U ≤ U^5 := by rw [←sq]; exact Nat.pow_le_pow_right (by omega) (by decide : 2≤5)
  have seedFit : seedCount S start t j ≤ 2^(60*L) := (hs t j).trans
    ((Nat.mul_le_mul (by omega : V ≤ U) (hbins.trans hnu)).trans (square.trans big))
  change Nat.clog 2 (2^(60*L)+vol+2)+1 ≤ 60*L+3 at log
  have log63 := log.trans (by omega : 60*L+3 ≤ 63*L)
  have link := Adaptive.Levels.step word (terminalDepth word S.last start t) S.last j
  change stageLevel S start t j.val + 1 = lev+1+2*word j at link
  have step : stageLevel S start t j.val = lev+2*word j := by omega
  obtain ⟨d,hd,dl,hcut,_⟩ := depth t ht' j
  change d+2*word j = lev+1 at dl
  have floor := Finset.le_sup (f := fun i => cut i+(S.source.pattern i).floor+2*word i+2) (Finset.mem_univ j)
  change lim ≤ d+2*word j+2*word j at hcut
  change cut j+(S.source.pattern j).floor+2*word j+2 ≤ lim at floor
  exact ⟨⟨d,hd,dl.symm,by omega,by omega⟩,step,⟨dfit,packed,run,site,edge,seedFit,
    successor.1.trans lift,successor.2.trans lift,Nat.clog_le_of_le_pow score,pad,log63⟩,vcap⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
