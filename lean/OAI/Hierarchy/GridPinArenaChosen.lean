import OAI.Hierarchy.GridPinArenaRoom
import OAI.Hierarchy.GridBandwidth
import OAI.Hierarchy.GridTraceCap
import OAI.Hierarchy.TraceRecordScale
import OAI.Hierarchy.TraceSeedDirectories
import OAI.Hierarchy.TracePhysicalSiteCount

namespace OAI
/-! # Pin-publisher room for the terminal factors of the selected native trace -/

namespace Hierarchy.GridPinArena

open ThreeFlat Diagonal Diagonal.PhysicalStage
open GridScale Filter TraceDistribution
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.RAMMemory
open scoped Classical

variable {F : Type} [Field F]

/-- The publisher uses only the final row count from the public trace geometry. -/
theorem chosen_count [Fintype F] (B : Block F) {Q : ℕ → ℕ} {D : ℕ → ℝ}
    (env : Envelopes Q D) (k A c : ℕ) (hk : 0<k) (q : ℕ → ℕ)
    (range : ∀ᶠ w : ℕ in atTop, 0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop, let a := overhead Q D w
      let u := evalDepth w k A c a (q w)
      let passes := traceBlocks k a
      ∀ (axes pc regs words S base fuel nparams text : ℕ)
        (_dim : axes+1=u+1-w/2) (_axesFit : 2≤axes+1)
        (M : Machine (64*w) pc regs words)
        (_fit : NativeTrace.Fits M S base ((axes+1)+w/2) fuel)
        (N : ℕ) (_sites : N ≤ (axes+1)*2^(axes+1)),
        let full := 2^(axes+1)
        let span := 2*2^(w/2)
        let levels := (B.repeat passes).length
        let cap := pairs A w (q w)
        let P := GridPinPublisher.canonical w k (side a-1) (q w) (pins w a)
          nparams (selector k w a) text cap (external k a cap) S N levels full span
        Small w P S full (levels*full) (classes k w) := by
  have scale := trace_scale env k A c q range
  filter_upwards [range, header_room env k A hk, TraceAdmission.record_room scale (B.levels+1),
    polynomial_room (22^(k+2)) (k+2), polynomial_room (k+2) 0,
    eventually_ge_atTop 2] with w good headers record classPoly dimPoly large
  dsimp only at record ⊢
  intro axes pc regs words S base fuel nparams text dim axesFit M fit N sites
  let a := overhead Q D w
  let passes := traceBlocks k a
  rw [←dim] at record
  change (B.levels+1)*(passes+1)*(1+(axes+1)*2^(axes+1))*(64*w+1) ≤ _ at record
  have core : (B.levels+1)*(passes+1)*(1+(axes+1)*2^(axes+1)) ≤ 2^(3*w/5) :=
    (Nat.le_mul_of_pos_right _ (by omega)).trans record
  have mono : ∀ {a b : ℕ}, a≤b → (2:ℕ)^a≤2^b := fun h => Nat.pow_le_pow_right (by decide) h
  have coreBound := core.trans (mono (show 3*w/5≤w by omega))
  have laneSites : 2^(axes+1) ≤ (axes+1)*2^(axes+1) := Nat.le_mul_of_pos_left _ (by omega)
  have nBound : N ≤ 2^w := by
    exact sites.trans ((Nat.le_add_left _ 1).trans ((Nat.le_mul_of_pos_left _ (by positivity)).trans coreBound))
  have levelBound : (B.repeat passes).length * 2^(axes+1) ≤ 2^w := by
    rw [TraceSeedWriter.repeat_length]
    exact (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.le_succ passes))
      (laneSites.trans (Nat.le_add_left _ 1))).trans coreBound
  have fullBound : 2^(axes+1) ≤ 2^w :=
    laneSites.trans ((Nat.le_add_left _ 1).trans ((Nat.le_mul_of_pos_left _ (by positivity)).trans coreBound))
  have spanBound : 2*2^(w/2) ≤ 2^w := by
    rw [←Nat.pow_succ']
    exact mono (by omega)
  have capacity : S ≤ 2^(axes+1)*(2*2^(w/2)) := by
    calc S ≤ S+fuel := Nat.le_add_right _ _
         _ ≤ _ := fit.grid
         _ = _ := by simp only [pow_add,pow_one]; ring
  have twoBounds : (2:ℕ)^w*2^w ≤ slab w := by
    rw [←pow_add]
    exact mono (show w+w≤16*w by omega)
  have smallOne : (2:ℕ)^w ≤ slab w := mono (show w≤16*w by omega)
  have K : classes k w ≤ 2^w := by
    calc
      _ ≤ (22*(w+1))^(k+2) := Nat.pow_le_pow_left (show 20*(w+1)+2≤22*(w+1) by omega) _
      _ = 22^(k+2)*(w+1)^(k+2) := mul_pow ..
      _ ≤ 2^(w/100) := classPoly
      _ ≤ _ := mono (by omega)
  have widthBound : k+2 ≤ 2^w := (show k+2≤2^(w/100) by simpa using dimPoly).trans (mono (by omega))
  have gridTicks := headers (q w) good.1 good.2 (ticks k a (q w)) (by simp [a])
  have sidePos : 0< side a := Nat.two_pow_pos _
  have sideEq : side a-1+1=side a := by omega
  have headerBound : (2:ℕ)^(2*w+1)*2^w ≤ slab w := by
    rw [←pow_add]; exact mono (show 2*w+1+w≤16*w by omega)
  have pinBound : pins w a ≤ 2^w := mono (Nat.sub_le ..)
  change Small w _ S _ ((B.repeat passes).length*2^(axes+1)) _
  constructor
  · change 0 < (side a-1+1)^k*q w
    rw [sideEq]
    exact gridTicks.1
  · exact Nat.two_pow_pos _
  · change 0 < 2*2^(w/2)
    positivity
  · change (side a-1+1)^k*q w*pins w a ≤ slab w
    rw [sideEq]
    exact (Nat.mul_le_mul gridTicks.2.le pinBound).trans headerBound
  · exact (Nat.mul_le_mul K nBound).trans twoBounds
  · exact (Nat.mul_le_mul nBound widthBound).trans twoBounds
  · exact K.trans smallOne
  · exact (mono (Nat.sub_le w _)).trans smallOne
  · exact capacity.trans ((Nat.mul_le_mul fullBound spanBound).trans twoBounds)
  · exact fullBound.trans smallOne
  · exact levelBound.trans smallOne
  · exact spanBound.trans smallOne
  · exact capacity

/-- At the calibrated ages this covers every real selected history, including the
entire original input bit table, the resource factors and all chronological lane rows. -/
theorem chosen [Fintype F] (B : Block F) {Q : ℕ → ℕ} {D : ℕ → ℝ}
    (env : Envelopes Q D) (k A c : ℕ) (hk : 0<k) (q : ℕ → ℕ)
    (range : ∀ᶠ w : ℕ in atTop, 0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop, let a := overhead Q D w
      let u := evalDepth w k A c a (q w)
      let passes := traceBlocks k a
      ∀ (axes pc regs words S base fuel nparams text : ℕ)
        (_dim : axes+1=u+1-w/2) (axesFit : 2≤axes+1)
        (M : Machine (64*w) pc regs words)
        (fit : NativeTrace.Fits M S base ((axes+1)+w/2) fuel)
        (hf : Fintype.card F≤2^(64*w)) (st : Word (64*w))
        (room : B.blockCharge*passes≤axes+1)
        (h : (Physical.nativeRun B axesFit M fit hf st passes room).plan.History),
        let N := Fintype.card ((Physical.nativeRun B axesFit M fit hf st passes room).plan.finish h).Site
        let full := 2^(axes+1)
        let span := 2*2^(w/2)
        let levels := (B.repeat passes).length
        let cap := pairs A w (q w)
        let P := GridPinPublisher.canonical w k (side a-1) (q w) (pins w a)
          nparams (selector k w a) text cap (external k a cap) S N levels full span
        Small w P S full (levels*full) (classes k w) := by
  filter_upwards [chosen_count B env k A c hk q range] with w run
  dsimp only at run ⊢
  intro axes pc regs words S base fuel np text dim axesFit M fit hf st room h
  exact run axes pc regs words S base fuel np text dim axesFit M fit _
    (Physical.run_sites B axesFit _ _ _ (traceBlocks k (overhead Q D w)) room h)

end Hierarchy.GridPinArena

end OAI
