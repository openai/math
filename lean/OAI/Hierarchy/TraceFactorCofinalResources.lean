import OAI.Hierarchy.TraceRegisteredPinFloor
import OAI.Hierarchy.TraceReceiverAge
import OAI.ThreeFlat.Diagonal.PhysicalProgramFreshPrices

namespace OAI
/-! # Fresh terminal resources at the native receiver word width

If the archive clock satisfies `w ≤ age^10` and `16 * age^10 ≤ 64 * w`, every
fixed tile fits the clock and its cubic tariff fits the native receiver's
word width. The receiver age at half the width supplies both bounds for all
sufficiently large widths.
-/

noncomputable section
namespace Hierarchy.TraceDistribution.Physical
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open Filter Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Topology
variable {F : Type} [Field F] [Fintype F] (B : Block F)

omit [Fintype F] in
theorem window_resources_on_lanes {u s : ℕ → ℕ} (scale : Scale u s) (a b : ℕ) (positive : 0<a) :
    ∀ᶠ w : ℕ in atTop, ∀ age : ℕ, w≤age^10 → 16*age^10≤64*w → ∀ (Pins : Type) {lanes : ℕ} (rem low : ℕ) (X : State (2^(B.exponent 0)) lanes)
      (e : lanes=(B.repeat (s w)).charge+rem) (L : X.Words Pins) (N : Forest F L.ports.form)
      (start : X.Site → ℕ),
      low≤w/2 → X.OrderedHalves L → X.maxWidth ≤ 2^low*(a*(w+1)^b) →
      (∀ x,start x≤2^low*(a*(w+1)^b)) →
      (∀ x,1+X.incidentWidth x ≤ start x ∧ L.ports.form.width x≤2*start x ∧ (N x).resources≤ start x) →
      let R := Program.recast e X ((B.repeat (s w)).run rem (e ▸ X))
      let reg := registerOnLanes B Pins (s w) rem X e
      ∀ (h : R.plan.History) (v : (R.plan.finish h).Site),
        ((R.plan.assemble h (R.wordAssembly reg.1.steps L) N).2 v).resources ≤
          ((2*(B.repeat (s w)).length+1)*(B.localCoefficient*(64*w+1)^3))*R.chargeAt h reg.2 start v := by
  filter_upwards [fixed_tile_word_caps B, published_peak_room B scale a b 1 0 positive] with w tiles cap
  intro age fits upperAge Pins lanes rem low X e L N start small ord maxWidth startBound seeds
  subst lanes
  intro R reg h v
  have digits : 2^w ≤ 2^(age^10) := Nat.pow_le_pow_right (by decide : 0 < 2) fits
  have upper := cap rem low 1 X h start small (by simp) maxWidth startBound
  have room : ((B.repeat (s w)).run rem X).LevelsCapped 1 (2^(age^10)) h
      (B.charges (s w) rem X) start := by
    apply ((B.repeat (s w)).run rem X).levels_capped_of_terminal
    intro z
    have exponent : 3*w/5 ≤ age^10 := by omega
    simpa only [publishedWork,Nat.mul_one,Nat.one_mul] using
      (upper z).trans (Nat.pow_le_pow_right (by decide : 0<2) exponent)
  let P := B.repeat (s w)
  let K := B.localCoefficient*(16*age^10+1)^3
  have ge : 2 ≤ K := fresh_price_scale B age
  have prices := B.program_fresh_path (Pins:=Pins) age P (B.repeat_supported _) B.costFactors.sum
    (B.factor_bound _) rem X (fun i => (tiles.1 i).trans digits) (fun i => (tiles.2 i).trans digits) h start room
  have work := R.assembled_resources h reg.1.steps reg.2 (P.certified_floor _ (B.factor_bound _) rem X) L ord N start
    (fun x => (seeds x).1) (fun x => (seeds x).2.1) K ge prices
    (fun x => (seeds x).2.2.trans (Nat.le_mul_of_pos_left _ (by omega : 0<K)))
    P.length (P.stageLength_run rem X) v
  have factor : K ≤ B.localCoefficient*(64*w+1)^3 := Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right upperAge 1) 3)
  exact work.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ factor))

omit [Fintype F] in
theorem cofinal_resources_on_lanes {u s : ℕ → ℕ} (scale : Scale u s) (a b : ℕ) (positive : 0<a) :
    ∀ᶠ w : ℕ in atTop, ∀ age : ℕ, 64*w=16*age^10 → ∀ (Pins : Type) {lanes : ℕ} (rem low : ℕ) (X : State (2^(B.exponent 0)) lanes)
      (e : lanes=(B.repeat (s w)).charge+rem) (L : X.Words Pins) (N : Forest F L.ports.form)
      (start : X.Site → ℕ),
      low≤w/2 → X.OrderedHalves L → X.maxWidth ≤ 2^low*(a*(w+1)^b) →
      (∀ x,start x≤2^low*(a*(w+1)^b)) →
      (∀ x,1+X.incidentWidth x ≤ start x ∧ L.ports.form.width x≤2*start x ∧ (N x).resources≤ start x) →
      let R := Program.recast e X ((B.repeat (s w)).run rem (e ▸ X))
      let reg := registerOnLanes B Pins (s w) rem X e
      ∀ (h : R.plan.History) (v : (R.plan.finish h).Site),
        ((R.plan.assemble h (R.wordAssembly reg.1.steps L) N).2 v).resources ≤
          ((2*(B.repeat (s w)).length+1)*(B.localCoefficient*(64*w+1)^3))*R.chargeAt h reg.2 start v := by
  filter_upwards [window_resources_on_lanes B scale a b positive] with w bound
  intro age align
  exact bound age (by omega) (by omega)

theorem native_window_resources {u s : ℕ → ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ age : ℕ, w≤age^10 → 16*age^10≤64*w → ∀ {k low pc regs words S base fuel : ℕ}
      (M : Machine (64*w) pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (hk : 2≤k+1)
      (rem : ℕ) (e : k+1=(B.repeat (s w)).charge+rem) (_small : low≤w/2)
      (_q : Fintype.card F≤64*w) (_p : pc≤64*w) (_r : regs≤64*w) (_a : words≤64*w) (_d : (k+1)+low≤64*w),
      let d := (k+1)+low
      let grid := TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words d
      let X := B.cursorState hk low (1+(d+d)) grid.cells
      let R := Program.recast e X ((B.repeat (s w)).run rem (e ▸ X))
      let reg := registerOnLanes B (Fin S → Bool) (s w) rem X e
      let L := TraceReceiverSeedWords.wordsLayout M t hF st B hk
      let N := TraceReceiverSeedWords.forest M t hF st B hk
      let start := TraceReceiverSeedWords.start M t hF st B hk
      ∀ (h : R.plan.History) (v : (R.plan.finish h).Site),
        ((R.plan.assemble h (R.wordAssembly reg.1.steps L) N).2 v).resources ≤
          ((2*(B.repeat (s w)).length+1)*(B.localCoefficient*(64*w+1)^3))*R.chargeAt h reg.2 start v := by
  let a := (2*2^(B.exponent 0)+3)*seedRate B.cursorCopies
  have pos : 0<a := Nat.mul_pos (by positivity) (seedRate_pos _)
  filter_upwards [window_resources_on_lanes B scale a 15 pos] with w bound
  intro age lower upper k low pc regs words S base fuel M t hF st hk rem e small q p r ext depth d grid X R reg L N start h v
  have seed := native_seed_bounds B M t hF st hk low q p r ext depth (fun x => decide (x.1=0))
    (TraceReceiverSeedWords.pairs M t hF st) (TraceReceiverSeedWords.pairs_le M t hF st)
  exact bound age lower upper (Fin S → Bool) rem low X e L N start small
    (TraceReceiverSeedWords.words_ordered M t hF st B hk) seed.1 seed.2
    (TraceReceiverSeedWords.seed_budget M t hF st B hk) h v

theorem native_cofinal_resources {u s : ℕ → ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ age : ℕ, 64*w=16*age^10 → ∀ {k low pc regs words S base fuel : ℕ}
      (M : Machine (64*w) pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (hk : 2≤k+1)
      (rem : ℕ) (e : k+1=(B.repeat (s w)).charge+rem) (_small : low≤w/2)
      (_q : Fintype.card F≤64*w) (_p : pc≤64*w) (_r : regs≤64*w) (_a : words≤64*w) (_d : (k+1)+low≤64*w),
      let d := (k+1)+low
      let grid := TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words d
      let X := B.cursorState hk low (1+(d+d)) grid.cells
      let R := Program.recast e X ((B.repeat (s w)).run rem (e ▸ X))
      let reg := registerOnLanes B (Fin S → Bool) (s w) rem X e
      let L := TraceReceiverSeedWords.wordsLayout M t hF st B hk
      let N := TraceReceiverSeedWords.forest M t hF st B hk
      let start := TraceReceiverSeedWords.start M t hF st B hk
      ∀ (h : R.plan.History) (v : (R.plan.finish h).Site),
        ((R.plan.assemble h (R.wordAssembly reg.1.steps L) N).2 v).resources ≤
          ((2*(B.repeat (s w)).length+1)*(B.localCoefficient*(64*w+1)^3))*R.chargeAt h reg.2 start v := by
  filter_upwards [native_window_resources B scale] with w bound
  intro age align
  exact bound age (by omega) (by omega)

/-- Every large native word width admits a physical clock in the necessary
range. This covers the issued terminal factor at every such width. -/
theorem native_universal_resources {u s : ℕ → ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {k low pc regs words S base fuel : ℕ}
      (M : Machine (64*w) pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (hk : 2≤k+1)
      (rem : ℕ) (e : k+1=(B.repeat (s w)).charge+rem) (_small : low≤w/2)
      (_q : Fintype.card F≤64*w) (_p : pc≤64*w) (_r : regs≤64*w) (_a : words≤64*w) (_d : (k+1)+low≤64*w),
      let d := (k+1)+low
      let grid := TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words d
      let X := B.cursorState hk low (1+(d+d)) grid.cells
      let R := Program.recast e X ((B.repeat (s w)).run rem (e ▸ X))
      let reg := registerOnLanes B (Fin S → Bool) (s w) rem X e
      let L := TraceReceiverSeedWords.wordsLayout M t hF st B hk
      let N := TraceReceiverSeedWords.forest M t hF st B hk
      let start := TraceReceiverSeedWords.start M t hF st B hk
      ∀ (h : R.plan.History) (v : (R.plan.finish h).Site),
        ((R.plan.assemble h (R.wordAssembly reg.1.steps L) N).2 v).resources ≤
          ((2*(B.repeat (s w)).length+1)*(B.localCoefficient*(64*w+1)^3))*R.chargeAt h reg.2 start v := by
  filter_upwards [native_window_resources B scale, eventually_ge_atTop (2*64^10)] with w bound big
  have half : 64^10 ≤ w/2 := by omega
  obtain ⟨lower,upper⟩ := TraceAdmission.receiverAge_chart (w/2) half
  intro k low pc regs words S base fuel
  exact @bound (TraceAdmission.receiverAge (w/2)) (by omega) (by omega) k low pc regs words S base fuel

end Hierarchy.TraceDistribution.Physical

end
end OAI
