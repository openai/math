import OAI.Hierarchy.TraceRegisteredVolume
import OAI.Hierarchy.TraceReceiverForest
import OAI.Hierarchy.TraceAdmittedFactor
import OAI.Hierarchy.TracePhysicalCharges
import OAI.Hierarchy.TraceFactorHeight
import OAI.ThreeFlat.Diagonal.PhysicalProgramFreshPrices
import OAI.Hierarchy.TraceReceiverSeedBudget

namespace OAI
/-! # Archived work of the actual native verifier's selected terminal factors -/

noncomputable section
namespace Hierarchy.TraceDistribution.Physical

open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open Filter Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Topology

variable {F Pins : Type} [Field F] [Fintype F] (B : Block F)

omit [Fintype F] in
theorem priced_on_lanes {u s : ℕ → ℕ} (scale : Scale u s) (a b : ℕ) (positive : 0<a) :
    ∀ᶠ w : ℕ in atTop, ∀ (Pins : Type) {lanes : ℕ} (rem low : ℕ) (X : State (2^(B.exponent 0)) lanes)
      (e : lanes=(B.repeat (s w)).charge+rem) (L : X.Words Pins) (N : Forest F L.ports.form)
      (start : X.Site → ℕ),
      low≤w/2 → X.OrderedHalves L → X.maxWidth ≤ 2^low*(a*(w+1)^b) →
      (∀ x,start x≤2^low*(a*(w+1)^b)) →
      (∀ x,1+X.incidentWidth x ≤ start x ∧ L.ports.form.width x≤2*start x ∧ (N x).resources≤ start x) →
      let R := Program.recast e X ((B.repeat (s w)).run rem (e ▸ X))
      let reg := registerOnLanes B Pins (s w) rem X e
      ∀ (h : R.plan.History) (depth setup maps : ℕ) (v : (R.plan.finish h).Site),
        FactorWork.work R.plan h (R.wordAssembly reg.1.steps L) N depth setup maps v ≤
          publishedWork R h reg.2 start
            (FactorWork.archiveTariff w depth setup maps (B.repeat (s w)).length B.localCoefficient) v := by
  filter_upwards [fixed_tile_caps B, published_peak_room B scale a b 1 0 positive] with w tiles cap
  intro Pins lanes rem low X e L N start small ord maxWidth startBound seeds
  subst lanes
  intro R reg h depth setup maps v
  have upper := cap rem low 1 X h start small (by simp) maxWidth startBound
  have room : ((B.repeat (s w)).run rem X).LevelsCapped 1 (2^(w^10)) h
      (B.charges (s w) rem X) start := by
    apply ((B.repeat (s w)).run rem X).levels_capped_of_terminal
    intro z
    have lim : 3*w/5≤w^10 := (show 3*w/5≤w by omega).trans (Nat.le_self_pow (by decide : (10:ℕ)≠0) w)
    simpa only [publishedWork,Nat.mul_one,Nat.one_mul] using
      (upper z).trans (Nat.pow_le_pow_right (by decide : 0<2) lim)
  let P := B.repeat (s w)
  let K := B.localCoefficient*(16*w^10+1)^3
  have ge : 2≤K := fresh_price_scale B w
  have actual := B.program_fresh_path (Pins:=Pins) w P (B.repeat_supported _) B.costFactors.sum
    (B.factor_bound _) rem X tiles.1 tiles.2 h start room
  exact block_work_charged B (s w) rem X h reg.1.steps L N start ord (fun x=>(seeds x).1)
    (fun x=>(seeds x).2.1) K ge actual
    (fun x=>(seeds x).2.2.trans (Nat.le_mul_of_pos_left _ (by omega : 0<K)))
    depth setup maps _ le_rfl v

/-- Every admitted factor of the native paired-input trace is covered by its
own physical work word. The tree and pin layout here cover every original bit. -/
theorem native_factor_work {u s : ℕ → ℕ} (scale : Scale u s) :
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
      ∀ (h : R.plan.History) (depth setup maps : ℕ) (v : (R.plan.finish h).Site),
        FactorWork.work R.plan h (R.wordAssembly reg.1.steps L) N depth setup maps v ≤
          publishedWork R h reg.2 start
            (FactorWork.archiveTariff w depth setup maps (B.repeat (s w)).length B.localCoefficient) v := by
  let a := (2*2^(B.exponent 0)+3)*seedRate B.cursorCopies
  have pos : 0<a := Nat.mul_pos (by positivity) (seedRate_pos _)
  filter_upwards [priced_on_lanes B scale a 15 pos] with w admitted
  intro k low pc regs words S base fuel M t hF st hk rem e small q p r a' depth d grid X R reg L N start h height setup maps v
  have seed := native_seed_bounds B M t hF st hk low q p r a' depth (fun x => decide (x.1=0))
    (TraceReceiverSeedWords.pairs M t hF st) (TraceReceiverSeedWords.pairs_le M t hF st)
  exact admitted (Fin S → Bool) rem low X e L N start small (TraceReceiverSeedWords.words_ordered M t hF st B hk)
    seed.1 seed.2 (TraceReceiverSeedWords.seed_budget M t hF st B hk) h height setup maps v

/-- The canonical archived W_j simultaneously covers native factor work,
has a total bounded by the time cap times a fixed polynomial, and fits the
individual factor allowance. -/
theorem native_work_bounds {u s : ℕ → ℕ} (scale : Scale u s) (c b : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ {k low pc regs words S base fuel : ℕ}
      (M : Machine (64*w) pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (hk : 2≤k+1)
      (rem : ℕ) (e : k+1=(B.repeat (s w)).charge+rem) (_small : low≤w/2)
      (_q : Fintype.card F≤64*w) (_p : pc≤64*w) (_r : regs≤64*w) (_a : words≤64*w) (_d : (k+1)+low≤64*w),
      k+1≤2*(w+1) → (k+1)+low≤u w+1 → s w≤w →
      let d := (k+1)+low
      let grid := TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words d
      let X := B.cursorState hk low (1+(d+d)) grid.cells
      let R := Program.recast e X ((B.repeat (s w)).run rem (e ▸ X))
      let reg := registerOnLanes B (Fin S → Bool) (s w) rem X e
      let L := TraceReceiverSeedWords.wordsLayout M t hF st B hk
      let N := TraceReceiverSeedWords.forest M t hF st B hk
      let start := TraceReceiverSeedWords.start M t hF st B hk
      let stageCount := (B.repeat (s w)).length
      let a := c+B.levels+1
      let rate := (10025+1018*a)*(2*a+1)*B.localCoefficient*17^3
      let initial := (2*2^(B.exponent 0)+3)*seedRate B.cursorCopies
      ∀ (h : R.plan.History) (depth setup maps : ℕ),
        depth≤c*(w+1)^b → setup≤c*(w+1)^b → maps≤c*(w+1)^b →
        let unit := FactorWork.archiveTariff w depth setup maps stageCount B.localCoefficient
        let W := publishedWork R h reg.2 start unit
        (∑ v,W v) ≤ 2^(u w)*(rate*(4*initial*⌈scanRate B⌉₊))*(w+1)^(max b 1+max b 1+30+17) ∧
          ∀ v, FactorWork.work R.plan h (R.wordAssembly reg.1.steps L) N depth setup maps v ≤ W v ∧
            W v ≤ 2^(3*w/5) := by
  let a := (2*2^(B.exponent 0)+3)*seedRate B.cursorCopies
  let coef := c+B.levels+1
  let e' := max b 1
  let rate := (10025+1018*coef)*(2*coef+1)*B.localCoefficient*17^3
  have pos : 0<a := Nat.mul_pos (by positivity) (seedRate_pos _)
  filter_upwards [native_factor_work B scale, registered_bounds B scale a 15 rate (e'+e'+30) pos] with w admitted bounded
  intro k low pc regs words S base fuel M t hF st hk rem e small q p r ext fits axes round blocks
    d grid X R reg L N start stageCount coefficient tariffRate initial h depth setup maps hd hs hm unit W
  let desc := TraceSourceOwner.shape (64*w) pc regs words S fuel d grid.internal
  have poly : c*(w+1)^b ≤ coef*(w+1)^e' := Nat.mul_le_mul (by dsimp [coef]; omega)
    (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left ..))
  have stages : stageCount ≤ coef*(w+1)^e' := by
    change (B.repeat (s w)).length ≤ _
    rw [repeated_stages]
    apply Nat.mul_le_mul (by dsimp [coef]; omega)
    exact (blocks.trans (Nat.le_succ w)).trans
      (Nat.le_self_pow (by dsimp [e']; omega : e'≠0) _)
  have cost := FactorWork.archiveTariff_le w depth setup maps stageCount B.localCoefficient coef e'
    (hd.trans poly) (hs.trans poly) (hm.trans poly) stages
  have seed := native_seed_bounds B M t hF st hk low q p r ext fits (fun x => decide (x.1=0))
    (TraceReceiverSeedWords.pairs M t hF st) (TraceReceiverSeedWords.pairs_le M t hF st)
  have slots : (1+(d+d))*grid.cells*3 ≤ a*(w+1)^15 := by
    have baseSlots := (seed_covers_arc 0 desc.stride grid.cells B.cursorCopies d).trans
      (native_seed_charge M t hF st 0 B.cursorCopies q p r ext fits)
    have unitBound : seedRate B.cursorCopies≤a := Nat.le_mul_of_pos_left _ (by positivity)
    exact (show (1+(d+d))*grid.cells*3≤ seedRate B.cursorCopies*(w+1)^15 by
      simpa only [pow_zero,one_mul] using baseSlots).trans (Nat.mul_le_mul_right _ unitBound)
  have both := bounded (Fin S → Bool) rem low (1+(d+d)) grid.cells unit e hk axes round blocks small
    slots cost h start seed.2
  exact ⟨both.1, fun v=>⟨admitted M t hF st hk rem e small q p r ext fits h depth setup maps v,both.2 v⟩⟩

/-- With the actual receiver rates and terminal replay depth, the total exponent is 51.
The coefficient depends only on the fixed block, its stage and root instruction rates, and the port degree. -/
theorem native_scheduled_work_bounds {u s : ℕ → ℕ} (scale : Scale u s) (degree stageRate rootRate : ℕ) :
    ∃ C : ℕ,
    ∀ᶠ w : ℕ in atTop, ∀ {k low pc regs words S base fuel : ℕ}
      (M : Machine (64*w) pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (hk : 2≤k+1)
      (rem : ℕ) (e : k+1=(B.repeat (s w)).charge+rem) (_small : low≤w/2)
      (_q : Fintype.card F≤64*w) (_p : pc≤64*w) (_r : regs≤64*w) (_a : words≤64*w) (_d : (k+1)+low≤64*w),
      k+1≤2*(w+1) → (k+1)+low≤u w+1 → s w≤w →
      let d := (k+1)+low
      let grid := TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words d
      let X := B.cursorState hk low (1+(d+d)) grid.cells
      let R := Program.recast e X ((B.repeat (s w)).run rem (e ▸ X))
      let reg := registerOnLanes B (Fin S → Bool) (s w) rem X e
      let L := TraceReceiverSeedWords.wordsLayout M t hF st B hk
      let N := TraceReceiverSeedWords.forest M t hF st B hk
      let start := TraceReceiverSeedWords.start M t hF st B hk
      let stageCount := (B.repeat (s w)).length
      ∀ h : R.plan.History,
        let depth:=4+stageCount
        let setup:=TraceFactorReceiver.Gather.setupPrice stageCount stageRate
        let maps:=TraceFactorReceiver.Gather.mapPrice degree rootRate
        let unit := FactorWork.archiveTariff w depth setup maps stageCount B.localCoefficient
        let W := publishedWork R h reg.2 start unit
        (∑ v,W v) ≤ 2^(u w)*C*(w+1)^51 ∧
          ∀ v, FactorWork.work R.plan h (R.wordAssembly reg.1.steps L) N depth setup maps v ≤ W v ∧
            W v ≤ 2^(3*w/5) := by
  let pass:=B.levels+1
  let a:=pass+degree+4
  let c:=a+10*(a+2)^2*stageRate+rootRate*(a+7)
  let ar:=c+B.levels+1
  let rate:=(10025+1018*ar)*(2*ar+1)*B.localCoefficient*17^3
  let initial:=(2*2^(B.exponent 0)+3)*seedRate B.cursorCopies
  refine ⟨rate*(4*initial*⌈scanRate B⌉₊),?_⟩
  filter_upwards [native_work_bounds B scale c 2] with w bound
  intro k low pc regs words S base fuel M t hF st hk rem e small q hp hr ext fits axes round blocks
    d grid X R reg L N start stageCount h depth setup maps unit weights
  have stages : stageCount≤pass*(w+1) := by
    change (B.repeat (s w)).length≤_
    rw [repeated_stages]
    exact Nat.mul_le_mul_left pass (by omega)
  have ap : pass≤a := by dsimp [a];omega
  have ad : degree≤a := by dsimp [a];omega
  have age : w+1≤(w+1)^2 := Nat.le_self_pow (by decide) _
  have cap : stageCount≤a*(w+1)^1 := by simpa using stages.trans (Nat.mul_le_mul_right _ ap)
  have deg : degree≤a*(w+1)^1 := by
    rw [pow_one]; exact ad.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have fees:=TraceFactorReceiver.Gather.prices_polynomial w 1 a stageCount degree stageRate rootRate cap deg
  have hd : depth≤c*(w+1)^2 := calc
    4+stageCount ≤ 4*(w+1)+pass*(w+1) :=
      Nat.add_le_add (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) stages
    _ = (4+pass)*(w+1) := (Nat.add_mul ..).symm
    _ ≤ c*(w+1)^2 := Nat.mul_le_mul (by dsimp [c,a];omega) age
  have hs : setup≤c*(w+1)^2 := fees.1.trans
    (Nat.mul_le_mul_right _ (by dsimp [c];omega))
  have hm : maps≤c*(w+1)^2 := fees.2.trans (Nat.mul_le_mul
    (by dsimp [c];omega) (by simpa using age))
  exact bound M t hF st hk rem e small q hp hr ext fits axes round blocks h depth setup maps hd hs hm


end Hierarchy.TraceDistribution.Physical

end
end OAI
