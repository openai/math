import OAI.Hierarchy.DescentChronologicalGrains
import OAI.Hierarchy.DescentChosenRotorMenu
import OAI.Hierarchy.DescentRecipeClosedReset
import OAI.Hierarchy.DescentPeriodClose
import OAI.Hierarchy.DescentIssuedChronology

namespace OAI
/-! # A period of actually recorded scalar recipes -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentColonies DescentFineTerminals DescentResetInvoice DescentBaseProfile
open DescentRotor DescentMixedRouter DescentHostDegree
open LinearAlgebra.SpectralBooks ThreeFlat
open Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z w hist : ℕ}

namespace Chronology

variable {W₀ W₁ W₂ : MarkedWorld F d P bits} {i₀ z₀ D₀ i₁ z₁ D₁ i₂ z₂ D₂ : ℕ}
    {first : Reached W₀ G q ε S k i₀ z₀ D₀ w hist} {middle : Reached W₁ G q ε S k i₁ z₁ D₁ w hist}
    {last : Reached W₂ G q ε S k i₂ z₂ D₂ w hist}

def Path.recorded (p : ℕ) (path : Path first middle) : Prop := by
  induction path with
  | here => exact True
  | ordinary prev ticket ih => exact ih
  | reset prev b ih => exact ih ∧ b.Recorded p

theorem Path.recorded_of_ordinaryOnly (path : Path first middle) (p : ℕ)
    (ordinary : path.ordinaryOnly) : path.recorded p := by
  induction path with
  | here=>trivial
  | ordinary prev ticket ih=>exact ih ordinary
  | reset prev b ih=>exact ordinary.elim

theorem Path.recorded_whole (path : Path first middle) (p : ℕ)
    (receipt : path.recorded p) : path.whole p := by
  induction path with
  | here=>trivial
  | ordinary prev ticket ih=>exact ih receipt
  | reset prev b ih=>exact ⟨ih receipt.1,receipt.2.divides⟩

theorem Path.recorded_append (x : Path first middle) (y : Path middle last) (p : ℕ)
    (hx : x.recorded p) (hy : y.recorded p) : (x.append y).recorded p := by
  induction y with
  | here=>exact hx
  | ordinary prev ticket ih=>exact ih hy
  | reset prev b ih=>exact ⟨ih hy.1,hy.2⟩

end Chronology

theorem close_period_recorded {n h C f g cut tail p start z₀ D₀ : ℕ} (he : 0≤ε) (hu : 0≤q*w)
    (H : Histories F d P bits) (run : Schedule G he (u:=q*w) S.rounds H)
    (ctl : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
    (age : i<S.length) (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (positive : 0<z) (hp : 0<p) (grainAt : z=S.grainAt G.b p (i+1))
    (branch : G.b≤2^S.capGain) (wire : w=S.epochPower^S.priceExponent) (history : hist=S.firstWidth G.b p)
    (initial : ∀c,Reached (H.state c) G q ε S k start z₀ D₀ w hist)
    (zRow : ℕ→ℕ)
    (terminal : ∀c,∃last : Reached ((Schedule.finish G he run).state c) G q ε S k i z (atRound S.rounds) w hist,
      ∃path : Chronology.Path (initial (Chronology.sourceChoice he run c)) last,
        path.selections=Chronology.scheduled he run c ∧ path.ordinaryOnly ∧ (∀n,path.whole n) ∧
          ∀v R,(∀j<S.rounds,v∣zRow j)→path.aligned v R)
    (issued : Schedule.Grains zRow run) (atStop : zRow S.rounds=z) (ordinal : ∀j<S.rounds,p∣zRow j) :
    ∃E : Epoch H G hu he S.rounds h C (GroupStage.depthBound (atRound S.rounds) n f g),
      Epoch.Grains zRow ctl.board ctl.bitsR E ∧ ∀c,
        ∃target : Reached ((E.finish G hu he).state c) G q ε S k (i+1) z 3 w hist,
          ∃path : Chronology.Path (initial (Chronology.sourceChoice he E.subrounds c)) target,
            path.selections=Chronology.scheduled he E.subrounds c ∧ path.recorded p ∧
            path.aligned p (max 1 (max ctl.bitsR (C*ctl.bitsR))) := by
  let done:=Schedule.finish G he run
  let stop (c : done.Choice):=(terminal c).choose
  let packet (c : done.Choice):=close_recipe_branch (stop c) ctl age budget hp grainAt branch wire history
  let b (c : done.Choice):=(packet c).choose
  refine ⟨periodEpoch he hu H run ctl positive stop b,
    periodEpoch_grains he hu H run ctl positive stop b zRow issued atStop,?_⟩
  intro c
  obtain ⟨path,steps,ordinary,_,aligned⟩:=(terminal c).choose_spec
  have read:=(packet c).choose_spec
  refine ⟨(b c).next,.reset path (b c),steps,⟨path.recorded_of_ordinaryOnly p ordinary,read⟩,
    aligned p _ ordinal,?_,read.divides,?_⟩
  · rw [(b c).unit]
    exact Nat.mul_pos positive G.base_pos
  · rw [(b c).width]

theorem close_period_ordered {n h C f g cut tail p start z₀ D₀ : ℕ} (he : 0≤ε) (hu : 0≤q*w)
    (H : Histories F d P bits) (run : Schedule G he (u:=q*w) S.rounds H)
    (order : DescentTerminalEpochDecoder.ScheduleOrders G he run)
    (ctl : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
    (age : i<S.length) (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (positive : 0<z) (hp : 0<p) (grainAt : z=S.grainAt G.b p (i+1))
    (branch : G.b≤2^S.capGain) (wire : w=S.epochPower^S.priceExponent) (history : hist=S.firstWidth G.b p)
    (initial : ∀c,Reached (H.state c) G q ε S k start z₀ D₀ w hist)
    (zRow : ℕ→ℕ)
    (terminal : ∀c,∃last : Reached ((Schedule.finish G he run).state c) G q ε S k i z (atRound S.rounds) w hist,
      ∃path : Chronology.Path (initial (Chronology.sourceChoice he run c)) last,
        path.ranked=Chronology.rankedSchedule he run order c ∧
        path.selections=Chronology.scheduled he run c ∧ path.ordinaryOnly ∧ (∀n,path.whole n) ∧
          ∀v R,(∀j<S.rounds,v∣zRow j)→path.aligned v R)
    (issued : Schedule.Grains zRow run) (atStop : zRow S.rounds=z) (ordinal : ∀j<S.rounds,p∣zRow j) :
    ∃E : Epoch H G hu he S.rounds h C (GroupStage.depthBound (atRound S.rounds) n f g),
      ∃orders : DescentTerminalEpochDecoder.ScheduleOrders G he E.subrounds,
      Epoch.Grains zRow ctl.board ctl.bitsR E ∧ ∀c,
        ∃target : Reached ((E.finish G hu he).state c) G q ε S k (i+1) z 3 w hist,
          ∃path : Chronology.Path (initial (Chronology.sourceChoice he E.subrounds c)) target,
            path.ranked=Chronology.rankedSchedule he E.subrounds orders c ∧
            path.selections=Chronology.scheduled he E.subrounds c ∧ path.recorded p ∧
            path.aligned p (max 1 (max ctl.bitsR (C*ctl.bitsR))) := by
  let done:=Schedule.finish G he run
  let stop (c : done.Choice):=(terminal c).choose
  let packet (c : done.Choice):=close_recipe_branch (stop c) ctl age budget hp grainAt branch wire history
  let b (c : done.Choice):=(packet c).choose
  refine ⟨periodEpoch he hu H run ctl positive stop b,order,
    periodEpoch_grains he hu H run ctl positive stop b zRow issued atStop,?_⟩
  intro c
  obtain ⟨path,ranks,steps,ordinary,_,aligned⟩:=(terminal c).choose_spec
  have read:=(packet c).choose_spec
  refine ⟨(b c).next,.reset path (b c),ranks,steps,⟨path.recorded_of_ordinaryOnly p ordinary,read⟩,
    aligned p _ ordinal,?_,read.divides,?_⟩
  · rw [(b c).unit]
    exact Nat.mul_pos positive G.base_pos
  · rw [(b c).width]

/-- Close the same issued period while retaining both the source cable and emitted pair ordinal. -/
theorem close_period_dated {n h C f g cut tail p start z₀ D₀ : ℕ} (he : 0≤ε) (hu : 0≤q*w)
    (H : Histories F d P bits) (run : Schedule G he (u:=q*w) S.rounds H)
    (order inputOrder : DescentTerminalEpochDecoder.ScheduleOrders G he run)
    (ctl : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
    (age : i<S.length) (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (positive : 0<z) (hp : 0<p) (grainAt : z=S.grainAt G.b p (i+1))
    (branch : G.b≤2^S.capGain) (wire : w=S.epochPower^S.priceExponent) (history : hist=S.firstWidth G.b p)
    (initial : ∀c,Reached (H.state c) G q ε S k start z₀ D₀ w hist)
    (zRow : ℕ→ℕ)
    (terminal : ∀c,∃last : Reached ((Schedule.finish G he run).state c) G q ε S k i z (atRound S.rounds) w hist,
      ∃path : Chronology.Path (initial (Chronology.sourceChoice he run c)) last,
        path.ranked=Chronology.rankedSchedule he run order c ∧
        path.inputRanked=Chronology.rankedSchedule he run inputOrder c ∧
        path.capFactors=ordinaryCapFactors G.b 0 S.rounds ∧
        path.selections=Chronology.scheduled he run c ∧ path.ordinaryOnly ∧ (∀n,path.whole n) ∧
          ∀v R,(∀j<S.rounds,v∣zRow j)→path.aligned v R)
    (issued : Schedule.Grains zRow run) (atStop : zRow S.rounds=z) (ordinal : ∀j<S.rounds,p∣zRow j) :
    ∃E : Epoch H G hu he S.rounds h C (GroupStage.depthBound (atRound S.rounds) n f g),
      ∃orders inputOrders : DescentTerminalEpochDecoder.ScheduleOrders G he E.subrounds,
      Epoch.Grains zRow ctl.board ctl.bitsR E ∧ ∀c,
        ∃target : Reached ((E.finish G hu he).state c) G q ε S k (i+1) z 3 w hist,
          ∃path : Chronology.Path (initial (Chronology.sourceChoice he E.subrounds c)) target,
            path.ranked=Chronology.rankedSchedule he E.subrounds orders c ∧
            path.inputRanked=Chronology.rankedSchedule he E.subrounds inputOrders c ∧
            ((path.capFactors=capPeriod G.b S.rounds g ∧ path.OnlyRotor (RotorSpec.ofRates ctl)) ∧ path.ClosedPeriod) ∧
            path.selections=Chronology.scheduled he E.subrounds c ∧ path.recorded p ∧
            path.aligned p (max 1 (max ctl.bitsR (C*ctl.bitsR))) := by
  let done:=Schedule.finish G he run
  let stop (c : done.Choice):=(terminal c).choose
  let packet (c : done.Choice):=close_recipe_branch (stop c) ctl age budget hp grainAt branch wire history
  let b (c : done.Choice):=(packet c).choose
  refine ⟨periodEpoch he hu H run ctl positive stop b,order,inputOrder,
    periodEpoch_grains he hu H run ctl positive stop b zRow issued atStop,?_⟩
  intro c
  obtain ⟨path,ranks,inputs,factors,steps,ordinary,_,aligned⟩:=(terminal c).choose_spec
  have read:=(packet c).choose_spec
  have resetFactors : (path.reset (b c)).capFactors = capPeriod G.b S.rounds g := by
    change path.capFactors ++ [2^g] = ordinaryCapFactors G.b 0 S.rounds ++ [2^g]
    exact congrArg (fun xs : List ℕ => xs ++ [2^g]) factors
  refine ⟨(b c).next,.reset path (b c),ranks,inputs,⟨⟨resetFactors,path.ordinary_rotor _ ordinary,rfl⟩,ordinary⟩,steps,⟨path.recorded_of_ordinaryOnly p ordinary,read⟩,
    aligned p _ ordinal,?_,read.divides,?_⟩
  · rw [(b c).unit]
    exact Nat.mul_pos positive G.base_pos
  · rw [(b c).width]

theorem close_period_joint {n h C f g cut tail p start z₀ D₀ : ℕ} (he : 0≤ε) (hu : 0≤q*w)
    (H : Histories F d P bits) (run : Schedule G he (u:=q*w) S.rounds H)
    (order inputOrder : DescentTerminalEpochDecoder.ScheduleOrders G he run)
    (ctl : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
    (age : i<S.length) (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (positive : 0<z) (hp : 0<p) (grainAt : z=S.grainAt G.b p (i+1))
    (branch : G.b≤2^S.capGain) (wire : w=S.epochPower^S.priceExponent) (history : hist=S.firstWidth G.b p)
    (initial : ∀c,Reached (H.state c) G q ε S k start z₀ D₀ w hist)
    (zRow : ℕ→ℕ)
    (terminal : ∀c,∃last : Reached ((Schedule.finish G he run).state c) G q ε S k i z (atRound S.rounds) w hist,
      ∃path : Chronology.Path (initial (Chronology.sourceChoice he run c)) last,
        path.ranked=Chronology.rankedSchedule he run order c ∧
        path.inputRanked=Chronology.rankedSchedule he run inputOrder c ∧
        path.capFactors=ordinaryCapFactors G.b 0 S.rounds ∧
        path.selections=Chronology.scheduled he run c ∧ path.ordinaryOnly ∧ (∀n,path.whole n) ∧
          ∀v R,(∀j<S.rounds,v∣zRow j)→path.aligned v R)
    (issued : Schedule.Grains zRow run) (atStop : zRow S.rounds=z) (ordinal : ∀j<S.rounds,p∣zRow j) :
    ∃E : Epoch H G hu he S.rounds h C (GroupStage.depthBound (atRound S.rounds) n f g),
      ∃orders inputOrders : DescentTerminalEpochDecoder.ScheduleOrders G he E.subrounds,
      Epoch.Grains zRow ctl.board ctl.bitsR E ∧ ∀c,
        ∃target : Reached ((E.finish G hu he).state c) G q ε S k (i+1) z 3 w hist,
          ∃path : Chronology.Path (initial (Chronology.sourceChoice he E.subrounds c)) target,
            path.ranked=Chronology.rankedSchedule he E.subrounds orders c ∧
            path.inputRanked=Chronology.rankedSchedule he E.subrounds inputOrders c ∧
            (path.capFactors=capPeriod G.b S.rounds g ∧ path.OnlyRotor (RotorSpec.ofRates ctl)) ∧
            path.selections=Chronology.scheduled he E.subrounds c ∧ path.recorded p ∧
            path.aligned p (max 1 (max ctl.bitsR (C*ctl.bitsR))) := by
  obtain ⟨E,orders,inputs,grains,rows⟩:=close_period_dated he hu H run order inputOrder ctl age budget positive hp
    grainAt branch wire history initial zRow terminal issued atStop ordinal
  refine ⟨E,orders,inputs,grains,fun c=>?_⟩
  obtain ⟨target,path,ranks,fromInput,fees,rest⟩:=rows c
  exact ⟨target,path,ranks,fromInput,fees.1,rest⟩

end
end Hierarchy.DescentSixParty

end OAI
