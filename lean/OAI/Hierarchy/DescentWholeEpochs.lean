import OAI.Hierarchy.DescentRecordedPeriod
import OAI.Hierarchy.DescentChronologicalSeed
import OAI.Hierarchy.DescentPeriodClose
import OAI.Hierarchy.DescentGrainCalendar
import OAI.Hierarchy.DescentPaidGroupSeed
import OAI.Hierarchy.DescentSeedRootRows

namespace OAI
/-! # Running the priced ordinary and reset phases through the final group -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentHostDegree DescentInitialHost Catalyst
open scoped Classical BigOperators
noncomputable section
set_option Elab.async false
universe v
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ}
variable (G : PoweredGadget F) (S : AtomSchedule) {k cut tail n h C f g p : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "ε" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "z" => S.grainAt G.b p
local notation "D" => atRound S.rounds
local notation "period" => (fun epoch slot=>z (epoch*(S.rounds+1)+slot))
local notation "resetDepth" => GroupStage.depthBound D n f g

variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
  (branch : G.b≤2^S.capGain) (p0 : 0<p)
  (he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)
  (hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ)^S.priceExponent)) *
    (S.epochPower : ℝ)^S.priceExponent)

namespace Chronology
variable {q fee : ℝ} {hq : 0 ≤ q} {hf : 0 ≤ fee} {t h C ht : ℕ}

/-- The initial choice obtained by following the recorded ordinary transitions back through the epochs. -/
def epochsSource : {J : ℕ} → {H : Histories.{0, 0, v} F d P bits} →
    (run : Epochs G hq hf (h := h) (C := C) (Ht := ht) (t := t) J H) →
    (Epochs.finish G hq hf run).Choice → H.Choice
  | 0, _, _, c => c
  | j+1, _, run, c =>
    sourceChoice hf run.1.subrounds (@epochsSource j (run.1.finish G hq hf) run.2 c)

/-- The selections made on the chosen branch in chronological order. -/
def epochsSelections : {J : ℕ} → {H : Histories.{0, 0, v} F d P bits} →
    (run : Epochs G hq hf (h := h) (C := C) (Ht := ht) (t := t) J H) →
    (Epochs.finish G hq hf run).Choice → List (Selection F P d bits G fee)
  | 0, _, _, _ => []
  | j+1, _, run, c =>
    scheduled hf run.1.subrounds (epochsSource G (J := j) (H := run.1.finish G hq hf) run.2 c) ++
      @epochsSelections j (run.1.finish G hq hf) run.2 c

/-- Pair ordinals in chronological order, shared by every profile below each parent. -/
def epochsRanked : {J : ℕ} → {H : Histories.{0, 0, v} F d P bits} →
    (run : Epochs G hq hf (h := h) (C := C) (Ht := ht) (t := t) J H) →
    DescentTerminalEpochDecoder.EpochOrders G hq hf run →
    (Epochs.finish G hq hf run).Choice → List (RankedSelection F P d bits G fee)
  | 0, _, _, _, _ => []
  | j+1, _, run, order, c =>
    rankedSchedule hf run.1.subrounds order.1
      (epochsSource G (J := j) (H := run.1.finish G hq hf) run.2 c) ++
      @epochsRanked j (run.1.finish G hq hf) run.2 order.2 c
end Chronology

section
include ordinary branch p0

/-- One fixed native incoming placement per old profile and the literal issued rows of every
ordinary transition and of the one reset at the end of the period. -/
theorem exact_period_links_dated (H : Histories F d P bits) {j : ℕ} (age : j<S.height)
    (initial : ∀c,Reached (H.state c) G price ε S k (j*(S.rounds+1)) (z (j*(S.rounds+1))) 3 wire s) :
    ∃e : Epoch H G hu he S.rounds h C resetDepth,∃order inputOrder : DescentTerminalEpochDecoder.ScheduleOrders G he e.subrounds,
      Epoch.Grains (period j) reset.board reset.bitsR e ∧ ∀c,
      ∃target : Reached ((e.finish G hu he).state c) G price ε S k ((j+1)*(S.rounds+1)) (z ((j+1)*(S.rounds+1))) 3 wire s,
        ∃path : Chronology.Path (initial (Chronology.sourceChoice he e.subrounds c)) target,
          path.ranked=Chronology.rankedSchedule he e.subrounds order c ∧
          path.inputRanked=Chronology.rankedSchedule he e.subrounds inputOrder c ∧
          ((path.capFactors=capPeriod G.b S.rounds g ∧ path.OnlyRotor (RotorSpec.ofRates reset)) ∧ path.GrainDates p ∧ path.kinds=Chronology.kindPeriod S.rounds) ∧
          path.selections=Chronology.scheduled he e.subrounds c ∧ path.recorded p ∧ path.aligned p (max 1 (max reset.bitsR (C*reset.bitsR))) := by
  let Claim (rate : ℝ) (hrate : 0 ≤ rate) : Prop :=
      ∃e : Epoch H G hrate he S.rounds h C resetDepth,∃order inputOrder : DescentTerminalEpochDecoder.ScheduleOrders G he e.subrounds,
        Epoch.Grains (period j) reset.board reset.bitsR e ∧ ∀c,
        ∃target : Reached ((e.finish G hrate he).state c) G price ε S k ((j+1)*(S.rounds+1)) (z ((j+1)*(S.rounds+1))) 3 wire s,
          ∃path : Chronology.Path (initial (Chronology.sourceChoice he e.subrounds c)) target,
            path.ranked=Chronology.rankedSchedule he e.subrounds order c ∧
            path.inputRanked=Chronology.rankedSchedule he e.subrounds inputOrder c ∧
            ((path.capFactors=capPeriod G.b S.rounds g ∧ path.OnlyRotor (RotorSpec.ofRates reset)) ∧ path.GrainDates p ∧ path.kinds=Chronology.kindPeriod S.rounds) ∧
            path.selections=Chronology.scheduled he e.subrounds c ∧ path.recorded p ∧ path.aligned p (max 1 (max reset.bitsR (C*reset.bitsR)))
  have carry {a b : ℝ} (eqRate : a = b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      Claim a ha → Claim b hb := by
    cases eqRate
    exact id
  have castWire : (((S.epochPower ^ S.priceExponent : ℕ) : ℝ)) =
      (S.epochPower : ℝ) ^ S.priceExponent :=
    Nat.cast_pow S.epochPower S.priceExponent
  have sameRate : price * (((S.epochPower ^ S.priceExponent : ℕ) : ℝ)) =
      price * ((S.epochPower : ℝ) ^ S.priceExponent) :=
    congrArg (fun r : ℝ => price * r) castWire
  have hNative : 0 ≤ price * (((S.epochPower ^ S.priceExponent : ℕ) : ℝ)) := by
    rw [sameRate]
    exact hu
  refine carry sameRate hNative hu ?_
  dsimp only [Claim]
  let i := j*(S.rounds+1)
  have boundary : i+S.rounds<S.length := by
    have le := Nat.mul_le_mul_right (S.rounds+1) (Nat.succ_le_of_lt age)
    rw [Nat.succ_mul] at le
    dsimp only [i]
    rw [AtomSchedule.length,Nat.mul_comm (S.rounds+1)]
    omega
  let z' (a : ℕ) := z (i+a)
  let pre : ∀c,Reached (H.state c) G price ε S k i (z' 0) (atRound 0) wire s := initial
  obtain ⟨stages,order,inputOrder,cuts,terminal⟩ := ordinary_block_joint (q := price) (k := k) G S ordinary he rfl H (start := i) (j:=0) (count:=S.rounds)
    (by omega) boundary.le z' wire s (fun v hv=>by
      simpa [z',i,Nat.add_assoc] using S.grain_ordinary G.b p age hv)
    (fun v _=>S.grain_history reset.height G.base_pos branch p (i+v)) pre
  let terminalRows (round : ℕ) : Prop :=
    ∀ c : (Schedule.finish G he stages).Choice,
      ∃ last : Reached ((Schedule.finish G he stages).state c) G price ε S k
          (i + S.rounds) (z' S.rounds) (atRound round) wire s,
        ∃ path : Chronology.Path (pre (Chronology.sourceChoice he stages c)) last,
          path.ranked = Chronology.rankedSchedule he stages order c ∧
          path.inputRanked = Chronology.rankedSchedule he stages inputOrder c ∧
          path.capFactors = ordinaryCapFactors G.b 0 S.rounds ∧
          path.selections = Chronology.scheduled he stages c ∧ path.ordinaryOnly ∧
          (∀ n, path.whole n) ∧
          ∀ v R, (∀ slot < S.rounds, v ∣ z' slot) → path.aligned v R
  have rowsAtSum : terminalRows (0 + S.rounds) := terminal
  have rowsAtRound : terminalRows S.rounds :=
    (congrArg terminalRows (Nat.zero_add S.rounds)).mp rowsAtSum
  have after : z (i+S.rounds)=z ((j+1)*(S.rounds+1)) := by simpa only [i] using S.grain_reset G.b p j
  have atNext : i+S.rounds+1=(j+1)*(S.rounds+1) := by dsimp [i];ring
  have same : z' S.rounds=z (i+S.rounds+1) := by rw [atNext];exact after
  obtain ⟨e,numbers,inputNumbers,receipt,ready⟩ := close_period_dated (G := G) (S := S) (q := price) (k := k)
    (w := (S.epochPower ^ S.priceExponent : ℕ)) (hist := s) (i := i + S.rounds) (start := i) he hNative H stages order inputOrder reset boundary rfl
    (S.grain_positive G.base_pos p0 (i+S.rounds)) p0 same branch rfl rfl pre z'
    rowsAtRound cuts rfl (fun v _=>dvd_mul_right p _)
  refine ⟨e,numbers,inputNumbers,receipt,?_⟩
  intro c
  obtain ⟨target,path,ranks,inputs,fees,rest⟩:=ready c
  have dates:=path.grainDates_period p j age (by rfl) atNext rfl fees.2
  have kinds:=path.kinds_period S.rounds (by rfl) fees.2
  rw [←atNext,←same]
  exact ⟨target,path,ranks,inputs,⟨fees.1,dates,kinds⟩,rest⟩

theorem exact_period_links_joint (H : Histories F d P bits) {j : ℕ} (age : j<S.height)
    (initial : ∀c,Reached (H.state c) G price ε S k (j*(S.rounds+1)) (z (j*(S.rounds+1))) 3 wire s) :
    ∃e : Epoch H G hu he S.rounds h C resetDepth,∃order inputOrder : DescentTerminalEpochDecoder.ScheduleOrders G he e.subrounds,
      Epoch.Grains (period j) reset.board reset.bitsR e ∧ ∀c,
      ∃target : Reached ((e.finish G hu he).state c) G price ε S k ((j+1)*(S.rounds+1)) (z ((j+1)*(S.rounds+1))) 3 wire s,
        ∃path : Chronology.Path (initial (Chronology.sourceChoice he e.subrounds c)) target,
          path.ranked=Chronology.rankedSchedule he e.subrounds order c ∧
          path.inputRanked=Chronology.rankedSchedule he e.subrounds inputOrder c ∧
          (path.capFactors=capPeriod G.b S.rounds g ∧ path.OnlyRotor (RotorSpec.ofRates reset)) ∧
          path.selections=Chronology.scheduled he e.subrounds c ∧ path.recorded p ∧ path.aligned p (max 1 (max reset.bitsR (C*reset.bitsR))) := by
  obtain ⟨e,ord,inp,grains,rows⟩:=exact_period_links_dated G S ordinary reset branch p0 he hu H age initial
  refine ⟨e,ord,inp,grains,fun c=>?_⟩
  obtain ⟨target,path,ranks,inputs,fees,rest⟩:=rows c
  exact ⟨target,path,ranks,inputs,fees.1,rest⟩

theorem exact_period_links (H : Histories F d P bits) {j : ℕ} (age : j<S.height)
    (initial : ∀c,Reached (H.state c) G price ε S k (j*(S.rounds+1)) (z (j*(S.rounds+1))) 3 wire s) :
    ∃e : Epoch H G hu he S.rounds h C resetDepth,∃order : DescentTerminalEpochDecoder.ScheduleOrders G he e.subrounds,
      Epoch.Grains (period j) reset.board reset.bitsR e ∧ ∀c,
      ∃target : Reached ((e.finish G hu he).state c) G price ε S k ((j+1)*(S.rounds+1)) (z ((j+1)*(S.rounds+1))) 3 wire s,
        ∃path : Chronology.Path (initial (Chronology.sourceChoice he e.subrounds c)) target,
          path.ranked=Chronology.rankedSchedule he e.subrounds order c ∧
          path.selections=Chronology.scheduled he e.subrounds c ∧ path.recorded p ∧ path.aligned p (max 1 (max reset.bitsR (C*reset.bitsR))) := by
  obtain ⟨e,order,_,grains,links⟩:=exact_period_links_joint G S ordinary reset branch p0 he hu H age initial
  refine ⟨e,order,grains,fun c=>?_⟩
  obtain ⟨target,path,ranks,_,_,facts⟩:=links c
  exact ⟨target,path,ranks,facts⟩

/-- A complete period consists of *exactly* the ordinary branches of the
corresponding age interval, and the paid router and named output at its end. -/
theorem exact_period (H : Histories F d P bits) {j : ℕ} (age : j<S.height)
    (initial : ∀c, Nonempty (Reached (H.state c) G price ε S k (j*(S.rounds+1))
      (z (j*(S.rounds+1))) 3 wire s)) :
    ∃e : Epoch H G hu he S.rounds h C resetDepth,Epoch.Grains (period j) reset.board reset.bitsR e ∧ ∀c,Nonempty (Reached ((e.finish G hu he).state c) G price ε S k
      ((j+1)*(S.rounds+1)) (z ((j+1)*(S.rounds+1))) 3 wire s) := by
  obtain ⟨e,_,grains,links⟩ := exact_period_links G S ordinary reset branch p0 he hu H age (fun c=>(initial c).some)
  exact ⟨e,grains,fun c=>⟨(links c).choose⟩⟩

/-- The stitched path originates in the exact initial choice of its output branch. All
recorded resets are the constructors that produced the next stage. -/
theorem exact_epochs_links_dated (H : Histories F d P bits) {j count : ℕ} (total : j+count≤S.height)
    (initial : ∀c,Reached (H.state c) G price ε S k (j*(S.rounds+1)) (z (j*(S.rounds+1))) 3 wire s) :
    ∃run : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) count H,
      ∃order inputOrder : DescentTerminalEpochDecoder.EpochOrders G hu he run,Epochs.Grains reset.board reset.bitsR period j run ∧ ∀c,
      ∃target : Reached ((Epochs.finish G hu he run).state c) G price ε S k ((j+count)*(S.rounds+1)) (z ((j+count)*(S.rounds+1))) 3 wire s,
        ∃path : Chronology.Path (initial (Chronology.epochsSource G run c)) target,
          path.ranked=Chronology.epochsRanked G run order c ∧
          path.inputRanked=Chronology.epochsRanked G run inputOrder c ∧
          ((path.capFactors=capCalendar G.b S.rounds g count ∧ path.OnlyRotor (RotorSpec.ofRates reset)) ∧ path.GrainDates p ∧ path.kinds=Chronology.kindCalendar S.rounds count) ∧
          path.selections=Chronology.epochsSelections G run c ∧ path.recorded p ∧ path.aligned p (max 1 (max reset.bitsR (C*reset.bitsR))) := by
  induction count generalizing H j with
  | zero=>exact ⟨PUnit.unit,PUnit.unit,PUnit.unit,trivial,fun c=>⟨initial c,Chronology.Path.here,rfl,rfl,⟨⟨rfl,trivial⟩,trivial,rfl⟩,rfl,trivial,trivial⟩⟩
  | succ count ih=>
    obtain ⟨one,headOrder,inputHead,og,links⟩ := exact_period_links_dated G S ordinary reset branch p0 he hu H (by omega) initial
    let next c:=(links c).choose
    obtain ⟨rest,tailOrder,inputTail,rg,ends⟩ := ih (one.finish G hu he) (j:=j+1) (by omega) next
    refine ⟨⟨one,rest⟩,⟨headOrder,tailOrder⟩,⟨inputHead,inputTail⟩,⟨og,rg⟩,?_⟩
    intro c
    let mid:=Chronology.epochsSource G rest c
    obtain ⟨a,rankA,inputA,capA,sel,recs,aok⟩:=(links mid).choose_spec
    obtain ⟨target,b,rankB,inputB,capB,sels,recsB,bok⟩:=ends c
    have calendarStep : Chronology.kindPeriod S.rounds ++ Chronology.kindCalendar S.rounds count =
        Chronology.kindCalendar S.rounds (count+1) := by
      simp [Chronology.kindCalendar, List.replicate_succ]
    have endAge : j+(count+1)=j+1+count := by omega
    rw [endAge]
    exact ⟨target,a.append b,(a.ranked_append b).trans (congrArg₂ List.append rankA rankB),
      (a.inputRanked_append b).trans (congrArg₂ List.append inputA inputB),
      ⟨⟨(a.capFactors_append b).trans (congrArg₂ List.append capA.1.1 capB.1.1), a.onlyRotor_append b _ capA.1.2 capB.1.2⟩,
        (a.grainDates_append b p).2 ⟨capA.2.1,capB.2.1⟩,
        (a.kinds_append b).trans ((congrArg₂ List.append capA.2.2 capB.2.2).trans calendarStep)⟩,
      (a.selections_append b).trans (congrArg₂ List.append sel sels),
      a.recorded_append b p recs recsB,Chronology.Path.aligned_append p _ a b aok bok⟩

theorem exact_epochs_links_joint (H : Histories F d P bits) {j count : ℕ} (total : j+count≤S.height)
    (initial : ∀c,Reached (H.state c) G price ε S k (j*(S.rounds+1)) (z (j*(S.rounds+1))) 3 wire s) :
    ∃run : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) count H,
      ∃order inputOrder : DescentTerminalEpochDecoder.EpochOrders G hu he run,Epochs.Grains reset.board reset.bitsR period j run ∧ ∀c,
      ∃target : Reached ((Epochs.finish G hu he run).state c) G price ε S k ((j+count)*(S.rounds+1)) (z ((j+count)*(S.rounds+1))) 3 wire s,
        ∃path : Chronology.Path (initial (Chronology.epochsSource G run c)) target,
          path.ranked=Chronology.epochsRanked G run order c ∧
          path.inputRanked=Chronology.epochsRanked G run inputOrder c ∧
          (path.capFactors=capCalendar G.b S.rounds g count ∧ path.OnlyRotor (RotorSpec.ofRates reset)) ∧
          path.selections=Chronology.epochsSelections G run c ∧ path.recorded p ∧ path.aligned p (max 1 (max reset.bitsR (C*reset.bitsR))) := by
  obtain ⟨run,ord,inp,grains,rows⟩:=exact_epochs_links_dated G S ordinary reset branch p0 he hu H total initial
  refine ⟨run,ord,inp,grains,fun c=>?_⟩
  obtain ⟨target,path,ranks,inputs,fees,rest⟩:=rows c
  exact ⟨target,path,ranks,inputs,fees.1,rest⟩

theorem exact_epochs_links (H : Histories F d P bits) {j count : ℕ} (total : j+count≤S.height)
    (initial : ∀c,Reached (H.state c) G price ε S k (j*(S.rounds+1)) (z (j*(S.rounds+1))) 3 wire s) :
    ∃run : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) count H,
      ∃order : DescentTerminalEpochDecoder.EpochOrders G hu he run,Epochs.Grains reset.board reset.bitsR period j run ∧ ∀c,
      ∃target : Reached ((Epochs.finish G hu he run).state c) G price ε S k ((j+count)*(S.rounds+1)) (z ((j+count)*(S.rounds+1))) 3 wire s,
        ∃path : Chronology.Path (initial (Chronology.epochsSource G run c)) target,
          path.ranked=Chronology.epochsRanked G run order c ∧
          path.selections=Chronology.epochsSelections G run c ∧ path.recorded p ∧ path.aligned p (max 1 (max reset.bitsR (C*reset.bitsR))) := by
  obtain ⟨run,order,_,grains,links⟩:=exact_epochs_links_joint G S ordinary reset branch p0 he hu H total initial
  refine ⟨run,order,grains,fun c=>?_⟩
  obtain ⟨target,path,ranks,_,_,facts⟩:=links c
  exact ⟨target,path,ranks,facts⟩

/-- A single genuine history tree and price are maintained from the first
source through every ordinary choice and every paid reentry. -/
theorem exact_epochs (H : Histories F d P bits) {j count : ℕ} (total : j+count≤S.height)
    (initial : ∀c,Nonempty (Reached (H.state c) G price ε S k (j*(S.rounds+1)) (z (j*(S.rounds+1))) 3 wire s)) :
    ∃run : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) count H,Epochs.Grains reset.board reset.bitsR period j run ∧ ∀c, Nonempty
      (Reached ((Epochs.finish G hu he run).state c) G price ε S k ((j+count)*(S.rounds+1))
        (z ((j+count)*(S.rounds+1))) 3 wire s) := by
  obtain ⟨r,_,grains,links⟩ := exact_epochs_links G S ordinary reset branch p0 he hu H total (fun c=>(initial c).some)
  exact ⟨r,grains,fun c=>⟨(links c).choose⟩⟩

end

include ordinary reset p0 in
/-- The initial branches use the immutable source header's edge and host ordinals. -/
theorem source_reached {cp p' : ℕ} (X : Approximation F cp p') (budget : 10*(X.size+1)≤S.initialSites)
    (c : (initialGroup X S.copies s).Choice) :
    Nonempty (Reached ((initialGroup X S.copies s).state c) G price ε S k 0 (z 0) 3 wire s) := by
  have hfield : 0 < k := by
    rw [ordinary.adr]
    unfold groupBits
    omega
  obtain ⟨reached, _link⟩ := Chronology.initial_link X G S (S.grain_positive G.base_pos p0 0)
    hfield reset.height reset.seed ordinary.radix ordinary.adr budget c
  simpa only [AtomSchedule.firstWidth, Nat.cast_pow] using (Nonempty.intro reached)

end
end Hierarchy.DescentSixParty

end OAI
