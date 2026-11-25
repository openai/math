import OAI.Hierarchy.DescentWholeEpochs

namespace OAI
/-! # Normalized frontier volume and coefficients of the final physical worlds -/

namespace Hierarchy.DescentSixParty
open DescentHostDegree DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch CorrectionFrame
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "q" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "ε" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => q*(wire:ℝ)
local notation "resetDepth" => GroupStage.depthBound (atRound S.rounds) n f g
local notation "start" => initialGroup X S.copies s
local notation "E" => Fintype.card (Port P X.width)
local notation "m" => S.initialSites
local notation "d" => S.copies*s
local notation "K" => 258*reentryRate h C+reentryExteriorRate h C 256 resetDepth

/-- The real initialized parent and selected final placement, with their common native
opcode chronology. The original coefficient choice is recovered from this same run. -/
structure NativeBranch {he : 0≤ε} {hu : 0≤u} (radix : S.radix=2^k) (R : ℕ)
    (r : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) S.height start)
    (c : (Epochs.finish G hu he r).Choice) where
  source : Reached ((start).state (Chronology.epochsSource G r c)) G q ε S k 0 (S.grainAt G.b p 0) 3 wire s
  seed : Chronology.SeedLink X (Chronology.epochsSource G r c) source (S.initialDigits radix)
  target : Reached ((Epochs.finish G hu he r).state c) G q ε S k S.length p 3 wire s
  path : Chronology.Path source target
  selections : path.selections=Chronology.epochsSelections G r c
  recorded : path.recorded p
  aligned : path.aligned p R

/-- Dense scalar-node order read by the code that realizes this same final world. -/
def NativeBranch.archive {he : 0≤ε} {hu : 0≤u} {radix : S.radix=2^k} {R : ℕ}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) S.height start}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p) :
    Chronology.Archive ((Epochs.finish G hu he r).state c) :=
  b.path.archive p hp (Chronology.seedArchive X S.copies s (Chronology.epochsSource G r c)) (b.path.recorded_whole p b.recorded)

/-- Both the exact independent-copy coefficients and the terminal frontier
estimate refer to the same history tree, in every branch of its terminal
profile. Total widths include physical old tethers. -/
theorem normalized_epochs_issued_joint (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
    (branch : G.b≤2^S.capGain) (positive : 0<p) (room : 10*(X.size+1)≤ m)
    (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds≤1/2) :
    let he : 0≤ε := by positivity
    let hu : 0≤u := by positivity
    ∃r : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) S.height start,
      let terminal := Epochs.finish G hu he r
      Epochs.Grains reset.board reset.bitsR (fun j slot=>S.grainAt G.b p (j*(S.rounds+1)+slot)) 0 r ∧
      (∀x : Port (d*P) (copiesWidth d X.width)→Bool,
        terminal.value (packagePins X S.copies s x)=(independentCopies d X).coeff x) ∧
      ∃order inputOrder : DescentTerminalEpochDecoder.EpochOrders G hu he r,
        ∀c, ∃b : NativeBranch X G S ordinary.radix (max 1 (max reset.bitsR (C*reset.bitsR))) r c,
        b.path.ranked=Chronology.epochsRanked G r order c ∧
        b.path.inputRanked=Chronology.epochsRanked G r inputOrder c ∧
        (b.path.capFactors=capCalendar G.b S.rounds g S.height ∧ b.path.OnlyRotor (RotorSpec.ofRates reset)) ∧
        (terminal.state c).tetherWidth≤d*E ∧
        ((terminal.state c).liveWidth:ℝ)≤(d:ℝ)*((m:ℝ)/S.epochPower+2*K*((E:ℝ)+(m:ℝ)/S.epochPower)) := by
  intro he hu
  have hs:=Nat.mul_pos (S.grain_positive G.base_pos positive 0) G.base_pos
  change 0<s at hs
  have hw : 0<wire := Nat.pow_pos (Nat.two_pow_pos _)
  have hwR : 0 < (S.epochPower : ℝ)^S.priceExponent := by exact_mod_cast hw
  have scale : u=1/(s:ℝ) := by field_simp [(Nat.cast_pos.mpr hs : (0 : ℝ) < s).ne',hwR.ne']
  have smaller : Fintype.card X.network.copyGraph.Edge≤ m := by
    have inj : Fintype.card X.network.copyGraph.Edge≤Fintype.card (Wire X.network.copyGraph) :=
      Fintype.card_le_of_injective (fun e=>Sum.inl e) Sum.inl_injective
    have cost:=(«initialize» X).2.1
    omega
  let E₀ := (S.copies:ℝ)*E
  let X₀ := (S.copies:ℝ)*m
  have first (c : (start).Choice) : u*((start).state c).tetherWidth≤E₀ ∧ u*((start).state c).liveWidth≤X₀ := by
    rw [initial_tetherWidth,initial_liveWidth,scale]
    push_cast
    constructor
    · dsimp [E₀]
      field_simp [(Nat.cast_pos.mpr hs : (0 : ℝ) < s).ne']; ring_nf; exact le_rfl
    · have sm : (Fintype.card X.network.copyGraph.Edge:ℝ)≤ m := by exact_mod_cast smaller
      dsimp [X₀]
      calc
        _ = (S.copies:ℝ)*Fintype.card X.network.copyGraph.Edge := by field_simp [(Nat.cast_pos.mpr hs : (0 : ℝ) < s).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left sm (by positivity)
  have hk : 0 < k := by
    rw [ordinary.adr]
    unfold groupBits
    omega
  have ticket (c : (start).Choice) :
      ∃ a : Reached ((start).state c) G q ε S k 0 (S.grainAt G.b p 0) 3 wire s,
        Chronology.SeedLink X c a (S.initialDigits ordinary.radix) := by
    let SeedAtPrice (unitPrice : ℝ) : Prop :=
      ∃ a : Reached ((start).state c) G unitPrice ε S k 0 (S.grainAt G.b p 0) 3 wire s,
        Chronology.SeedLink X c a (S.initialDigits ordinary.radix)
    have raw : SeedAtPrice (1 / ((s : ℝ) * (((wire : ℕ) : ℝ)))) :=
      Chronology.initial_link X G S (S.grain_positive G.base_pos positive 0)
        hk reset.height reset.seed ordinary.radix ordinary.adr room c
    have agree : 1 / ((s : ℝ) * (((wire : ℕ) : ℝ))) = q := by rw [Nat.cast_pow]
    exact (congrArg SeedAtPrice agree).mp raw
  let root (c : (start).Choice) := (ticket c).choose
  have links := exact_epochs_links_joint G S ordinary reset branch positive he hu start
    (j := 0) (count := S.height) (Nat.zero_add S.height).le
  rw [Nat.zero_mul, Nat.zero_add] at links
  obtain ⟨run, order, inputOrder, issued, ended⟩ := links root
  refine ⟨run, issued, fun x => (Epochs.value G hu he start run _).trans
    (complete_input X S.copies s x), order, inputOrder, ?_⟩
  intro c
  have prop := ended c
  have ageEq : S.height * (S.rounds + 1) = S.length := by
    exact Nat.mul_comm _ _
  rw [ageEq, S.grain_terminal] at prop
  obtain ⟨target, path, ranked, inputs, factors, rows, recorded, aligned⟩ := prop
  let data : NativeBranch X G S ordinary.radix (max 1 (max reset.bitsR (C * reset.bitsR))) run c :=
    ⟨root (Chronology.epochsSource G run c), (ticket (Chronology.epochsSource G run c)).choose_spec,
      target, path, rows, recorded, aligned⟩
  obtain ⟨tether,core⟩ := Epochs.core G hu he start run E₀ X₀ (by dsimp [E₀];positivity)
    (by dsimp [X₀];positivity) first shorten c
  have divideWidth (width : ℕ) (budget : ℝ) (paid : u * (width : ℝ) ≤ budget) :
      (width : ℝ) / (s : ℝ) ≤ budget := by
    rw [scale, one_div_mul_eq_div] at paid
    exact paid
  have tetherDiv := divideWidth _ _ tether
  have coreDiv := divideWidth _ _ core
  have kpos : 0≤K := by
    dsimp [reentryRate,splicedRate,internalRate,reentryExteriorRate,splicedExteriorRate,exteriorRate]
    positivity
  have bonus : 2*(1-(1/2:ℝ)^S.height)*K*(E₀+ε)≤2*K*(E₀+ε) := by
    have a : 1-(1/2:ℝ)^S.height≤1 := by linarith only [pow_nonneg (by norm_num : (0:ℝ)≤1/2) S.height]
    have b := mul_le_mul_of_nonneg_left a (show 0≤2*K*(E₀+ε) by dsimp [E₀];positivity)
    nlinarith only [b]
  refine ⟨data,ranked,inputs,factors,?_,?_⟩
  · have t := (div_le_iff₀ (Nat.cast_pos.mpr hs)).mp tetherDiv
    dsimp [E₀] at t
    norm_cast at t
    simpa [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using t
  · have e := (div_le_iff₀ (Nat.cast_pos.mpr hs)).mp (coreDiv.trans (add_le_add (le_refl _) bonus))
    convert e using 1
    dsimp [E₀,X₀,AtomSchedule.epochPower]
    push_cast
    ring

theorem normalized_epochs_issued (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
    (branch : G.b≤2^S.capGain) (positive : 0<p) (room : 10*(X.size+1)≤ m)
    (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds≤1/2) :
    let he : 0≤ε := by positivity
    let hu : 0≤u := by positivity
    ∃r : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) S.height start,
      let terminal := Epochs.finish G hu he r
      Epochs.Grains reset.board reset.bitsR (fun j slot=>S.grainAt G.b p (j*(S.rounds+1)+slot)) 0 r ∧
      (∀x : Port (d*P) (copiesWidth d X.width)→Bool,
        terminal.value (packagePins X S.copies s x)=(independentCopies d X).coeff x) ∧
      ∃order : DescentTerminalEpochDecoder.EpochOrders G hu he r,
        ∀c, ∃b : NativeBranch X G S ordinary.radix (max 1 (max reset.bitsR (C*reset.bitsR))) r c,
        b.path.ranked=Chronology.epochsRanked G r order c ∧
        (terminal.state c).tetherWidth≤d*E ∧
        ((terminal.state c).liveWidth:ℝ)≤(d:ℝ)*((m:ℝ)/S.epochPower+2*K*((E:ℝ)+(m:ℝ)/S.epochPower)) := by
  intro he hu
  obtain ⟨r,grains,value,order,_,links⟩:=normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
  refine ⟨r,grains,value,order,fun c=>?_⟩
  obtain ⟨b,ranked,_,_,bounds⟩:=links c
  exact ⟨b,ranked,bounds⟩

/-- The original frontier statement, obtained from the run with its issued path. -/
theorem normalized_epochs (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
    (branch : G.b≤2^S.capGain) (positive : 0<p) (room : 10*(X.size+1)≤ m)
    (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds≤1/2) :
    let he : 0≤ε := by positivity
    let hu : 0≤u := by positivity
    ∃r : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) S.height start,
      let terminal := Epochs.finish G hu he r
      Epochs.Grains reset.board reset.bitsR (fun j slot=>S.grainAt G.b p (j*(S.rounds+1)+slot)) 0 r ∧
      (∀x : Port (d*P) (copiesWidth d X.width)→Bool,
        terminal.value (packagePins X S.copies s x)=(independentCopies d X).coeff x) ∧
      ∀c, Nonempty (Reached (terminal.state c) G q ε S k S.length p 3 wire s) ∧
        (terminal.state c).tetherWidth≤d*E ∧
        ((terminal.state c).liveWidth:ℝ)≤(d:ℝ)*((m:ℝ)/S.epochPower+2*K*((E:ℝ)+(m:ℝ)/S.epochPower)) := by
  intro he hu
  obtain ⟨r,grains,value,_,receipt⟩:=normalized_epochs_issued X G S ordinary reset branch positive room shorten
  exact ⟨r,grains,value,fun c=>⟨⟨(receipt c).choose.target⟩,(receipt c).choose_spec.2⟩⟩

end
end Hierarchy.DescentSixParty

end OAI
