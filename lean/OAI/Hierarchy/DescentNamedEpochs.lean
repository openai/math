import OAI.Hierarchy.DescentNamedSeedChronology
import OAI.Hierarchy.DescentSeedChosenOrigin

namespace OAI
/-! # Issued epochs starting in the physical order read by the first matching pass -/

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentHostDegree DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch CorrectionFrame
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
local notation "epochWire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "unitPrice" => (1/((s:ℝ)*(epochWire:ℝ)):ℝ)
local notation "ε" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => unitPrice*(epochWire:ℝ)
local notation "resetDepth" => GroupStage.depthBound (atRound S.rounds) n f g
local notation "raw" => initialGroup X S.copies s
local notation "E" => Fintype.card (Port P X.width)
local notation "m" => S.initialSites
local notation "d" => S.copies*s
local notation "K" => 258*reentryRate h C+reentryExteriorRate h C 256 resetDepth

local notation "seedPorts" => (Σ _ : Fin S.copies, Fin E)
local notation "seedBits" => (fun _ : seedPorts => s*1)

/-- The endpoint witnesses, their path and the six certificates about that path.
Keeping the endpoint types parameterized lets all projections use the same path. -/
structure BranchWitness (A B : Type*) (Route : A → B → Type*)
    (Selections Recorded Aligned Calendar Grains Kinds : ∀ {a b}, Route a b → Prop) where
  origin : A
  target : B
  path : Route origin target
  selections : Selections path
  recorded : Recorded path
  aligned : Aligned path
  calendar : Calendar path
  issuedGrains : Grains path
  kinds : Kinds path

abbrev BranchData (radix : S.radix=2^k) (R : ℕ) (choice : (raw).Choice)
    (W : MarkedWorld F 0 seedPorts seedBits)
    (published : List (Chronology.Selection F seedPorts 0 seedBits G ε)) :=
  BranchWitness
    (Origin (G:=G) (S:=S) («s»:=s) (q:=unitPrice) (fee:=ε) (z:=S.grainAt G.b p 0)
      (wire:=epochWire) X choice (S.initialDigits radix))
    (Reached W G unitPrice ε S k S.length p 3 epochWire s)
    (fun origin target => Chronology.Path origin.source target)
    (fun {_ _} path => path.selections=published)
    (fun {_ _} path => path.recorded p)
    (fun {_ _} path => path.aligned p R)
    (fun {_ _} path => path.capFactors=capCalendar G.b S.rounds g S.height)
    (fun {_ _} path => path.GrainDates p)
    (fun {_ _} path => path.kinds=Chronology.kindCalendar S.rounds S.height)

/-- Recover all three indices from the same run and terminal choice. -/
abbrev Branch {he : 0 ≤ ε} {hu : 0 ≤ u} (radix : S.radix=2^k) (R : ℕ)
    (r : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) S.height
      (initial X S.copies s (S.groupCount 0) k (S.initialDigits radix)))
    (c : (Epochs.finish G hu he (J:=S.height) (h:=h) (C:=C) (t:=S.rounds) (Ht:=resetDepth)
      (H:=initial X S.copies s (S.groupCount 0) k (S.initialDigits radix)) r).Choice) :=
  BranchData X G S (p:=p) (g:=g) radix R
    (Chronology.epochsSource G (hq:=hu) (hf:=he) (J:=S.height) (h:=h) (C:=C) (t:=S.rounds) (ht:=resetDepth)
      (H:=initial X S.copies s (S.groupCount 0) k (S.initialDigits radix)) r c) ((Epochs.finish G hu he (J:=S.height) (h:=h) (C:=C) (t:=S.rounds) (Ht:=resetDepth)
      (H:=initial X S.copies s (S.groupCount 0) k (S.initialDigits radix)) r).state c)
    (Chronology.epochsSelections G (hq:=hu) (hf:=he) (J:=S.height) (h:=h) (C:=C) (t:=S.rounds) (ht:=resetDepth)
      (H:=initial X S.copies s (S.groupCount 0) k (S.initialDigits radix)) r c)

def Branch.archive {he : 0 ≤ ε} {hu : 0 ≤ u} {radix : S.radix=2^k} {R : ℕ}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) S.height
      (initial X S.copies s (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p) :
    Chronology.Archive ((Epochs.finish G hu he r).state c) :=
  b.path.archive p hp b.origin.archive (b.path.recorded_whole p b.recorded)

set_option maxHeartbeats 2000000 in
/-- Both the exact independent-copy coefficients and the terminal frontier
estimate refer to the same history tree, in every branch of its terminal
profile. Total widths include physical old tethers. -/
theorem normalized_epochs_issued_joint (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
    (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ m)
    (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2) :
    let he : 0 ≤ ε := by positivity
    let hu : 0 ≤ u := by positivity
    ∃r : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) S.height
        (initial X S.copies s (S.groupCount 0) k (S.initialDigits ordinary.radix)),
      let terminal := Epochs.finish G hu he r
      Epochs.Grains reset.board reset.bitsR (fun j slot=>S.grainAt G.b p (j*(S.rounds+1)+slot)) 0 r ∧
      (∀x : Port (d*P) (copiesWidth d X.width)→Bool,
        terminal.value (packagePins X S.copies s x)=(independentCopies d X).coeff x) ∧
      ∃order inputOrder : DescentTerminalEpochDecoder.EpochOrders G hu he r,
        ∀c, ∃b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) ordinary.radix (max 1 (max reset.bitsR (C*reset.bitsR))) r c,
        b.path.ranked=Chronology.epochsRanked G (hq:=hu) (hf:=he) (J:=S.height) (h:=h) (C:=C) (ht:=resetDepth) (t:=S.rounds)
      (H:=(initial X S.copies s (S.groupCount 0) k (S.initialDigits ordinary.radix))) r order c ∧
        b.path.inputRanked=Chronology.epochsRanked G (hq:=hu) (hf:=he) (J:=S.height) (h:=h) (C:=C) (ht:=resetDepth) (t:=S.rounds)
      (H:=(initial X S.copies s (S.groupCount 0) k (S.initialDigits ordinary.radix))) r inputOrder c ∧
        (b.path.capFactors=capCalendar G.b S.rounds g S.height ∧ b.path.OnlyRotor (RotorSpec.ofRates reset)) ∧
        (terminal.state c).tetherWidth ≤ d*E ∧
        ((terminal.state c).liveWidth:ℝ) ≤ (d:ℝ)*((m:ℝ)/S.epochPower+2*K*((E:ℝ)+(m:ℝ)/S.epochPower)) := by
  intro he hu
  let start:=initial X S.copies s (S.groupCount 0) k (S.initialDigits ordinary.radix)
  have hs:=Nat.mul_pos (S.grain_positive G.base_pos positive 0) G.base_pos
  change 0 < s at hs
  have hw : 0<epochWire := Nat.pow_pos (Nat.two_pow_pos _)
  have hwR : 0 < (S.epochPower : ℝ)^S.priceExponent := by exact_mod_cast hw
  have scale : u=1/(s:ℝ) := by field_simp [(Nat.cast_pos.mpr hs : (0 : ℝ) < s).ne',hwR.ne']
  have smaller : Fintype.card X.network.copyGraph.Edge ≤ m := by
    have inj : Fintype.card X.network.copyGraph.Edge ≤ Fintype.card (Wire X.network.copyGraph) :=
      Fintype.card_le_of_injective (fun e=>Sum.inl e) Sum.inl_injective
    have cost:=(«initialize» X).2.1
    omega
  let E₀ := (S.copies:ℝ)*E
  let X₀ := (S.copies:ℝ)*m
  have first (c : start.Choice) : u*(start.state c).tetherWidth ≤ E₀ ∧ u*(start.state c).liveWidth ≤ X₀ := by
    change (initialGroup X S.copies s).Choice at c
    change u*(initial_world X S.copies s (S.groupCount 0) k (S.initialDigits ordinary.radix) c).tetherWidth ≤ E₀ ∧
      u*(initial_world X S.copies s (S.groupCount 0) k (S.initialDigits ordinary.radix) c).liveWidth ≤ X₀
    unfold initial_world
    rw [PhysicalRename.tetherWidth,PhysicalRename.liveWidth,
      initial_tetherWidth X S.copies s c, initial_liveWidth X S.copies s c, scale]
    push_cast
    constructor
    · dsimp [E₀]
      field_simp [(Nat.cast_pos.mpr hs : (0 : ℝ) < s).ne']; ring_nf; exact le_rfl
    · have sm : (Fintype.card X.network.copyGraph.Edge:ℝ)≤ m := by exact_mod_cast smaller
      dsimp [X₀]
      calc
        _ = (S.copies:ℝ)*Fintype.card X.network.copyGraph.Edge := by field_simp [(Nat.cast_pos.mpr hs : (0 : ℝ) < s).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left sm (by positivity)
  have field : 0 < k := by rw [ordinary.adr];unfold groupBits;omega
  let root (c : (raw).Choice) : Origin (G:=G) (S:=S) («s»:=s) (q:=unitPrice) (fee:=ε)
      (z:=S.grainAt G.b p 0) (wire:=epochWire) X c (S.initialDigits ordinary.radix) := by
    let AtPrice (price : ℝ) := Origin (G:=G) (S:=S) («s»:=s) (q:=price) (fee:=ε)
      (z:=S.grainAt G.b p 0) (wire:=epochWire) X c (S.initialDigits ordinary.radix)
    have original : AtPrice (1 / ((s : ℝ) * (((epochWire : ℕ) : ℝ)))) :=
      originalOrigin X G S (S.grain_positive G.base_pos positive 0)
        field reset.height reset.seed ordinary.radix ordinary.adr room rfl c
    have agree : 1 / ((s : ℝ) * (((epochWire : ℕ) : ℝ))) = unitPrice := by rw [Nat.cast_pow]
    exact (congrArg AtPrice agree).mp original
  have links := exact_epochs_links_dated G S ordinary reset branch positive he hu start
    (j := 0) (count := S.height) (Nat.zero_add S.height).le
  rw [Nat.zero_mul, Nat.zero_add] at links
  obtain ⟨run,order,inputOrder,issued,ended⟩ := links (fun c=>(root c).source)
  refine ⟨run,issued,fun x=>(Epochs.value G hu he start run _).trans
    ((congrFun (initial_value X S.copies s (S.groupCount 0) k (S.initialDigits ordinary.radix)) _).trans
      (complete_input X S.copies s x)),order,inputOrder,?_⟩
  intro c
  have prop := ended c
  have ageEq : S.height*(S.rounds+1)=S.length := Nat.mul_comm _ _
  rw [ageEq,S.grain_terminal] at prop
  obtain ⟨target,path,ranked,inputs,factors,rows,recorded,aligned⟩ := prop
  let data : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) ordinary.radix (max 1 (max reset.bitsR (C*reset.bitsR))) run c :=
    ⟨root (Chronology.epochsSource G (hq:=hu) (hf:=he) (J:=S.height) (h:=h) (C:=C) (ht:=resetDepth) (t:=S.rounds)
      (H:=start) run c),target,path,rows,recorded,aligned,factors.1.1,factors.2.1,factors.2.2⟩
  obtain ⟨tether,core⟩ := Epochs.core G hu he start run E₀ X₀ (by dsimp [E₀];positivity)
    (by dsimp [X₀];positivity) first shorten c
  have divideWidth (width : ℕ) (budget : ℝ) (paid : u * (width : ℝ) ≤ budget) :
      (width : ℝ) / (s : ℝ) ≤ budget := by
    rw [scale, one_div_mul_eq_div] at paid
    exact paid
  have tetherDiv := divideWidth _ _ tether
  have coreDiv := divideWidth _ _ core
  have kpos : 0 ≤ K := by
    dsimp [reentryRate,splicedRate,internalRate,reentryExteriorRate,splicedExteriorRate,exteriorRate]
    positivity
  have bonus : 2*(1-(1/2:ℝ)^S.height)*K*(E₀+ε) ≤ 2*K*(E₀+ε) := by
    have a : 1-(1/2:ℝ)^S.height ≤ 1 := by linarith only [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) S.height]
    have b := mul_le_mul_of_nonneg_left a (show 0 ≤ 2*K*(E₀+ε) by dsimp [E₀];positivity)
    nlinarith only [b]
  refine ⟨data,ranked,inputs,factors.1,?_,?_⟩
  · have t := (div_le_iff₀ (Nat.cast_pos.mpr hs)).mp tetherDiv
    dsimp [E₀] at t
    norm_cast at t
    simpa [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using t
  · have e := (div_le_iff₀ (Nat.cast_pos.mpr hs)).mp (coreDiv.trans (add_le_add (le_refl _) bonus))
    convert e using 1
    dsimp [E₀,X₀,AtomSchedule.epochPower]
    push_cast
    ring

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
