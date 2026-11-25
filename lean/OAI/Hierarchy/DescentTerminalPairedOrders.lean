import OAI.Hierarchy.DescentTerminalEpochLocalProfiles
import OAI.Hierarchy.DescentTerminalTraceSum

namespace OAI
/-! # The packed input and structural output may name the same matched pair differently -/
namespace Hierarchy.DescentTerminalEpochDecoder
open DescentTerminalEpochChart DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentTerminalEpochFlags DescentKernelHistory.BitDescription
open scoped Classical BigOperators
noncomputable section

variable {S Z U : Type} {bits : Z→S→Bool} {ok : (S→Bool)→Prop} {src : U→Z}

def accepted (b : Chart bits ok src) := {z : b.Pin→Bool // ∃t,b.read z=some t}

def honest (b : Chart bits ok src) : U ≃ accepted b where
  toFun t:=⟨b.store t,t,(b.read_iff _ _).mpr rfl⟩
  invFun z:=z.property.choose
  left_inv t:=by
    let a : accepted b:=⟨b.store t,t,(b.read_iff _ _).mpr rfl⟩
    change a.property.choose=t
    exact Option.some.inj (a.property.choose_spec.symm.trans ((b.read_iff _ _).mpr rfl))
  right_inv z:=Subtype.ext ((b.read_iff _ _).mp z.property.choose_spec).symm

/-- Both charts address the same choice fiber, including in positive characteristic.
The equivalence is used only to evaluate the Boolean sum. -/
def sameChoice (input structural : Chart bits ok src) : accepted input ≃ accepted structural :=
  (honest input).symm.trans (honest structural)

theorem sameChoice_seed (input structural : Chart bits ok src) (a : accepted input) (s : S) :
    ((sameChoice input structural a).val (structural.seed s))=a.val (input.seed s) := by
  let t:=a.property.choose
  have fixed : a.val=input.store t:=(input.read_iff _ _).mp a.property.choose_spec
  change structural.store t (structural.seed s)=a.val (input.seed s)
  rw [structural.original,fixed,input.original]

theorem weight_sum {F : Type} [AddCommMonoid F] [Fintype U] (b : Chart bits ok src) (weight : U→F) :
    (∑z : b.Pin→Bool,(b.read z).elim 0 weight)=∑t,weight t := by
  apply DescentTerminalHost.sum_decoded b.read b.once _ weight
  · intro a none_;rw [none_];rfl
  · intro a t hit;rw [hit];rfl

variable {F P : Type} [Field F] {d : ℕ} {bs : P→ℕ} {ε : ℝ} {G : PoweredGadget F}

theorem same_profile (v : Selection F P d bs G ε) (input structural : ScanNumbers v.nonneg v.stage)
    (e : (scannedRows v.nonneg v.stage).pairs) :
    issuedProfile G ⟨v,input⟩ (input e).val=issuedProfile G ⟨v,structural⟩ (structural e).val := by
  change profileAt input _ _=profileAt structural _ _
  rw [profileAt_row,profileAt_row]

/-- The stage's actual selected world consumes the very profiles read from
the packed coordinates. No relocation or copy of the whole bank is needed. -/
theorem actual_state (v : Selection F P d bs G ε) (input : ScanNumbers v.nonneg v.stage) :
    let rows:=scannedRows v.nonneg v.stage
    let choice:=v.choice
    let read:=fun e=>DescentTerminalEpochFlags.decode G.C (issuedProfile G ⟨v,input⟩ (input e).val)
    (∀e,read e=some (rows.profile choice e)) ∧
      (v.stage.result v.nonneg).state choice=
        v.world.selected G rows.pick (fun _=>v.stage.z) (fun _=>v.stage.unitPos) rows.fit rows.pack (rows.profile choice) := by
  refine ⟨fun e=>?_,(scannedRows v.nonneg v.stage).state _⟩
  change decode G.C (profileAt input _ (input e).val)=_
  rw [profileAt_row,decode_encode]

theorem schedule_forget {u : ℝ} {he : 0≤ε} {H : Histories F d P bs}
    {t : ℕ} (s : Schedule G (u:=u) he t H) (o : ScheduleOrders G he s)
    (c : (Schedule.finish G he s).Choice) :
    (rankedSchedule he s o c).map Sigma.fst=scheduled he s c := by
  induction t generalizing H with
  | zero=>rfl
  | succ t ih=>
    obtain ⟨one,tail⟩ := s
    simp only [rankedSchedule,scheduled,List.map_cons,ih tail o.2 c]

theorem epochs_forget {u : ℝ} {hu : 0≤u} {he : 0≤ε} {H : Histories F d P bs}
    {t h C Ht J : ℕ} (s : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H)
    (o : EpochOrders G hu he s) (c : (Epochs.finish G hu he s).Choice) :
    (epochsRanked G s o c).map Sigma.fst=epochsSelections G s c := by
  induction J generalizing H with
  | zero=>rfl
  | succ j ih=>
    simp only [epochsRanked,epochsSelections,List.map_append,ih s.2 o.2 c]
    rw [schedule_forget s.1.subrounds o.1 (epochsSource G (J:=j) (H:=s.1.finish G hu he) s.2 c)]

end
end Hierarchy.DescentTerminalEpochDecoder

namespace Hierarchy.DescentBundleHistory
open DescentSixParty DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalEpochDecoder DescentTerminalEpochChart DescentTerminalEpochBits
open DescentSeedRoot Catalyst CatalystSubstitution CorrectionBatch CorrectionFrame Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "seedWidth" => S.firstWidth G.b p
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "rs" => (cert).choose
local notation "final" => Epochs.finish G _ _ rs
variable (w : ℕ) (word : S.firstWidth G.b p < 2^w)
variable (o : EpochOrders G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose)
local notation "b" => actualWith G _ _ X S.copies seedWidth w word rs o

theorem inputChart_coeff (x : Port ((S.copies*seedWidth)*nP) (copiesWidth (S.copies*seedWidth) X.width)→Bool) :
    let pins:=packagePins X S.copies seedWidth x
    let weight:=fun c : (final).Choice=>(final).weight c*((final).state c).value pins
    (∑a : (b).Pin→Bool,((b).read a).elim 0 weight)=(independentCopies (S.copies*seedWidth) X).coeff x := by
  dsimp only
  rw [weight_sum]
  exact (cert).choose_spec.2.1 x

theorem inputChart_fields (z : (b).Pin→Bool) (t : (final).Choice) (hit : (b).read z=some t) :
    (b).layout.map (rawAt z)=(Chronology.epochsRanked G rs o t).map (issuedProfile G) := by
  rw [((b).read_iff z t).mp hit]
  have rows:=epochs_profiles G _ _ rs o (seedChart X S.copies seedWidth w word) t
  exact rows

theorem inputChart_card :
    Fintype.card (b).Pin ≤ 80*S.copies*(X.size+1)*((seedWidth).log2+1)+(S.length*S.batch)*DescentTerminalEpochBits.width G.C := by
  have bill:=epochsWith_size G _ _ rs o (seedChart X S.copies seedWidth w word)
  change Fintype.card (b).Pin=Fintype.card (Select X S.copies seedWidth)+epochSeats G _ _ rs*DescentTerminalEpochBits.width G.C at bill
  rw [bill]
  exact Nat.add_le_add (select_bound X S.copies seedWidth)
    (Nat.mul_le_mul_right _ (normalizedSeats X G S ordinary reset branch positive room shorten))

local notation "packedOrd" => normalizedIssuedInputOrders X G S ordinary reset branch positive room shorten
local notation "packChart" => actualWith G _ _ X S.copies seedWidth w word rs packedOrd

/-- This is the input order actually issued by the very same chronological
run that witnesses the coefficient identity. -/
def normalizedPackedChart := packChart

theorem packedChart_once (c : (final).Choice) : ∃!z,(packChart).read z=some c := (packChart).once c

theorem packedChart_coeff (x : Port ((S.copies*seedWidth)*nP) (copiesWidth (S.copies*seedWidth) X.width)→Bool) :
    let pins:=packagePins X S.copies seedWidth x
    let weight:=fun c : (final).Choice=>(final).weight c*((final).state c).value pins
    (∑a : (packChart).Pin→Bool,((packChart).read a).elim 0 weight)=(independentCopies (S.copies*seedWidth) X).coeff x :=
  inputChart_coeff X G S ordinary reset branch positive room shorten w word packedOrd x

theorem packedChart_fields (z : (packChart).Pin→Bool) (c : (final).Choice) (hit : (packChart).read z=some c) :
    let t:=normalizedIssuedRows X G S ordinary reset branch positive room shorten c
    (packChart).layout.map (rawAt z)=t.path.inputRanked.map (issuedProfile G) := by
  dsimp only
  rw [normalizedIssuedInputRanked]
  exact inputChart_fields X G S ordinary reset branch positive room shorten w word packedOrd z c hit

theorem packedChart_seed (z : (packChart).Pin→Bool) (c : (final).Choice) (hit : (packChart).read z=some c)
    (key : CountKey X S.copies) :
    (rawCount X (z∘(packChart).seed) key).val=selected X (Epochs.seedChoice G _ _ rs c) key :=
  actualWith_seed G _ _ X S.copies seedWidth w word rs packedOrd z c hit key

theorem packedChart_card : Fintype.card (packChart).Pin ≤
    80*S.copies*(X.size+1)*((seedWidth).log2+1)+(S.length*S.batch)*DescentTerminalEpochBits.width G.C :=
  inputChart_card X G S ordinary reset branch positive room shorten w word packedOrd

theorem packedChart_prefix (z : (packChart).Pin→Bool) :
    let c:=(actualRoute G _ _ X S.copies seedWidth w word rs packedOrd).follow z
    let issued:=normalizedIssuedRows X G S ordinary reset branch positive room shorten c
    List.IsPrefix ((packChart).counts z) (issued.path.selections.map (selectionCount G)) := by
  let c:=(actualRoute G _ _ X S.copies seedWidth w word rs packedOrd).follow z
  let issued:=normalizedIssuedRows X G S ordinary reset branch positive room shorten c
  change List.IsPrefix ((packChart).counts z) (issued.path.selections.map (selectionCount G))
  rw [issued.selections]
  exact raw_prefix G _ _ X S.copies seedWidth w word rs packedOrd z

end
end Hierarchy.DescentBundleHistory

end OAI
