import OAI.Hierarchy.DescentTerminalNativeChart
import OAI.Hierarchy.DescentMatchedRosterCount

namespace OAI
/-! # Each original selector word is the profile of its actually issued matched row -/
namespace Hierarchy.DescentTerminalEpochDecoder
open DescentSixParty DescentSixParty.Chronology DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochFlags DescentKernelHistory.BitDescription DescentPacking
open DescentInitialHost DescentSeedRoot DescentStageEdgeReceipt Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

def profileAt {I : Type} {n C : ℕ} (number : I≃Fin n) (p : I→Profile C) (i : ℕ) :=
  if h : i < n then encode (p (number.symm ⟨i,h⟩)) else 0

theorem profileAt_row {I : Type} {n C : ℕ} (number : I≃Fin n) (p : I→Profile C) (i : I) :
    profileAt number p (number i).val=encode (p i) := by simp [profileAt,(number i).isLt]

theorem profileAt_unused {I : Type} {n C : ℕ} (number : I≃Fin n) (p : I→Profile C) {i : ℕ} (tail : n≤ i) :
    profileAt number p i=0 := by simp [profileAt,not_lt.mpr tail]

def rawAt {A : Type} (z : A→Bool) (a : Source A) (j : ℕ) : ℕ :=
  if h : j < a.seats then DescentTerminalEpochBits.raw (z∘a.pin) ⟨j,h⟩ else 0

variable {F P : Type} [Field F] {d : ℕ} {portBits : P→ℕ} {u ε : ℝ}
variable (G : PoweredGadget F) (hu : 0≤u) (he : 0≤ε)

def issuedProfile (v : RankedSelection F P d portBits G ε) : ℕ→ℕ :=
  profileAt v.2 ((scannedRows v.1.nonneg v.1.stage).profile v.1.choice)

variable {S Z U : Type} {bits : Z→S→Bool} {ok : (S→Bool)→Prop} {src : U→Z}
variable (b : Chart bits ok src) {C seats : ℕ} {I Fiber : U→Type} (cnt : U→ℕ)
    (number : ∀c,I c≃Fin (cnt c)) (fit : ∀c,cnt c ≤ seats) (pf : ∀c,Fiber c≃(I c→Profile C))

theorem extend_profiles (t : Σc,Fiber c) :
    let a:=DescentTerminalEpochChart.extend b cnt number fit pf
    a.layout.map (rawAt (a.store t))=b.layout.map (rawAt (b.store t.1))++
      [profileAt (number t.1) (pf t.1 t.2)] := by
  let z:=extendedStore (seats:=seats) b cnt number pf t
  let last : Source (b.Pin⊕Pins C seats):=⟨C,seats,Sum.inr⟩
  have earlier : (b.layout.map (Source.map Sum.inl)).map (rawAt z)=b.layout.map (rawAt (b.store t.1)) := by
    rw [List.map_map]
    rfl
  have now : rawAt z last=profileAt (number t.1) (pf t.1 t.2) := by
    funext i
    by_cases h : i < seats
    · change (if ht : i < seats then raw (store (number t.1) (pf t.1 t.2)) ⟨i,ht⟩ else 0)=_
      rw [dite_eq_left h,raw_store]
      rfl
    · have off : ¬i < cnt t.1 := by have h₀:=fit t.1;omega
      simp only [rawAt,last,dite_eq_right h,profileAt,dite_eq_right off]
  change ((b.layout.map (Source.map Sum.inl)++[last]).map (rawAt z))=_
  rw [List.map_append,earlier,List.map_singleton,now]

theorem schedule_profiles {t : ℕ} {H : Histories F d P portBits} (s : Schedule G (u:=u) he t H)
    (order : ScheduleOrders G he s) {root : H.Choice→Z} (old : Chart bits ok root) (c : (Schedule.finish G he s).Choice) :
    let a:=scheduledWith G he s order old
    a.layout.map (rawAt (a.store c))=old.layout.map (rawAt (old.store (sourceChoice he s c)))++
      (rankedSchedule he s order c).map (issuedProfile G) := by
  induction t generalizing H with
  | zero=>simp [scheduledWith,sourceChoice,rankedSchedule]
  | succ t ih=>
    obtain ⟨one,rest⟩:=s
    have step:=extend_profiles old (count G he one) order.1 (count_le G he one)
      (fun x=>(scannedRows he (one.placement x)).profile) (sourceChoice he rest c)
    let middle:=extendWith G he one order.1 old
    change middle.layout.map (rawAt (middle.store _))=_ at step
    have rr:=ih rest order.2 middle c
    rw [step] at rr
    simp only [middle,scheduledWith,sourceChoice,rankedSchedule,List.map_cons,List.append_assoc,List.singleton_append,issuedProfile] at rr ⊢
    exact rr

theorem epochs_profiles {t h C Ht J : ℕ} {H : Histories F d P portBits}
    (s : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H) (order : EpochOrders G hu he s)
    {root : H.Choice→Z} (old : Chart bits ok root) (c : (Epochs.finish G hu he s).Choice) :
    let a:=epochsWith G hu he s order old
    a.layout.map (rawAt (a.store c))=old.layout.map (rawAt (old.store (epochsSource G s c)))++
      (epochsRanked G s order c).map (issuedProfile G) := by
  induction J generalizing H with
  | zero=>simp [epochsWith,epochsSource,epochsRanked]
  | succ j ih=>
    obtain ⟨one,rest⟩:=s
    have rr:=ih rest order.2 (scheduledWith G he one.subrounds order.1 old) c
    have first:=schedule_profiles G he one.subrounds order.1 old
      (epochsSource G (J:=j) (H:=one.finish G hu he) rest c)
    let more := (epochsRanked G (J:=j) (H:=one.finish G hu he) rest order.2 c).map (issuedProfile G)
    have joined := rr.trans (congrArg (fun xs => xs ++ more) first)
    simp only [more,epochsWith,epochsSource,epochsRanked,List.map_append,List.append_assoc] at joined ⊢
    exact joined

section Physical
variable {D : ℕ} {Q : Type*} {bs : Q→ℕ} (N : Network D Q bs)
    {K : Type} [Fintype K] [DecidableEq K] (core : Finset N.Edge) (home : N.Site→K)
    (color : N.Site→Bool) (B : ℕ) (rank : K↪ℕ)
set_option quotPrecheck false
local notation "T" => nativeTraffic N core home
local notation "num" => PairRAM.globalNumberBy N core home color B rank
local notation "loc" => fun c=>slabPacking T B (thinList home color c) (thickList home color c)

/-- The native source-local pair ordinal under its actual prior accepted count. -/
theorem at_local {q : ℕ} (profiles : StarKeys.NativePair N core home color B → Profile q) (c : K)
    (e : Matched T B (thinList home color c) (thickList home color c)) :
    profileAt num profiles (PairRAM.groupStartBy N core home color B rank c+
      (pairNumber (amount (live T)) (loc c).decisions e).val)=encode (profiles ⟨c,e⟩) := by
  exact profileAt_row num profiles ⟨c,e⟩

end Physical
end
end Hierarchy.DescentTerminalEpochDecoder

namespace Hierarchy.DescentBundleHistory
open DescentSixParty DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalEpochDecoder DescentTerminalEpochChart DescentTerminalEpochBits
open DescentSeedRoot Catalyst Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b≤2^S.capGain) (positive : 0<p) (room : 10*(X.size+1)≤S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds≤1/2)
set_option quotPrecheck false
local notation "s" => S.firstWidth G.b p
local notation "r" => (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
local notation "ord" => normalizedIssuedOrders X G S ordinary reset branch positive room shorten
variable (w : ℕ) (word : S.firstWidth G.b p < 2^w)
include word
local notation "b" => normalizedChart X G S ordinary reset branch positive room shorten w word

/-- At every actual issued step, the original selector has exactly the stage's
real eight-field profiles at the published ordinals, followed by zero padding. -/
theorem normalizedChart_profiles (z : (b).Pin→Bool) (t : (Epochs.finish G _ _ r).Choice) (hit : (b).read z=some t) :
    let issued:=normalizedIssuedRows X G S ordinary reset branch positive room shorten t
    (b).layout.map (rawAt z)=issued.path.ranked.map (issuedProfile G) := by
  let issued := normalizedIssuedRows X G S ordinary reset branch positive room shorten t
  change (b).layout.map (rawAt z) = issued.path.ranked.map (issuedProfile G)
  have ranked := normalizedIssuedRanked X G S ordinary reset branch positive room shorten t
  rw [ranked,((b).read_iff z t).mp hit]
  exact epochs_profiles G _ _ r ord (seedChart X S.copies s w word) t

end
end Hierarchy.DescentBundleHistory

end OAI
