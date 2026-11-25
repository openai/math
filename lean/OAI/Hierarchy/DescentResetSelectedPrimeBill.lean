import OAI.Hierarchy.DescentResetPrimeTariff
import OAI.Hierarchy.DescentResetSelectedAtlasTraffic

namespace OAI
/-! The selected input pointers are exactly the readdressed previous venue
passed to the original calendar's estimator program. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler TerminalScale DescentDatedAddressBook DescentPackedWalsh DescentStaticWordColumn ProtocolRAM Filter
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (S : AtomSchedule) (k tb i p f g drift degree h previous nextM C packet oldLanes primitiveLanes printedBits : ℕ)
    (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ)
local notation "date" => PhysicalReset.selected G S board k tb i p f g drift degree h previous nextM C packet
  oldLanes primitiveLanes printedBits old io.wire io.roster floor
local notation "cut" => PhysicalReset.receiverCut G S board k tb i p f g drift degree h previous nextM C packet
  oldLanes primitiveLanes printedBits old

theorem selected_calendar_data :
    ∃raw : ℕ→ℕ→Bank, date=PhysicalReset.fromCalendar S k tb i G.b p f old.degree h cut
      (date).successor.middle.stencil.n (date).successor.middle.stencil.t (capCalendar G.b S.rounds g S.height)
      raw io.roster (date).successor := by
  let L := (date).ingress
  let source (x j : ℕ) := if hx : x < 2^L.k then
    if hj : j < 2*L.cap then L.tokens floor (⟨x,hx⟩,⟨j,hj⟩) else io.wire x j
    else io.wire x j
  exact ⟨source,rfl⟩

section
variable {P : Type} {degree₀ : ℕ} {bs : P→ℕ} (W : MarkedWorld F degree₀ P bs) (q ε : ℝ)

theorem selected_prime_date_tariff_all (t f g reset τ B D n d C z ratio saving : ℕ)
    (tailPos : 0 < τ) (den : 0 < B)
    (cutoff : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g) ≤ B) :
    ∀ᶠ h : ℕ in atTop,∀ (P₀ : Type) (d₀ : ℕ) (bs₀ : P₀→ℕ) (world : MarkedWorld F d₀ P₀ bs₀) (q₀ ε₀ : ℝ),∀ copies i p w state wire hist : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let tb:=tail τ J
      let S:=stageNumbers G t J f g reset copies tb
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      ∀(r : Reached world G q₀ ε₀ S k i state D wire hist) (rates : ResetRates G S k D n d C f g z tb)
        (drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ)
        (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ) (count : Bank),
      let prev:=resetCut S k tb p f h i
      let a:=PhysicalReset.selected G S rates.board k tb i p f g drift degree h prev nextM C packet
        oldLanes primitiveLanes printedBits old io.wire io.roster floor
      let src:=a.ingress.source floor
      let start:=a.stageStart floor
      let unit:=PhysicalReset.primeUnit G t f g reset τ B D ratio J
      i ≤ S.length → p ≤ h → 2^h ≤ copies → w ≤ ratio*h → old.degree=D →
      r.placement.cap=((capCalendar G.b S.rounds g S.height).take i).prod*256 →
      a.PrimeRoom start src count (S.groupCount i) D w →
      (a.primeTicks start (S.groupCount i) D w+7*names (a.prime start src count (S.groupCount i) D w))*w ≤
        S.hostSize i*h*unit+S.hostSize i*(S.groupCount i*S.radix)*unit+2*(copies/(2^J)^saving) := by
  filter_upwards [PhysicalReset.prime_date_tariff G t f g reset τ B D ratio saving tailPos den cutoff] with h estimate
  intro P₀ d₀ bs₀ world q₀ ε₀ copies i p w state wire hist J tb S k r rates drift degree nextM packet oldLanes primitiveLanes printedBits
    old io floor count prev a src start unit age payload ambient hardware degreeAt capEq ready
  let chosen:=PhysicalReset.receiverCut G S rates.board k tb i p f g drift degree h prev nextM C packet
    oldLanes primitiveLanes printedBits old
  obtain ⟨raw,source⟩:=selected_calendar_data G rates.board S k tb i p f g drift degree h prev nextM C packet
    oldLanes primitiveLanes printedBits old io floor
  change a=PhysicalReset.fromCalendar S k tb i G.b p f old.degree h chosen a.successor.middle.stencil.n
    a.successor.middle.stencil.t (capCalendar G.b S.rounds g S.height) raw io.roster a.successor at source
  rw [degreeAt] at source
  have bounds:((capCalendar G.b S.rounds g S.height).take i).prod*256 ≤ 2^(8+(S.capGain-(G.b+3))*i):=by
    rw [←capEq];exact r.valid.bundleCapacity
  have actual:=estimate copies i p w chosen a.successor.middle.stencil.n a.successor.middle.stencil.t
    (capCalendar G.b S.rounds g S.height) raw io.roster a.successor start src count
  rw [←source] at actual
  exact actual age payload ambient hardware bounds ready

theorem selected_prime_date_tariff (t f g reset τ B D n d C z ratio saving : ℕ)
    (tailPos : 0 < τ) (den : 0 < B)
    (cutoff : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g) ≤ B) :
    ∀ᶠ h : ℕ in atTop,∀ copies i p w state wire hist : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let tb:=tail τ J
      let S:=stageNumbers G t J f g reset copies tb
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      ∀(r : Reached W G q ε S k i state D wire hist) (rates : ResetRates G S k D n d C f g z tb)
        (drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ)
        (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ) (count : Bank),
      let prev:=resetCut S k tb p f h i
      let a:=PhysicalReset.selected G S rates.board k tb i p f g drift degree h prev nextM C packet
        oldLanes primitiveLanes printedBits old io.wire io.roster floor
      let src:=a.ingress.source floor
      let start:=a.stageStart floor
      let unit:=PhysicalReset.primeUnit G t f g reset τ B D ratio J
      i ≤ S.length → p ≤ h → 2^h ≤ copies → w ≤ ratio*h → old.degree=D →
      r.placement.cap=((capCalendar G.b S.rounds g S.height).take i).prod*256 →
      a.PrimeRoom start src count (S.groupCount i) D w →
      (a.primeTicks start (S.groupCount i) D w+7*names (a.prime start src count (S.groupCount i) D w))*w ≤
        S.hostSize i*h*unit+S.hostSize i*(S.groupCount i*S.radix)*unit+2*(copies/(2^J)^saving) := by
  exact (selected_prime_date_tariff_all G t f g reset τ B D n d C z ratio saving tailPos den cutoff).mono fun _ h=>h P _ bs W q ε

end
end
end Hierarchy.DescentSixParty.NativePitch

end OAI
