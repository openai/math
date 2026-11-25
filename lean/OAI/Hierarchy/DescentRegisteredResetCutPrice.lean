import OAI.Hierarchy.DescentRegisteredResetDatePrice
import OAI.Hierarchy.DescentRegisteredResetGeometry
import OAI.Hierarchy.DescentRegisteredCutInvoice
import OAI.Hierarchy.DescentReachedCutDegree

namespace OAI
/-! Actual fixed menu and budgets for the reset projection of a named history. -/
namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset Chronology Chronology.RegisterTimeline
open DescentPacking.PackedMatch.Local.Stage DescentPrimitivePalette DescentHostDegree Filter NativePitch
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (K : Parameters)
variable (τ B h copies p w degreeLimit : ℕ)
local notation "J" => Nat.log 2 h/(2*B)
local notation "tb" => tail τ J
local notation "S" => stageNumbers G K.t J K.f K.g K.reset copies tb
local notation "k" => groupBits K.t J (hostRate K.t K.reset) (capRate G K.t K.g) (cutRate K.t K.f K.g)
variable (ordinary : ℕ→Dated.Ordinary) (seats profile : ℕ→ℕ) (header : ℕ)
local notation "b₀" => (⟨board,op,K.g,tb,p,K.f,K.drift,degreeLimit,h,seats,ordinary,profile,header⟩ : Menu n d)
variable {P : Type} [Fintype P] {d₀ : ℕ} {bits : P→ℕ} {wire hist final : ℕ} {q ε : ℝ} {C : Type*}
    (ts : C→RunTrace G q ε
      (stageNumbers G K.t (Nat.log 2 h/(2*B)) K.f K.g K.reset copies (tail τ (Nat.log 2 h/(2*B))))
      (groupBits K.t (Nat.log 2 h/(2*B)) (hostRate K.t K.reset) (capRate G K.t K.g) (cutRate K.t K.f K.g)) wire hist final bits d₀) (initial : Position) (i : ℕ)
local notation "current" => calendar (w:=w) ts b₀ initial i
local notation "prev" => (current).ports
local notation "near" => (prev).priorStart k (current).floor
local notation "s" => (S).firstWidth G.b p
local notation "Z" => (S).grainAt G.b p 0
local notation "outer" => scheduledAtPorts G S board k tb i p K.f K.g K.drift degreeLimit h ordinary op s Z prev (current).floor
variable (rates : ResetRates G
      (stageNumbers G K.t (Nat.log 2 h/(2*B)) K.f K.g K.reset copies (tail τ (Nat.log 2 h/(2*B))))
      (groupBits K.t (Nat.log 2 h/(2*B)) (hostRate K.t K.reset) (capRate G K.t K.g) (cutRate K.t K.f K.g)) K.degree n d op.C K.f K.g K.rate (tail τ (Nat.log 2 h/(2*B))))
    (boardAt : rates.board=board)

include rates boardAt in
omit [Fintype P] in
theorem trace_reset_bill (lead rate saving : ℕ)
    (price : ∀a : Sample G board op K τ B h,a.Geometry→a.ReachedAt→
      a.code.tariff ≤ a.hostWork*(lead*scale J rate)+a.groupWork*(lead*scale J rate)+a.copies/(2^J)^saving)
    (rounds : atRound K.t=K.degree) (caps : ∀c,(ts c).path.capFactors=capCalendar G.b K.t K.g J)
    (seed : ∀c,(ts c).first.placement.cap=256) (seedDeg : ∀c,(ts c).firstDegree=3)
    (kinds : ∀c,(ts c).path.kinds=kindCalendar K.t J) (active : i < (S).length)
    (cursor : RegisterTimeline.Geometry G S b₀ k w i current)
    (bounded : degreeLimit ≤ K.bound) (input : p ≤ h) (ambient : 2^h ≤ copies)
    (bus : w ≤ K.ratio*h) (wide : h ≤ w) (degreeWord : (prev).venue.degree+1 < 2^w)
    (standard : ∀j < (S).length,j%((S).rounds+1)≠(S).rounds → (ordinary j).payload=h ∧
       (ordinary j).unit=(DonorDate.atDate G S K.g k j p).amount)
    (next : 0 < incoming S k tb p K.f h ordinary (i+1))
    (data : (prev).ArchiveDensity ((S).groupCount i) h (scale J K.archive) (scale J K.archive))
    (resetRoom : i%((S).rounds+1)=(S).rounds →
       8*(outer).inner.successor.groupWidth ≤ h ∧ (outer).inner.successor.groupWidth ≤ scale J K.receiver ∧
       (outer).fullEnd < 2^w)
    (event : RunTrace.Events ts i) :
    resetBill ts b₀ initial (w:=w) i ((S).hostSize i*h*(lead*scale J rate)+
       (S).hostSize i*((S).groupCount i*(S).radix)*(lead*scale J rate)+copies/(2^J)^saving) event :=by
  obtain ⟨c,event⟩:=event
  cases event with
  | ordinary before ticket after joined=>trivial
  | @reset U z D _ _ _ _ _ _ _ src ctl before closed after cut=>
    intro cap space
    let a : Sample G board op K τ B h:=⟨copies,i,p,w,degreeLimit,current,ordinary,rates,boardAt,space,cap⟩
    have stamp:=reset_kind_on_cut closed before after cut (kinds c)
    have boundary:=reset_slot_index K.t J i stamp
    have frame:=(resetRoom boundary)
    have geo:=a.of_cursor seats profile header cursor active boundary rounds bounded input ambient bus wide degreeWord
      standard next data frame.1 frame.2.1 frame.2.2
    let tailPath:=(Path.here.reset closed).append after
    have joined:before.append tailPath=(ts c).path:=(Path.append_cut_assoc before (Path.here.reset closed) after).symm.trans cut
    have signed:D=K.degree:=((ts c).degree_before (seedDeg c) (kinds c) before tailPath joined).trans
      ((congrArg atRound boundary).trans rounds)
    have reached:=a.reached_of_path src before tailPath signed (seed c) ((congrArg Path.capFactors joined).trans (caps c))
    exact price a geo reached

end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI
