import OAI.Hierarchy.TaggedWideCalendarDateWords
import OAI.Hierarchy.TaggedWideCalendarSpillAddress
import OAI.Hierarchy.TaggedWireSignedComposition
import OAI.Hierarchy.ProbeFixedWideSignedRowTariff
import OAI.Hierarchy.ProbeFixedWideSpillRowTariff
import OAI.Hierarchy.ProbeFixedWideCorrectedSpill

namespace OAI
/-! # The fixed trivalent local network at every original native date -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks ThreeFlat Routing Diagonal TraceWords
open LinearAlgebra.SpectralBooks.ChordGraph LinearAlgebra.SpectralBooks.SiteTensor
open Tagged Tagged.WideControlJoin Tagged.WideStack AdaptiveProbe ProbeStage CoreBoard HistoryRoles HistoryRoles.RoleProgram
open WireTelescope WireTelescope.PassMatrix WireTelescope.CalendarTape
open Computability.VPVNP.BurstRAM PrivateRAM WideCPU
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 600000

variable {F Ex Sel Data : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype Data]
    {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h w ell unitCost bits datedROM datedWork terminalROM terminalWork first : ℕ) (G : Gate)
local notation "siteCount" => siteLast h (2^v.W) k+1
local notation "degree" => v.widePacketDegree
local notation "es" => events v.mesh
local notation "digits" => v.wideNeighborDigits w unitCost
local notation "cap" => v.wideNeighborCap w unitCost
local notation "g" => v.wideDated h w ell unitCost
local notation "Z" => v.wideSpillDates h w ell unitCost bits first
local notation "rank" => v.wideSpillRankEnd h w bits first
local notation "sw" => (Z).roleRoot rank 2
local notation "cw" => (Z).spillControlWork rank
local notation "old" => (Z).preClip datedWork rank
local notation "now" => fun j=>(g).roleStart datedWork j.succ
local notation "leftOnly" => fun j=>(Z).dateRole rank j 1
local notation "rightOnly" => fun j=>(Z).dateRole rank j 2
local notation "panel" => v.wideSpillTurnPage h w bits datedROM terminalROM terminalWork first
    ((Z).endAt rank) old now leftOnly rightOnly
local notation "bs" => siteNumber h (2^v.W) k
local notation "room" => HistoryRoles.ceiling v.sampler (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
    v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) w
local notation "ports" => (shelfSlot (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler)
local notation "seats" => WordSeats.room (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "V" => SitePins Ex Sel Data G
local notation "mid" => Fin (degree*cap)
local notation "Net" p:arg => BitNetwork F (Fintype.card p)
variable (time : Fin (((events v.mesh).length + 1) *
      Fintype.card ((r : Public v.sampler h v.W k v.wideJobs) × Fin
        (HistoryRoles.ceiling v.sampler (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
          v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) w r))) → Data)
    (s : Fin (siteLast h (2^v.W) k + 1)) (j : Fin (events v.mesh).length)
    (control : ∀ a : SiteControls.Field v.widePacketDegree,
      controlAddress (v.wideDated h w ell unitCost)
        ((v.wideSpillDates h w ell unitCost bits first).spillControlWork
          (v.wideSpillRankEnd h w bits first)) j s a < G.u)
    (signedControl : ∀ a : SiteControls.Field v.widePacketDegree,
      controlAddress (v.wideDated h w ell unitCost)
        ((v.wideSpillDates h w ell unitCost bits first).roleRoot
          (v.wideSpillRankEnd h w bits first) 2) j s a < G.u)
    (mode : ballotAddress (v.wideDated h w ell unitCost)
      ((v.wideSpillDates h w ell unitCost bits first).roleRoot
        (v.wideSpillRankEnd h w bits first) 2) j s 0 < G.u)
    (tagSmall : v.signedTagCeiling ≤ G.W + 1)
    (laneSmall : v.wideNeighborDigits w unitCost ≤ G.W + 1)
local notation "seatOf" => fun a : Fiber (attempts:=v.wideJobs) v.sampler ((bs).symm s)=>
  (finProdFinEquiv.symm (ports a.val)).2
local notation "feeRole" => fun (a : Fiber (attempts:=v.wideJobs) v.sampler ((bs).symm s)) b=>
    v.wide_shelf_role_fit h a.val b
local notation "raw" => LedgerStep.outerWord (Ex:=Ex) (Sel:=Sel) («degree»:=degree) («cap»:=cap) G es room ports time j s
local notation "sub" => LedgerStep.substepWord (Ex:=Ex) (Sel:=Sel) («degree»:=degree) («cap»:=cap) G es room ports time j s

def calendarMidAddress (q : Fin degree) : ℕ :=
  DatedRoleSheets.sheet ((Z).dateRole rank j 0) (g).roleWords (g).physical 0+(finProdFinEquiv (s,q)).val

private theorem midFits : cap≤2^(digits+1) := by
  change 2^digits≤2^(digits+1)
  rw [Nat.pow_succ]
  omega

/-- Physical occupancy, batch counts and accepted selector bits are all read
from the corrected native CPU by these networks. The event, pin order and
per-party turn capacity were fixed before that computation. -/
def calendarRow : Net V :=
  match (es).get j with
  | .feed _=>spillRow (F:=F) (slots:=seats) (e:=digits) G g cw j s control raw laneSmall
      v.sampler ((bs).symm s) (panel j).base feeRole seatOf
  | .attempt a=>
    let selection:=v.signed_tag_digits h a
    let signed:=v.signedRow (Ex:=Ex) (Sel:=Sel) (Data:=Data⊕mid) h w unitCost a G g sw j s (sub false) signedControl mode
      selection.1 (selection.2.1.trans tagSmall) laneSmall
    let spill:=spillRow (F:=F) (slots:=seats) (e:=digits) G g cw j s control (sub true) laneSmall
      v.sampler ((bs).symm s) (panel j).base feeRole seatOf
    LedgerStep.attemptRow (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=Data) G (v.midFits w unitCost)
      (v.calendarMidAddress h w ell unitCost bits first s j) signed spill

local notation "realRow" => v.calendarRow h w ell unitCost bits datedROM datedWork terminalROM terminalWork
  first G time s j control signedControl mode tagSmall laneSmall
local notation "afterClip" => spillRow (F:=F) (slots:=seats) (e:=digits) G g cw j s control (sub true) laneSmall
    v.sampler ((bs).symm s) (panel j).base feeRole seatOf
local notation "plainClip" => spillRow (F:=F) (slots:=seats) (e:=digits) G g cw j s control raw laneSmall
    v.sampler ((bs).symm s) (panel j).base feeRole seatOf
local notation "signedAt" a:arg => v.signedRow (Ex:=Ex) (Sel:=Sel) (Data:=Data⊕mid) h w unitCost a G g sw j s (sub false) signedControl mode
    (v.signed_tag_digits h a).1 ((v.signed_tag_digits h a).2.1.trans tagSmall) laneSmall
variable (out : Memory G.W) (ext : Ex→Bool) (sel : Sel→Bool) (data : Data→Bool)
local notation "seen" => Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))
local notation "combined" m:arg => Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim data m) (G.terminal out)))
local notation "quantity" => v.calendarMidAddress h w ell unitCost bits first s j

theorem calendarRow_feed {b} (date : (es).get j=.feed b) :
    TypedWiring.value (P:=V) realRow seen=TypedWiring.value (P:=V) plainClip seen :=by
  simp only [calendarRow,date]

theorem calendarRow_attempt {a} (date : (es).get j=.attempt a)
    {A B C : Widths siteCount} (vote : SiteMatrix (State A) (State B) F) (clip : SiteMatrix (State B) (State C) F)
    (x : State A s) (y : State C s)
    (layout : (Σt,SiteBit B t) ↪ Fin siteCount×mid) (site : ∀t b,(layout ⟨t,b⟩).1=t)
    (dense : ∀i:Fin G.u,(G.addr i).val=i.val) (inside : ∀q,quantity q<G.u)
    (strict : ∀q,(out (quantity q)).val<2^(digits+1))
    (published : ∀i:mid,(s,i)∈Set.range layout ↔
      ((finProdFinEquiv : Fin degree×Fin cap≃mid).symm i).2.val<
        (out (quantity (finProdFinEquiv.symm i).1)).val)
    (run : ∀z,TypedWiring.value (P:=SitePins Ex Sel (Data⊕mid) G) (signedAt a) (combined (LedgerStep.middle s (LedgerStep.siteChart layout site s) z))=vote s x z)
    (settle : ∀z,TypedWiring.value (P:=SitePins Ex Sel (Data⊕mid) G) afterClip (combined (LedgerStep.middle s (LedgerStep.siteChart layout site s) z))=clip s z y) :
    TypedWiring.value (P:=V) realRow seen=SiteMatrix.compose vote clip s x y :=by
  simp only [calendarRow,date]
  exact LedgerStep.attemptRow_value (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=Data) G out ext sel data
    (v.midFits w unitCost) quantity
    vote clip s x y layout site dense inside strict published (signedAt a) afterClip run settle

/-- Use the actual chronological factorization with its original dependent
source, intermediate and target widths. Both operands retain the signed
and settled matrix entries before their harmless width identifications. -/
theorem calendarRow_through {a} (date : (es).get j=.attempt a)
    {A U B B₀ C C₀ : Widths siteCount} (vote : SiteMatrix (State U) (State B₀) F) (clip : SiteMatrix (State B) (State C₀) F)
    (operator : SiteMatrix (State A) (State C) F) (factor : Through vote clip operator)
    (x : State A s) (y : State C s)
    (layout : (Σt,SiteBit B t) ↪ Fin siteCount×mid) (site : ∀t b,(layout ⟨t,b⟩).1=t)
    (dense : ∀i:Fin G.u,(G.addr i).val=i.val) (inside : ∀q,quantity q<G.u)
    (strict : ∀q,(out (quantity q)).val<2^(digits+1))
    (published : ∀i:mid,(s,i)∈Set.range layout ↔
      ((finProdFinEquiv : Fin degree×Fin cap≃mid).symm i).2.val<
        (out (quantity (finProdFinEquiv.symm i).1)).val)
    (run : ∀(entry : U=A) (join : B₀=B) z,
      TypedWiring.value (P:=SitePins Ex Sel (Data⊕mid) G) (signedAt a) (combined (LedgerStep.middle s (LedgerStep.siteChart layout site s) z))=
        vote s (cast (congrArg (fun ab=>State ab s) entry.symm) x)
          (cast (congrArg (fun ab=>State ab s) join.symm) z))
    (settle : ∀(exit : C₀=C) z,
      TypedWiring.value (P:=SitePins Ex Sel (Data⊕mid) G) afterClip (combined (LedgerStep.middle s (LedgerStep.siteChart layout site s) z))=
        clip s z (cast (congrArg (fun ab=>State ab s) exit.symm) y)) :
    TypedWiring.value (P:=V) realRow seen=operator s x y :=by
  obtain ⟨entry,join,exit,eqn⟩:=factor
  subst U
  subst B₀
  subst C₀
  rw [eqn]
  exact v.calendarRow_attempt h w ell unitCost bits datedROM datedWork terminalROM terminalWork first
    G time s j control signedControl mode tagSmall laneSmall out ext sel data date vote clip x y layout
    site dense inside strict published (run rfl rfl) (settle rfl)

private theorem volume_shift {P J K w : ℕ} (order : J≤K) :
    P*(w+1)*(Nat.log 2 (J*w+1)+2)^3≤P*(w+1)*(Nat.log 2 (K*w+1)+2)^3 := by
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_right (Nat.log_mono_right (b:=2) (Nat.succ_le_succ (Nat.mul_le_mul_right w order))) 2

private theorem guard_fee (w unitCost J : ℕ) (hw : 0<w)
    (fund : 2*(degree*v.wideHistoryUnit unitCost+1)≤J) :
    degree*(v.wideNeighborCap w unitCost)+degree*(v.wideNeighborCap w unitCost)*(200*((v.wideNeighborDigits w unitCost)+1)+65)≤(266*degree*J)*(w+1)*(Nat.log 2 (J*w+1)+2)^3 := by
  have limit:= (v.spill_width_cap unitCost w hw).trans (Nat.mul_le_mul_right w fund)
  have pow : 2^(v.wideNeighborDigits w unitCost)≤J*w+1 :=limit.trans (Nat.le_succ _)
  have bits : (v.wideNeighborDigits w unitCost)≤Nat.log 2 (J*w+1) :=by
    simpa only [Nat.log_pow (by decide : 1<2)] using Nat.log_mono_right (b:=2) pow
  let L:=Nat.log 2 (J*w+1)+2
  have pos : 0<L:=by dsimp [L];omega
  have step : (v.wideNeighborDigits w unitCost)+1≤L:=by dsimp [L];omega
  have cubed : L≤L^3:=by
    simpa only [pow_one] using Nat.pow_le_pow_right pos (by decide : 1≤3)
  calc
    _≤(266*degree)*(v.wideNeighborCap w unitCost)*((v.wideNeighborDigits w unitCost)+1) := by ring_nf;omega
    _≤(266*degree)*(J*(w+1))*(L^3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (limit.trans (Nat.mul_le_mul_left J (Nat.le_succ _)))) (step.trans cubed)
    _=_:=by simp only [Nat.mul_assoc,L]

/-- One coefficient and one logarithmic scale price every site and every
actual date of the fixed original protocol, independently of the CPU state. -/
theorem calendarRow_tariff (unitCost : ℕ) :
    ∃P J:ℕ,0<J ∧ ∀ {Ex Sel Data : Type} [Fintype Ex] [Fintype Sel] [Fintype Data]
      (h w ell bits datedROM datedWork terminalROM terminalWork first : ℕ) (_hw : 0<w) (G : Gate)
      time s j control signedControl mode tagSmall laneSmall,
      let row:=v.calendarRow (Ex:=Ex) (Sel:=Sel) (Data:=Data) h w ell unitCost bits datedROM datedWork
        terminalROM terminalWork first G time s j control signedControl mode tagSmall laneSmall
      row.cells+row.internal≤P*(w+1)*(Nat.log 2 (J*w+1)+2)^3 := by
  obtain ⟨A,J,aPos,attempt⟩:=v.signedRow_tariff unitCost
  obtain ⟨B,L,bPos,spill⟩:=v.spillRow_tariff unitCost
  let H:=max (max J L) (2*(degree*v.wideHistoryUnit unitCost+1))
  let guard:=266*degree*H
  have jh : J≤H:=(Nat.le_max_left ..).trans (Nat.le_max_left ..)
  have lh : L≤H:=(Nat.le_max_right ..).trans (Nat.le_max_left ..)
  refine ⟨guard+A+B,H,aPos.trans_le jh,?_⟩
  intro Ex Sel Data fEx fSel fData h w ell bits datedROM datedWork terminalROM terminalWork first
    _hw G time s j control signedControl mode tagSmall laneSmall row
  let vol:=(w+1)*(Nat.log 2 (H*w+1)+2)^3
  let dated := v.wideDated h w ell unitCost
  let spillDates := v.wideSpillDates h w ell unitCost bits first
  let rankEnd := v.wideSpillRankEnd h w bits first
  let spillBase := spillDates.spillControlWork rankEnd
  let signedBase := spillDates.roleRoot rankEnd 2
  let slotsAt := shelfSlot (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler
  let siteAt := (siteNumber h (2^v.W) k).symm s
  let slotAt : Fiber (attempts:=v.wideJobs) v.sampler siteAt → Fin v.widePacketDegree := fun a =>
    (finProdFinEquiv.symm (slotsAt a.val)).2
  let roomAt := HistoryRoles.ceiling v.sampler (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
    v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) w
  let turnPage := v.wideSpillTurnPage h w bits datedROM terminalROM terminalWork first
    (spillDates.endAt rankEnd) (spillDates.preClip datedWork rankEnd)
    (fun t => dated.roleStart datedWork t.succ)
    (fun t => spillDates.dateRole rankEnd t 1) (fun t => spillDates.dateRole rankEnd t 2)
  let outsideWord := LedgerStep.outerWord (Ex:=Ex) (Sel:=Sel) («degree»:=v.widePacketDegree) («cap»:=v.wideNeighborCap w unitCost)
    G (events v.mesh) roomAt slotsAt time j s
  let stepWord := LedgerStep.substepWord (Ex:=Ex) (Sel:=Sel) («degree»:=v.widePacketDegree) («cap»:=v.wideNeighborCap w unitCost)
    G (events v.mesh) roomAt slotsAt time j s
  cases date : (events v.mesh).get j with
  | feed b =>
    simp only [row,calendarRow,date]
    have paid := spill h w _hw G dated spillBase j s outsideWord control laneSmall siteAt (turnPage j).base slotAt
    have capped := paid.trans (volume_shift (P:=B) (w:=w) lh)
    calc
      _ ≤ B*vol := by simpa only [vol,Nat.mul_assoc] using capped
      _ ≤ (guard+A+B)*vol := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by simp only [vol,Nat.mul_assoc]
  | attempt a =>
    simp only [row,calendarRow,date]
    have tags := v.signed_tag_digits h a
    have signed := attempt h w a _hw G dated signedBase j s (stepWord false) signedControl mode
      tags.2.1 tags.1 (tags.2.1.trans tagSmall) laneSmall
    have clipped := spill h w _hw G dated spillBase j s (stepWord true) control laneSmall siteAt
      (turnPage j).base slotAt
    have signFee := signed.trans (volume_shift (P:=A) (w:=w) jh)
    have clipFee := clipped.trans (volume_shift (P:=B) (w:=w) lh)
    have mask := v.guard_fee w unitCost H _hw (Nat.le_max_right ..)
    apply (LedgerStep.attemptRow_fee (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=Data) G
      (v.midFits w unitCost) (v.calendarMidAddress h w ell unitCost bits first s j) _ _).trans
    exact (Nat.add_le_add (Nat.add_le_add mask signFee) clipFee).trans_eq (by
      simp only [guard,Nat.add_mul])

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
