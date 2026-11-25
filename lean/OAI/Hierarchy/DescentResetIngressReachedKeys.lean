import OAI.Hierarchy.DescentPackedCanvasCopy
import OAI.Hierarchy.DescentNextStagePitch
import OAI.Hierarchy.DescentFundedCalendar
import OAI.Hierarchy.DescentNamedResetOutput
import OAI.Hierarchy.DescentResetIngressWork

namespace OAI
/-! # The original funded and signed shelves pay for the full reached reset ingress -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentPackedWalsh DescentResetSignedTokens DescentDatedAddressBook
open ProtocolRAM DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
theorem walsh_rows {c k h b : ℕ} (positive : 0<b) (small : 8*b≤h) :
    chunks (2^c) (2^(laneBits (c+k) h b-k))*h≤h+2^c*(16*2^k*b) := by
  let l:=laneBits (c+k) h b
  let e:=l-k
  have low : l≤c+k := Nat.min_le_left ..
  have cut : e≤c := by dsimp [e];omega
  have exactRows : chunks (2^c) (2^e)=2^(c-e) := PackedFlow.Canvas.original_chunks
    (u:=c-e) (l:=e) (k:=0) (by simp [Nat.sub_add_cancel cut]) (by simp) (Nat.two_pow_pos _)
  have axes : c-e≤c+k-l := by dsimp [e];omega
  have bound := Nat.mul_le_mul_right h (Nat.pow_le_pow_right (by decide : 0<2) axes)
  have bill := per_layer (m:=c+k) 1 positive small
  change chunks (2^c) (2^e)*h≤_
  rw [exactRows]
  calc
    _ ≤ 2^(c+k-l)*h := bound
    _ ≤ h+16*2^(c+k)*b := by simpa [l] using bill
    _ = _ := by rw [pow_add];ring

variable {F P : Type} [Field F] {d k i D n C f g cut tail h₀ z wire hist : ℕ}
    {bs : P→ℕ} {W : MarkedWorld F d P bs} {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ}
    (r : Reached W G q ε S k i z D wire hist)
    (rates : ResetRates G S k D n h₀ C f g cut tail)
    (p payload drift degree e previous batch nextM packet oldLanes primitiveLanes printedBits : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (addr : ℕ→ℕ→Bank) (roster : Bank)
local notation "c" => S.groupWidth k tail i
local notation "μ" => (S.localWalshBits p (c+k) f (quota S.rounds))
local notation "calendar" => (capCalendar G.b S.rounds g S.height)
local notation "prior" => (DescentNamedFundedChart.previous S k i p D calendar
  (incoming S k tail p f payload ordinary i))
local notation "date" => PhysicalReset.named G S rates.board k tail i p f g drift degree payload e previous
  batch nextM C packet oldLanes primitiveLanes printedBits prior addr roster
local notation "L" floor => ((date floor).ingress)

/-- The two source fields have one quarter of the payload each at the
incoming normalized pitch. Their maximum at the collector obeys the same bound. -/
theorem ingress_widths (floor : ℕ) (alive : i<S.length) (boundary : i%(S.rounds+1)=S.rounds)
    (capacity : r.placement.cap=((calendar).take i).prod*256)
    (small : 8*μ≤payload) :
    (L floor).signed.bits*(L floor).sourceLanes≤payload/4 ∧
    (L floor).oldBits*(L floor).sourceLanes≤payload/4 ∧
    (L floor).collector.unitBits*(L floor).targetLanes≤payload/4 ∧
    (L floor).sourceLanes≤payload ∧ (L floor).targetLanes≤payload := by
  let l:=laneBits (c+k) payload μ
  let M:=2^(l-k)
  have equal : incoming S k tail p f payload ordinary i=M := by
    simp only [incoming,ite_eq_left alive,ite_eq_left boundary,resetCut,M,l]
  have wires := reached_quarter r rates p payload (l-k) alive.le small (Nat.sub_le ..)
  rw [r.branch,capacity] at wires
  have pos : 0<μ := by unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega
  have paid : S.censusBits p≤2*μ := by
    unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits
    omega
  have amounts := quarter_key (m:=c+k) pos small paid (Nat.sub_le l k)
  show DescentSignedCableCodec.width D (((calendar).take i).prod*256)*
        incoming S k tail p f payload ordinary i≤payload/4 ∧
      S.censusBits p*incoming S k tail p f payload ordinary i≤payload/4 ∧
      max (S.censusBits p) (DescentSignedCableCodec.width D (((calendar).take i).prod*256))*M≤payload/4 ∧
      incoming S k tail p f payload ordinary i≤payload ∧ M≤payload
  rw [equal,←Nat.mul_max_mul_right]
  have wpos : 0<DescentSignedCableCodec.width D (((calendar).take i).prod*256) := by
    unfold DescentSignedCableCodec.width;omega
  have mRoom := (Nat.le_mul_of_pos_left M wpos).trans wires
  exact ⟨wires,amounts,max_le amounts wires,mRoom.trans (Nat.div_le_self ..),
    mRoom.trans (Nat.div_le_self ..)⟩

/-- Original native statement at its real absolute floor, with both ROMs and
all host-dependent linear passes priced. -/
theorem ingress_invoice (floor : ℕ) (high : 64≤payload) (alive : i<S.length)
    (boundary : i%(S.rounds+1)=S.rounds)
    (capacity : r.placement.cap=((calendar).take i).prod*256) (small : 8*μ≤payload) :
    let s:=L floor
    let O:=s.hosts*chunks s.groups s.sourceLanes
    let N:=s.hosts*chunks s.groups s.targetLanes
    s.bill 7≤16384*((s.columns+1)*(1+O+N)+(s.columns+1)*2^(payload/2)) := by
  obtain ⟨signed,paid,fresh,old,next⟩ := ingress_widths r rates p payload drift degree e previous
    batch nextM packet oldLanes primitiveLanes printedBits ordinary addr roster floor alive boundary capacity small
  exact (L floor).work_bound payload high old next signed paid (by omega)

theorem named_ingress_price (floor w ratio : ℕ) (hosts : 0<S.hostSize i)
    (word : w≤ratio*payload) (alive : i<S.length) (boundary : i%(S.rounds+1)=S.rounds)
    (capacity : r.placement.cap=((calendar).take i).prod*256) (small : 8*μ≤payload) :
    let s:=L floor
    let unit:=16*2^k*μ
    s.bill 7*w≤ s.hosts*payload*(65536*(s.columns+1)*ratio)+
      s.hosts*s.groups*(65536*(s.columns+1)*ratio*unit)+
      (65536*(s.columns+1)*ratio*(payload+1)^3)*2^(payload/2) := by
  obtain ⟨_,_,fresh,_,next⟩ := ingress_widths r rates p payload drift degree e previous
    batch nextM packet oldLanes primitiveLanes printedBits ordinary addr roster floor alive boundary capacity small
  have matchPitch : (L floor).sourceLanes=(L floor).targetLanes := by
    change incoming S k tail p f payload ordinary i=2^(resetCut S k tail p f payload i)
    simp [incoming,alive,boundary]
  have pos : 0<μ := by unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega
  apply (L floor).matching_bill payload w ratio matchPitch next (by omega) word hosts
  exact walsh_rows pos small


end
end Hierarchy.DescentSixParty.NativePitch

end OAI
