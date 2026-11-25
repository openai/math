import OAI.Hierarchy.DescentResetSelectedRootRooms
import OAI.Hierarchy.DescentResetAtlasTraffic
import OAI.Hierarchy.DescentResetRootControlScale
import OAI.Hierarchy.DescentNamedResetAtlas

namespace OAI
/-! # The signed pages and normalized root tables fit at the actual selected pitch -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentPackedWalsh DescentDatedAddressBook DescentSIMDLookup ProtocolRAM
open DescentFallbackPeriod DescentGLPacked.BankImage.SignedFields
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d k i D n C f g rate tail h₀ z wire hist : ℕ}
    {bs : P→ℕ} {W : MarkedWorld F d P bs} {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ}
    (r : Reached W G q ε S k i z D wire hist) (rates : ResetRates G S k D n h₀ C f g rate tail)
    (p h drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ)
    (old : StageVenueTail.Date) (addr : ℕ→ℕ→Bank) (roster : Bank)
local notation "c₀" => S.groupWidth k tail i
local notation "mass₀" => S.localWalshBits p (c₀+k) f (quota S.rounds)
local notation "cut₀" => resetCut S k tail p f h i
local notation "next₀" => S.groupWidth k tail (i+1)
local notation "rawCap" => (((capCalendar G.b S.rounds g S.height).take i).prod*256)
local notation "a₀" floor => PhysicalReset.selected G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old addr roster floor
local notation "v₀" floor => (a₀ floor).successor
local notation "mid₀" floor => (v₀ floor).middle
local notation "physicalCut" => PhysicalReset.receiverCut G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old
local notation "physicalBounds" => PhysicalReset.selected_cut G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old

theorem selected_atlas_shape (floor : ℕ) (live : i<S.length) (degreeAt : old.degree=D)
    (capacity : r.placement.cap=rawCap) (localRoom : 8*mass₀≤h)
    (rootRoom : 8*(v₀ floor).groupWidth≤h)
    (dimension : (c₀+k)*(c₀+k)≤h/2)
    (ranges : Nat.clog 2 (c₀+k+2)+(c₀+k+S.censusBits p)≤h/2) :
    PhysicalReset.Atlas.Shape (a₀ floor) (mid₀ floor).rootField
      ((mid₀ floor).rootControlBits rawCap) h := by
  let m:=mid₀ floor
  let v:=v₀ floor
  let e:=physicalCut
  have cut:=physicalBounds
  have eqn : v.exponent cut₀ cut₀ next₀ h = e :=
    selected_root_exponent (i := i) rates p h drift degree nextM packet oldLanes primitiveLanes
      printedBits old addr roster floor
  have next:=ResetOutput.next_difference S k tail i live
  have within : e≤c₀ := (show e≤next₀ from cut.2.2).trans (by omega)
  have basis : m.high+m.low=c₀+k := by change c₀-e+(e+k)=_;omega
  have cap : (a₀ floor).c/2=rawCap := by change (2*rawCap)/2=rawCap;omega
  have donor : v.front.donor.cap=rawCap :=rfl
  have oldDegree : (a₀ floor).ports=m.rootDegree :=rfl
  have signed : DescentSignedCableCodec.width (a₀ floor).ports ((a₀ floor).c/2)=m.signedBits := by
    rw [cap];rfl
  have pos : 0< mass₀ := by unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega
  have lp : 2^cut₀≤h := by
    have H:=DescentResetSignedTokens.quarter_key (a:=1) (m:=c₀+k) pos localRoom
      (by omega) (Nat.sub_le (laneBits (c₀+k) h mass₀) k)
    have : 2^cut₀≤h/4 := by simpa only [Nat.one_mul,resetCut] using H
    omega
  have key (u : ℕ) (member : u∈v.rootUnits) : u*m.signedLanes≤h/2 := by
    have paid := v.operand_room cut₀ cut₀ next₀ h rootRoom (Or.inl member)
    change u * 2^e ≤ h/2
    rw [← eqn]
    exact paid
  have both : ((m.signedBits+m.signedBits)*2^m.rootDepth)*m.signedLanes≤h/2 :=
    key _ (by simp [v,m,ResetOutput.rootUnits])
  have combined : (m.signedBits+m.signedBits)*2^m.low≤h/2 := by
    change (m.signedBits+m.signedBits)*2^(e+k)≤_
    simpa only [pow_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using
      (show ((m.signedBits+m.signedBits)*2^k)*2^e≤h/2 from both)
  have separate : joinWidth m.signedBits m.oldBlocks*m.signedLanes≤h/2 := by
    have one : m.signedBits≤ m.signedBits*2^m.rootDepth := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    apply le_trans (Nat.mul_le_mul_right m.signedLanes (show joinWidth m.signedBits m.oldBlocks≤
      (m.signedBits+m.signedBits)*2^m.rootDepth by
        change m.signedBits*2^m.rootDepth+m.signedBits≤_
        rw [Nat.add_mul];omega)) both
  have oldRoom:=selected_root_retile r rates p h drift degree nextM packet oldLanes primitiveLanes
    printedBits old addr roster floor degreeAt live.le capacity localRoom
  have lookup:=selected_root_lookup rates p h drift degree nextM packet oldLanes primitiveLanes
    printedBits old addr roster floor rootRoom
  have headers:=selected_header_exponents rates p h drift degree nextM packet oldLanes primitiveLanes
    printedBits old addr roster floor live dimension ranges
  have bound (u : ℕ) (hit : u∈[PackedFlow.Padded.sharedWidth m.stencil,(m.signedBits+m.signedBits)*2^m.rootDepth,
      m.projectBits,m.stencil.n,m.rootField*(Projected.Receiver.arityLimit m.rootDegree
        (2^m.rootDepth) rawCap m.rotorBits m.rootDepth+1),m.rootField*(Projected.Receiver.arityLimit
          m.rootDegree (2^m.rootDepth) rawCap m.rotorBits m.rootDepth),m.signedBits*2^m.rootDepth,
        Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth) rawCap m.rotorBits m.rootDepth]) :
      u≤ m.rootControlBits rawCap := m.rootControl_le rawCap u hit
  have dimFit : c₀+k≤ m.rootControlBits rawCap := by
    apply le_trans _ (bound m.stencil.n (by simp))
    change c₀+k≤k+mass₀+2
    unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits
    omega
  constructor
  · rfl
  · exact (ResetOutput.dyadic_chunks c₀ e within).symm
  · have upper:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le cut₀ e)
    exact (upper.trans lp).trans (Nat.le_succ h)
  · exact (Nat.pow_le_pow_right (by decide : 0<2) (show e≤cut₀ from cut.1)).trans lp
  · rfl
  · rw [signed]
    exact oldRoom.trans (show h/4≤h/2 by omega)
  · exact headers.1
  · rw [signed];exact combined
  · rw [signed];exact separate
  · change max (m.stencil.t*2^m.rootDepth)
      (DescentSignedCableCodec.width (a₀ floor).ports ((a₀ floor).c/2)*2^m.rootDepth)*m.signedLanes≤_
    rw [signed];exact key m.projectBits (by simp [v,m,ResetOutput.rootUnits])
  · rw [oldDegree,cap]
    change m.rootField*(Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth) rawCap m.rotorBits
      m.rootDepth+1)*m.signedLanes≤_
    change m.rootField*(Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth) v.front.donor.cap
      m.rotorBits m.rootDepth+1)*m.signedLanes≤_ at lookup
    rwa [donor] at lookup
  · exact key m.stencil.n (by simp [v,m,ResetOutput.rootUnits])
  · have remaining : m.stencil.levels+m.stencil.total≤h/2 := headers.2
    exact (Nat.le_add_left _ _).trans remaining
  · rw [oldDegree,cap]
    exact bound (Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth) rawCap m.rotorBits m.rootDepth) (by simp)
  · rw [basis];exact dimFit
  · exact dimFit

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
