import OAI.Hierarchy.DescentResetIngressSelectedPrice
import OAI.Hierarchy.DescentResetRootPitchRows
import OAI.Hierarchy.DescentResetRootHeaderScale

namespace OAI
/-! # Row, retile and lookup prices at the original selected root -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentPackedWalsh DescentDatedAddressBook DescentSIMDLookup ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d k i D n C f g rate tail h₀ z wire hist : ℕ}
    {bs : P→ℕ} {W : MarkedWorld F d P bs} {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ}
    (r : Reached W G q ε S k i z D wire hist) (rates : ResetRates G S k D n h₀ C f g rate tail)
    (p h drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ)
    (old : StageVenueTail.Date) (addr : ℕ→ℕ→Bank) (roster : Bank)
local notation "c₀" => S.groupWidth k tail i
local notation "bits₀" => S.localWalshBits p (c₀+k) f (quota S.rounds)
local notation "cut₀" => resetCut S k tail p f h i
local notation "next₀" => S.groupWidth k tail (i+1)
local notation "a₀" floor => PhysicalReset.selected G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old addr roster floor
local notation "v₀" floor => (a₀ floor).successor
local notation "middle" floor => (v₀ floor).middle

local notation "physicalCut" => PhysicalReset.receiverCut G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old
local notation "physicalBounds" => PhysicalReset.selected_cut G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old
local notation "inventory" floor => PhysicalReset.selected_inventory G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old addr roster floor

private theorem inventory_exponent {v seed : ResetOutput} (previous transform next h : ℕ)
    (roots : v.rootUnits = seed.rootUnits) (receivers : v.receiverUnits = seed.receiverUnits) :
    v.exponent previous transform next h = seed.exponent previous transform next h := by
  unfold ResetOutput.exponent ResetOutput.groupWidth
  rw [roots, receivers]

/-- The physical date and its seed have the same key inventory, so clipping gives the same exponent. -/
theorem selected_root_exponent (floor : ℕ) :
    (v₀ floor).exponent cut₀ cut₀ next₀ h = physicalCut := by
  have inv := inventory floor
  exact inventory_exponent cut₀ cut₀ next₀ h inv.1 inv.2.1

theorem selected_root_rows (floor : ℕ) (live : i<S.length) (localRoom : 8*bits₀≤h)
    (rootRoom : 8*(v₀ floor).groupWidth≤h) :
    chunks (middle floor).rootGroups (middle floor).rootLanes*h≤
      (2+2^k)*h+2^c₀*(32*2^k*bits₀+16*(v₀ floor).groupWidth) := by
  have next : next₀=c₀-k := by
    have step:=ResetOutput.next_difference S k tail i live
    omega
  have pos : 0<bits₀ := by unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega
  have inv := inventory floor
  have eqn := selected_root_exponent (i := i) rates p h drift degree nextM packet oldLanes primitiveLanes
    printedBits old addr roster floor
  change chunks (2^c₀) (middle floor).rootLanes*h≤_
  rw [inv.2.2.2, ← eqn, next]
  exact (v₀ floor).boundary_rows c₀ k h bits₀ pos localRoom rootRoom

theorem selected_root_lookup (floor : ℕ) (rootRoom : 8*(v₀ floor).groupWidth≤h) :
    let R:=middle floor
    (R.rootField*(DescentFallbackPeriod.Projected.Receiver.arityLimit R.rootDegree (2^R.rootDepth)
      (v₀ floor).front.donor.cap R.rotorBits R.rootDepth+1))*R.rootLanes≤h/2 := by
  have inv := inventory floor
  have eqn := selected_root_exponent (i := i) rates p h drift degree nextM packet oldLanes primitiveLanes
    printedBits old addr roster floor
  dsimp only
  rw [inv.2.2.2, ← eqn]
  exact (v₀ floor).root_lookup_operand cut₀ cut₀ next₀ h rootRoom

theorem selected_root_retile (floor : ℕ) (degreeAt : old.degree=D) (live : i≤S.length)
    (capacity : r.placement.cap=((capCalendar G.b S.rounds g S.height).take i).prod*256)
    (localRoom : 8*bits₀≤h) :
    let m:=middle floor
    m.signedBits*(m.signedRatio*m.signedLanes)≤h/4 := by
  let e:=physicalCut
  have cut : e ≤ cut₀ := (physicalBounds).1
  have signed:=DescentResetSignedTokens.reached_quarter r rates p h cut₀ live localRoom (Nat.sub_le ..)
  rw [r.branch,capacity] at signed
  change DescentSignedCableCodec.width old.degree (((capCalendar G.b S.rounds g S.height).take i).prod*256)*
    (2^(cut₀-e)*2^e)≤h/4
  rw [degreeAt,←pow_add,Nat.sub_add_cancel cut]
  exact signed

theorem selected_header_exponents (floor : ℕ) (live : i<S.length)
    (dimension : (c₀+k)*(c₀+k)≤h/2)
    (ranges : Nat.clog 2 (c₀+k+2)+(c₀+k+S.censusBits p)≤h/2) :
    let R:=middle floor
    (R.high+R.low)*(R.high+R.low)≤h/2 ∧ R.stencil.levels+R.stencil.total≤h/2 := by
  let e:=physicalCut
  have first := physicalBounds
  have step:=ResetOutput.next_difference S k tail i live
  have nt : e≤c₀ := by
    have lim : e≤next₀ := first.2.2
    omega
  have count : c₀-e+(e+k)=c₀+k := by omega
  change (c₀-e+(e+k))*(c₀-e+(e+k))≤h/2 ∧ Nat.clog 2 (c₀+k+2)+(c₀+k+S.censusBits p)≤h/2
  exact ⟨by simpa only [count] using dimension,ranges⟩


end
end Hierarchy.DescentSixParty.NativePitch

end OAI
