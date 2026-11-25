import OAI.Hierarchy.DescentRegisteredVenuePitchBounds
import OAI.Hierarchy.DescentNamedSignedCalibrated
import OAI.Hierarchy.DescentNamedResetVenueRate
import OAI.Hierarchy.DescentSignedVenueDensity

namespace OAI
/-! # Address space of every issued ordinary successor venue -/
namespace Hierarchy.DescentSixParty.StageVenueTail.Date
open DescentDatedAddressBook DescentCompiler DescentCompiler.TerminalScale DescentSIMDLookup Filter
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {ι : ℕ→Type*}
variable (t f g reset τ B : ℕ) (sites age grain sourcePitch : ∀h,ι h→ℕ)
variable (programs : ∀h,ι h→ℕ→Dated.Ordinary)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h) f g reset (sites h i) (tail τ (J_ h))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "q_" h:arg i:arg => SignedStage.atDate G (S_ h i) g (k_ h) (age h i) (NativePitch.incomingHosts (S_ h i) (age h i+1))
local notation "d_" h:arg i:arg => atOrdinary G (S_ h i) g (k_ h) (tail τ (J_ h)) (grain h i) f h (programs h i) (age h i) (sourcePitch h i)

/-- Both source bounds are literal consequences of `fundedClipAt_paid_pitch` on the actual named
clip.  The destination includes the last frozen roster of the original schedule. -/
theorem ordinary_venue_room (positive : 0<B) (tailRoom : τ≤B)
    (seed : Bounded sites) (earlier : ∀h i,age h i<(S_ h i).length)
    (issued : ∀h i j,(programs h i j).payload=h)
    (clip : ∀h i,sourcePitch h i≤h ∧ (S_ h i).censusBits (grain h i)*sourcePitch h i≤h/4)
    (bought : ∀ᶠ h : ℕ in atTop,∀i,2*(q_ h i).unit ≤ h) : ScalarRoom (fun h i=>d_ h i) := by
  let p:=fun h i=>d_ h i
  let q:=fun h i=>q_ h i
  have axes:=schedule_space G t f g reset τ B sites age seed (fun h i=>(earlier h i).le)
  have hosts : Bounded (fun h i=>(p h i).hosts):=axes.newHost.padded.of_le fun h i=>
    (NativePitch.hosts_bounds (S_ h i) _ (earlier h i)).2
  have masks:=ResetOutput.normalized_mask_rate G t f g reset τ B sites age grain (fun h i=>(p h i).lanes)
    programs issued positive tailRoom
  have normalized : ∀ᶠ h : ℕ in atTop,∀i,(p h i).lanes≤1*h:=masks.mono fun h use i=>use i rfl
  have linear {x : ∀h,ι h→ℕ} (fit : ∀ᶠ h : ℕ in atTop,∀i,x h i≤1*h) : Bounded x :=
    ⟨1,fit.mono fun _ fits i=>(fits i).trans Nat.lt_two_pow_self.le⟩
  have digit {h i} (small : 2*(q h i).unit≤h) : (q h i).fieldBits ≤ 1*h := by
    let Q:=q h i
    have live := (occupancy h Q.unit Q.positive small).1
    have field : Q.fieldBits ≤ Q.fieldBits*2^Q.k+Q.fieldBits := Nat.le_add_left ..
    have unit : Q.fieldBits ≤ Q.unit := field.trans (Nat.le_max_right ..)
    have pay : Q.unit*DescentSIMDLookup.lanes h Q.unit ≤ h/2 := by rw [Nat.mul_comm];exact lanes_fit ..
    calc Q.fieldBits ≤ Q.unit*DescentSIMDLookup.lanes h Q.unit := unit.trans (Nat.le_mul_of_pos_right _ live)
         _ ≤ 1*h := pay.trans (by simpa only [Nat.one_mul] using Nat.div_le_self h 2)
  have alphabet : Bounded (fun h i=>2^(q h i).fieldBits):=Bounded.pow_of_linear (K:=1)
    (bought.mono fun h ok i=>digit (ok i))
  have tickets : Bounded (fun h i=>(p h i).degree) := alphabet.of_le fun h i=>
    (Nat.le_succ _).trans ((Nat.le_max_left ..).trans_lt (q h i).field_room.2.1).le
  have sizes (h i) (paid : 2*(q h i).unit≤h) :=
    atOrdinary_signed_caps G (S_ h i) g (k_ h) (tail τ (J_ h)) (grain h i) f h (programs h i)
      (age h i) (sourcePitch h i) paid
  have half (h : ℕ) : h/2≤1*h:=by simpa only [Nat.one_mul] using Nat.div_le_self h 2
  have alive : ∀ᶠ h : ℕ in atTop,∀i,sourcePitch h i≤1*h :=
    Eventually.of_forall fun h i=>by simpa only [Nat.one_mul] using (clip h i).1
  have width : ∀ᶠ h : ℕ in atTop,∀i,(p h i).paidBits*(p h i).paidLanes≤1*h :=
    Eventually.of_forall fun h i=>(clip h i).2.trans (by simpa only [Nat.one_mul] using Nat.div_le_self h 4)
  refine ⟨alphabet.of_le (fun h i=>(q h i).alphabet_dims.1),hosts,axes.newGroup,tickets,
    alphabet.of_le (fun h i=>(q h i).alphabet_dims.2.2.2.1),linear normalized,
    linear (bought.mono fun h ok i=>(sizes h i (ok i)).2.2.1.trans (half h)),linear alive,linear alive,
    ⟨1,bought.mono fun h ok i=>(sizes h i (ok i)).2.2.2.trans (half h)⟩,⟨1,width⟩,⟨1,alive⟩,⟨1,normalized⟩⟩

end
end Hierarchy.DescentSixParty.StageVenueTail.Date

end OAI
