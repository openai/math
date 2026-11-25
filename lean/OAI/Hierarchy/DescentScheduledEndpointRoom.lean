import OAI.Hierarchy.DescentScheduledResetChart
import OAI.Hierarchy.DescentResetStencilCalendar

namespace OAI
/-! The selected receiver's first per-group width pays the native reset stencil. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler DescentSixParty DescentPacking.PackedMatch.Local.Stage ProtocolRAM
open DescentPackedWalsh DescentGLPacked DescentSixParty.PackedFlow.Padded
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h : ℕ)
    (priorCut nextLanes C packet operandLanes primitiveLanes printed : ℕ) (venue : StageVenueTail.Date)
local notation "priorᵣ" => ResetOutput.Prior.atDate G S age p drift operandLanes primitiveLanes printed venue
local notation "fieldsᵣ" => ResetOutput.fromBoard G S board k tail age p f g drift degree h
  0 priorCut 1 nextLanes C packet priorᵣ 0
local notation "bookᵣ" => S.endpointBook k tail age p f venue.degree h n
local notation "cutᵣ" => receiverCut G S board k tail age p f g drift degree h priorCut nextLanes C packet
  operandLanes primitiveLanes printed venue

theorem receiver_endpoint :
    cutᵣ ≤ S.endpointExponent k tail age p f venue.degree h n ∧
    sharedWidth bookᵣ ≤ (fieldsᵣ).groupWidth :=by
  have inventory : sharedWidth bookᵣ ∈ (fieldsᵣ).rootUnits :=by
    change sharedWidth bookᵣ ∈ sharedWidth (fieldsᵣ).middle.stencil :: _
    exact List.mem_cons_self
  have share:=(fieldsᵣ).groupWidth_fit (Or.inl inventory)
  refine ⟨le_min ?_ ?_,share⟩
  · have bound:=(selected_cut G S board k tail age p f g drift degree h priorCut nextLanes C packet
      operandLanes primitiveLanes printed venue).2.2
    apply bound.trans
    change tail+k*(S.length-(age+1)) ≤ tail+k*(S.length-age)
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  · change cutᵣ ≤ (h/(4*sharedWidth bookᵣ)).log2
    rw [Nat.log2_eq_log_two]
    apply (Nat.min_le_right _ _).trans
    apply Nat.log_mono_right
    have hb : 0 < (bookᵣ).b:=by
      change 0 < DescentWalshPrecision.bits _ _ _ _
      unfold DescentWalshPrecision.bits;omega
    have pos:=positive_width bookᵣ hb
    exact Nat.div_le_div_left (by omega : 4*sharedWidth bookᵣ ≤ 8*(fieldsᵣ).groupWidth) (by omega)

variable (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ) (addr : ℕ→ℕ→Bank) (roster : Bank)
local notation "oldₛ" => NativePitch.resetCut S k tail p f h age
local notation "nextₛ" => NativePitch.incoming S k tail p f h ordinary (age+1)
local notation "tokenₛ" => DescentPrimitivePalette.printedBits G s Z op
local notation "schedₛ" => scheduled G S board k tail age p f g drift degree h ordinary op s Z
  operandLanes primitiveLanes venue addr roster

theorem scheduled_endpoint (floor : ℕ) (short : 8*((schedₛ) floor).successor.groupWidth ≤ h) :
    receiverCut G S board k tail age p f g drift degree h oldₛ nextₛ op.C op.w
      operandLanes primitiveLanes tokenₛ venue ≤ S.endpointExponent k tail age p f venue.degree h n ∧
    4*sharedWidth bookᵣ ≤ h :=by
  have both:=receiver_endpoint G S board k tail age p f g drift degree h oldₛ nextₛ op.C op.w
    operandLanes primitiveLanes tokenₛ venue
  have field : sharedWidth bookᵣ ≤ ((schedₛ) floor).successor.groupWidth := by
    apply ((schedₛ) floor).successor.groupWidth_fit (Or.inl ?_)
    change sharedWidth bookᵣ ∈ sharedWidth (((schedₛ) floor).successor.middle.stencil) :: _
    exact List.mem_cons_self
  exact ⟨both.1,by omega⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
