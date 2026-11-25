import OAI.Hierarchy.TaggedWideHistoryUnit
import OAI.Hierarchy.TaggedWidePlacement
import OAI.Hierarchy.TaggedWideCalendarFrame
import OAI.Hierarchy.TaggedWideDataCost

namespace OAI
/-! # Counting the four literal workspace blocks over the actual packed directory -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard HistoryRoles Tagged
open ReportSockets TaggedShorterBudget
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "d" => 2^v.W

def widePackedFactor :=
  let roles:=copies k v.wideJobs
  let buffer:=2^(9*d+18*(d-1)+2+2*roles)
  2*((2*rounds d+1)*4^(rounds d+1))*roles+2*buffer

theorem wide_group_space (h : ℕ) :
    ((WideMemory.dir h v.W k v.wideJobs).groups+1)*(WideMemory.H h v.W k v.wideJobs)≤v.widePackedFactor*2^h := by
  let cap:=WideMemory.H h v.W k v.wideJobs
  let groups:=(WideMemory.dir h v.W k v.wideJobs).groups
  let roles:=copies k v.wideJobs
  let coefficient:=(2*rounds d+1)*4^(rounds d+1)
  let buffer:=2^(9*d+18*(d-1)+2+2*roles)
  have budget : groups*cap≤2*((coefficient*2^h)*roles)+cap:=WideMemory.dir_space h v.W k v.wideJobs
  have extra : cap≤buffer*2^h:=CoreCatalogue.packed_height v.W (2*roles) h
  change (groups+1)*cap≤(2*coefficient*roles+2*buffer)*2^h
  nlinarith only [budget,extra]

def wideSpaceFactor (types lanes dates K J : ℕ) :=
  types*(2*v.widePackedFactor*lanes)+2*v.rowFactor*K+
    dates*(RoleProgram.RoleRoom.publicFactor d k v.sampler.degree v.wideJobs)*J+v.widePackedFactor*J

theorem wide_workspace {T : Type} [Fintype T] (key : T ↪ ℕ×ℕ) (h w lanes dates view K J : ℕ)
    (cap : (v.widePlacement h w).catalogue.Private (v.wideOrder h w)→ℕ)
    (floor : Public v.sampler h v.W k v.wideJobs→ℕ)
    (priv : ∀e,cap e≤K*w) (timeline : ∀i,floor i≤J*w) (output : view≤J*w) :
    Fintype.card (PhysicalTerm.CalendarTerms.Shared key cap floor (WideMemory.dir h v.W k v.wideJobs).groups
      (WideMemory.H h v.W k v.wideJobs) lanes dates view w)≤
      v.wideSpaceFactor (Fintype.card T) lanes dates K J*(2^h*w) := by
  let D:=(WideMemory.dir h v.W k v.wideJobs).groups
  let P:=v.widePlacement h w
  let b:=P.catalogue
  let order:=v.wideOrder h w
  let H:=WideMemory.H h v.W k v.wideJobs
  have pool : (Fintype.card (Fin D)+1)*H≤v.widePackedFactor*2^h:=by
    simpa only [Fintype.card_fin] using v.wide_group_space h
  have free : Fintype.card (b.Private order)≤v.rowFactor*2^h:=by
    exact (Fintype.card_subtype_le _).trans (by simpa only [Fintype.card_fin] using v.wideCatalogueRows h w)
  have roles:=RoleProgram.RoleRoom.raw_public_bound (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler
  apply WideStack.workspace_bill H lanes dates view _ cap floor (2^h) w v.widePackedFactor v.rowFactor _ K J
    pool free roles _ priv timeline output
  intro t
  exact Nat.ceil_le.mpr (mul_le_of_le_one_left (Nat.cast_nonneg w) (dyadic_le_one _))

def wideUnitCost (directCap treeCap coreCap : ℕ) :=
  max (2*directCap+treeCap+coreCap) (FeedLayout.lanes (publicStages v.W) k*coreCap)

def widePrivateUnit (unitCost : ℕ) :=
  HistoryRoles.clock v.mesh*unitCost+(1+publicStages v.W*(2*k))*(2*publicStages v.W+2)*(2*v.keepLimit+1)+
    CatalystArchive.fuel v.mesh

theorem original_workspace {T : Type} [Fintype T] (key : T ↪ ℕ×ℕ) (h w lanes dates unitCost : ℕ) :
    let roles:=HistoryRoles.ceiling v.sampler (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
      v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) w
    let priv:=fun _ : (v.widePlacement h w).catalogue.Private (v.wideOrder h w) => v.widePrivateUnit unitCost*w
    let view:=v.wideHistoryUnit unitCost*w
    Fintype.card (PhysicalTerm.CalendarTerms.Shared key priv roles (WideMemory.dir h v.W k v.wideJobs).groups
      (WideMemory.H h v.W k v.wideJobs) lanes dates view w)≤
      v.wideSpaceFactor (Fintype.card T) lanes dates (v.widePrivateUnit unitCost) (v.wideHistoryUnit unitCost)*(2^h*w) := by
  apply v.wide_workspace
  · exact fun _=>le_rfl
  · exact HistoryRoles.ceiling_le v.sampler v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) w
  · exact le_rfl

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
