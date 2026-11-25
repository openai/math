import OAI.Hierarchy.DescentNativeHomeReplay
import OAI.Hierarchy.DescentTerminalCohortRanks

namespace OAI
/-! # The actual replayed frozen-home word supplies every attached port rank -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height (initialGroup X S.copies (S.firstWidth G.b p))}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p)

open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace NativeBranch
open DescentTerminalExteriorPackets DescentExteriorReplay ThreeFlat.RAM PhysicalProcedure
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "retained" => S.groupWidth k tail S.length+k
local notation "shape" => j+(j+rest)
local notation "E" => Fintype.card (Port P X.width)
local notation "Public" => Σ _:Fin (2^shape),Fin E
variable (width : S.groupWidth k tail 0 + k = j + (j + rest))


open DescentTerminalPacketHomeRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM

local notation "tracking" => publicSpine X G S b hp base width
local notation "origPin" => rawPin S (X:=X) (radix:=radix) base width
local notation "originLayout" => fun _ : Fin E=>LinearEquiv.refl (ZMod 2) (Bits shape)
local notation "oldOwner" => fun u : Public=>host b.source (origPin u)
local notation "newOwner" => fun u : Public=>host b.target (origPin u)
local notation "frozen_" => b.path.frozen


local notation "size₀" => E*2^frozen_
local notation "rows₀" => E*2^(j+rest)
local notation "rep" => fun a:Fin size₀=>origPin (representative tracking originLayout (finProdFinEquiv.symm a))


theorem frozenHome_direct (a:Fin size₀) : frozenHome X G S b hp base width a=cohortHome X G S b hp base a := by
  have eqn : cohort X G S b hp base (rep a)=a := by
    apply finProdFinEquiv.symm.injective
    rw [cohort,Equiv.symm_apply_apply]
    apply Prod.ext
    · rfl
    · exact Fin.ext (representative_digit X G S b hp base width a)
  have loc:=home_cohort X G S b hp base (active b.target base radix (rep a)) (cohort X G S b hp base (rep a))
  rw [at_cohort,eqn] at loc
  exact loc

theorem cohort_slot {bw : ℕ} (m : Memory bw) (L : ProtocolRAMEndpointSort.Layout)
    (ok : L.Fits bw size₀ (S.hostSize S.length)) (hH : S.hostSize S.length<2^bw)
    (frozen : ∀a:Fin size₀,m (L.src+a.val)=((frozenHome X G S b hp base width a).val:Computability.VPVNP.BurstRAM.Word bw))
    (v:((Epochs.finish G hu he r).state c).graph.Site)
    (z:DescentKernelHistory.Attached ((Epochs.finish G hu he r).state c).graph v) :
    let home:=cohortHome X G S b hp base
    let a:=cohort X G S b hp base z.val
    DescentTerminalPacketSlotRAM.after L size₀ (S.hostSize S.length) (ProtocolRAMEndpointSort.image L home m)
      (DescentTerminalPacketSlotRAM.out L size₀ (S.hostSize S.length)+(Computability.BorderVNP.FragmentBucket.dest home a).val)=
        ((densePin X G S b hp base v z):Computability.VPVNP.BurstRAM.Word bw) := by
  let home:=cohortHome X G S b hp base
  let a:=cohort X G S b hp base z.val
  have key (i:Fin size₀) : m (L.src+i.val)=((home i).val:Computability.VPVNP.BurstRAM.Word bw) := by simpa only [frozenHome_direct] using frozen i
  have h:=DescentTerminalPacketSlotRAM.scan_read L ok hH home m key (Computability.BorderVNP.FragmentBucket.dest home a)
  simp only [Equiv.symm_apply_apply] at h
  have host : home a=b.target.home v:=((attachedCohorts X G S b hp base v) z).2
  change _ = (Computability.BorderVNP.FragmentBucket.prior home a.val (b.target.home v) : Computability.VPVNP.BurstRAM.Word bw)
  simpa only [host] using h

end NativeBranch
end
end Hierarchy.DescentSixParty

end OAI
