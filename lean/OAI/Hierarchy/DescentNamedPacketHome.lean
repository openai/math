import OAI.Hierarchy.DescentTerminalPacketHomeRAM
import OAI.Hierarchy.DescentNamedExteriorRows
import OAI.Hierarchy.DescentTerminalFrozenRows

namespace OAI
open Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Branch.publicSpine

/-! # The common frozen-index column and honest native host of every terminal cohort -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
set_option quotPrecheck false
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S radix R r c) (hp : 0<p)

open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace Branch
open DescentTerminalExteriorPackets
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "retained" => S.groupWidth k tail S.length+k
local notation "shape" => j+(j+rest)
local notation "E" => Fintype.card (Port P X.width)
local notation "Public" => Σ _:Fin (2^shape),Fin E
variable (width : S.groupWidth k tail 0 + k = j + (j + rest))


open DescentTerminalPacketHomeRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM

local notation "tracking" => publicSpine X G S b hp base width
local notation "origPin" => NativeBranch.rawPin S (X:=X) (radix:=radix) base width
local notation "originLayout" => fun _ : Fin E=>LinearEquiv.refl (ZMod 2) (Bits shape)
local notation "oldOwner" => fun u : Public=>host b.origin.source (origPin u)
local notation "newOwner" => fun u : Public=>host b.target (origPin u)
local notation "frozen_" => b.path.frozen

/-- The row-to-antecedent index is given entirely by the copy calendar. -/
def frozenIndex (room : j ≤ retained) (i : Fin (E*2^(j+rest))) : Fin (E*2^frozen_) :=
  finProdFinEquiv (previous room ((Nat.add_comm frozen_ retained).trans (tracking).width) i)

theorem frozenIndex_val (room : j ≤ retained) (i : Fin (E*2^(j+rest))) :
    (frozenIndex X G S b hp base width room i).val=calendar E j rest retained i := by
  have cut:=(tracking).width
  have total : frozen_=shape-retained:=by omega
  change (finProdFinEquiv.symm i).2.val/2^(retained-j)+2^frozen_*(finProdFinEquiv.symm i).1.val=_
  rw [total]
  rfl

include hp base width in
theorem frozen_count : (E*2^frozen_)*2^retained=E*2^shape :=
  size_frozen (tracking).width

def frozenHome (a : Fin (E*2^frozen_)) : Fin (S.hostSize S.length) :=
  (b.target.vertex (newOwner (representative tracking originLayout (finProdFinEquiv.symm a)))).castLE b.target.valid.host

theorem publicHost_frozen (room : j ≤ retained) (i : Fin (E*2^(j+rest))) :
    publicHost X G S b hp base width i=
      frozenHome X G S b hp base width (frozenIndex X G S b hp base width room i) := by
  have group:=owner_previous tracking originLayout room (fun _=>rfl)
    (fun u v eqn=>Branch.pinHost X G S b (a:=origPin u) (b':=origPin v) eqn) i
  have paid:=congrArg (fun v=>(b.target.vertex v).castLE b.target.valid.host) group
  simpa only [publicHost,frozenHome,frozenIndex,Equiv.symm_apply_apply] using paid

theorem frozen_home_source {w : ℕ} (L : DescentTerminalPacketHomeRAM.Layout) (room : j ≤ retained)
    (R_ : DescentTerminalPacketHomeRAM.Room L w (E*2^(j+rest)) (E*2^frozen_)) (m : Memory w)
    (idx : ∀i : Fin (E*2^(j+rest)),m (L.index.base+i.val)=((frozenIndex X G S b hp base width room i).val:Word w))
    (replayed : ∀a : Fin (E*2^frozen_),m (L.frozen.base+a.val)=((frozenHome X G S b hp base width a).val:Word w))
    (i : Fin (E*2^(j+rest))) :
    L.dest.read (DescentTerminalPacketHomeRAM.after L (E*2^(j+rest)) m) (i.val:Word w)=
      ((publicHost X G S b hp base width i).val:Word w) := by
  rw [publicHost_frozen X G S b hp base width room]
  exact DescentTerminalPacketHomeRAM.source L R_ _ _ m idx replayed i

/-- The original literal column and the honest reached ancestry bank suffice
for the sort. The physical index column uses the fixed public calendar. -/
theorem calendar_home_source {w : ℕ} (L : DescentTerminalPacketHomeRAM.Layout) (room : j ≤ retained)
    (R_ : DescentTerminalPacketHomeRAM.Room L w (E*2^(j+rest)) (E*2^frozen_)) (m : Memory w)
    (idx : ∀i : Fin (E*2^(j+rest)),m (L.index.base+i.val)=(calendar E j rest retained i:Word w))
    (replayed : ∀a : Fin (E*2^frozen_),m (L.frozen.base+a.val)=((frozenHome X G S b hp base width a).val:Word w))
    (i : Fin (E*2^(j+rest))) :
    L.dest.read (DescentTerminalPacketHomeRAM.after L (E*2^(j+rest)) m) (i.val:Word w)=
      ((publicHost X G S b hp base width i).val:Word w) :=
  frozen_home_source X G S b hp base width L room R_ m
    (fun t=>by simpa only [frozenIndex_val X G S b hp base width room] using idx t) replayed i

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
