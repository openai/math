import OAI.Hierarchy.DescentExteriorPrintedCalendar
import OAI.Hierarchy.DescentTerminalPacketHomeRAM
import OAI.Hierarchy.DescentNativeExteriorRows
import OAI.Hierarchy.DescentTerminalFrozenRows

namespace OAI
/-! # The common frozen-index column and honest native host of every terminal cohort -/
namespace Hierarchy.DescentSixParty
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

/-- All claims about the initial ancestry tape refer to immutable original
incidence indices of X. No branch field or selected matrix enters these words. -/
def seedAncestry (a : Fin size₀) : ℕ :=
  (Fintype.equivFin (Site X.network.copyGraph) (.inr (finProdFinEquiv.symm a).1)).val

/-- The immutable index of a printed ancestry class is the exact frozen half
of the composed layout on its original representative. -/
theorem representative_digit (a : Fin size₀) :
    (address frozen_ ((b.pinSpine X G S hp base).cut (active b.source base radix (rep a))).2).val=
      (finProdFinEquiv.symm a : Fin E × Fin (2^frozen_)).2.val := by
  let u:=representative tracking originLayout (finProdFinEquiv.symm a)
  have opening : castBits width.symm ((address shape).symm u.1)=active b.source base radix (origPin u) := by
    apply (address initialBits).injective
    apply Fin.ext
    rw [address_cast,Equiv.apply_symm_apply]
    exact (b.pinInput X G S base (origPin u)).symm
  change (address _ ((b.pinSpine X G S hp base).cut (active b.source base radix (origPin u))).2).val=_
  rw [←opening]
  change (address _ ((tracking).cut ((address shape).symm u.1)).2).val=_
  rw [show ((tracking).cut ((address shape).symm u.1)).2=
      (address frozen_).symm ((finProdFinEquiv.symm a).2) from
    representative_frozen tracking originLayout (fun _=>rfl) _,Equiv.apply_symm_apply]

/-- Word-size residues of the immutable final address give all authentic per-step
frozen digits; only the geometry tables for the earlier, actually executed hops vary. -/
theorem printed_fields {bw:ℕ} (hops : ℕ→Hop) (m:Memory bw)
    (emitted : b.path.shapeFields (count:=size₀) hops m)
    (literals : ∀t<S.length,∀a:Fin size₀,(hops t).frozenDigit.read (stage hops size₀ m t) (a.val:Word bw)=
      (((finProdFinEquiv.symm a : Fin E×Fin (2^frozen_)).2.val/2^(k*t)%2^k:ℕ):Word bw)) :
    b.path.exteriorFields base radix hops m rep := by
  let seed:=Chronology.seed_particles X (Chronology.epochsSource G r c) b.source (S.initialDigits radix) b.seed
  apply b.path.fields_of_digits base radix hops m rep p hp _ b.recorded seed
    (fun a=>(finProdFinEquiv.symm a : Fin E×Fin (2^frozen_)).2.val) literals emitted
  intro a
  rw [Nat.mod_eq_of_lt (finProdFinEquiv.symm a : Fin E×Fin (2^frozen_)).2.isLt]
  exact (representative_digit X G S b hp base width a).symm

/-- Every row of the *same* reached home bank is reconstructed by replaying
over frozen ancestry classes, followed by one literal gather per routed word. -/
theorem replayed_frozen {bw:ℕ} (hops : ℕ→Hop) (L : DescentTerminalPacketHomeRAM.Layout) (m : Memory bw)
    (ok : DescentTerminalPacketHomeRAM.Room L bw rows₀ size₀)
    (seedRead : ∀a:Fin size₀,(hops 0).source.read m (a.val:Word bw)=
      (seedAncestry X G S b a:Word bw))
    (arrived : b.path.exteriorFields base radix hops m rep)
    (chain : ∀t<S.length,(hops t).dest=(hops (t+1)).source)
    (capacity : ∀t<S.length,size₀≤(hops t).dest.size ∧ (hops t).dest.size<2^bw)
    (last : (hops S.length).source=L.frozen) :
    ∀a:Fin size₀,stage hops size₀ m S.length (L.frozen.base+a.val)=
      ((frozenHome X G S b hp base width a).val:Word bw) := by
  have seed : Holds m (hops 0).source (b.source.vertex.trans Fin.valEmbedding) (host b.source) rep := by
    intro a
    rw [seedRead]
    exact congrArg (fun n:ℕ=>(n:Word bw)) (b.seedRank X G S (rep a)).symm
  have real:=b.path.exterior_held base radix hops m rep arrived seed chain capacity
  intro a
  have read:=real a
  rw [last] at read
  have small:=a.isLt.trans_le ok.frozenRows
  simpa only [frozenHome,Fin.val_castLE,Function.Embedding.trans_apply,Fin.valEmbedding_apply,
    Bank.read,Fin.val_cast_of_lt (small.trans ok.frozen.2.1),Nat.mod_eq_of_lt small] using read

theorem replayed_homes {bw:ℕ} (hops : ℕ→Hop) (L : DescentTerminalPacketHomeRAM.Layout) (m : Memory bw)
    (enough : j≤retained) (ok : DescentTerminalPacketHomeRAM.Room L bw rows₀ size₀)
    (fit : ∀t<S.length,DescentExteriorReplay.Room bw size₀ (hops t))
    (seedRead : ∀a:Fin size₀,(hops 0).source.read m (a.val:Word bw)=
      (seedAncestry X G S b a:Word bw))
    (arrived : b.path.exteriorFields base radix hops m rep)
    (chain : ∀t<S.length,(hops t).dest=(hops (t+1)).source)
    (capacity : ∀t<S.length,size₀≤(hops t).dest.size ∧ (hops t).dest.size<2^bw)
    (last : (hops S.length).source=L.frozen)
    (literal : ∀i:Fin rows₀,stage hops size₀ m S.length (L.index.base+i.val) =
      (DescentTerminalPacketHomeRAM.calendar E j rest retained i:Word bw)) :
    let sortedInput:=stage hops size₀ m S.length
    let published:=DescentTerminalPacketHomeRAM.after L rows₀ sortedInput
    let action:=(steps bw size₀ (schedule hops S.length)).seq (DescentTerminalPacketHomeRAM.program L bw rows₀)
    action.Exec m published (clocks size₀ (schedule hops S.length)+(4+28*rows₀)) ∧
      CheapCode action ∧
      ∀i:Fin rows₀,L.dest.read published (i.val:Word bw) =
        ((publicHost X G S b hp base width i).val:Word bw) := by
  have birth:=replayed_frozen X G S b hp base width hops L m ok seedRead arrived chain capacity last
  have prior:=stage_control hops S.length m fit
  have wrote:=DescentTerminalPacketHomeRAM.run L ok (stage hops size₀ m S.length)
  exact ⟨Procedure.Exec.then (A := steps bw size₀ (schedule hops S.length))
      (B := DescentTerminalPacketHomeRAM.program L bw rows₀) prior.1 wrote.1,cheap_seq prior.2 wrote.2,
    calendar_home_source X G S b hp base width L enough ok _ literal birth⟩

end NativeBranch
end
end Hierarchy.DescentSixParty

end OAI
