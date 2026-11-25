import OAI.Hierarchy.DescentNamedSeedPins
import OAI.Hierarchy.DescentNamedEpochs
import OAI.Hierarchy.DescentNativePinSpine

namespace OAI
/-! # Exterior readback from the named seed actually consumed by the first match -/

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
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

open private rankAt from OAI.Hierarchy.DescentNamedSeedPins

private theorem activeOfSeedPosition {Pins : Type} {d : ℕ} {bits : Pins → ℕ}
    {W : MarkedWorld F d Pins bits} {price fee : ℝ} {z wire size tail : ℕ}
    (reached : Reached W G price fee S k 0 z 3 wire size)
    (base : S.baseGroups = 2 ^ tail) (radix : S.radix = 2 ^ k)
    (pin : Pins) (copy : Fin S.copies)
    (aligned : ((reached.placement.pos (W.graph.attach pin)).1, reached.placement.block (W.graph.attach pin)) =
      S.initialDigits radix copy) :
    active reached base radix pin = copyBits S base radix copy :=
  congrArg (fun row => (address _).symm ((S.resetInputDigits base radix 0).symm row)) aligned

private theorem readSeedRank {Pins : Type} {d : ℕ} {bits : Pins → ℕ}
    {W : MarkedWorld F d Pins bits} {price fee : ℝ} {z wire size : ℕ}
    (reached : Reached W G price fee S k 0 z 3 wire size) (pin : Pins) (value : ℕ)
    (h : rankAt reached pin = value) : (reached.vertex (host reached pin)).val = value := h

attribute [local irreducible] Origin.source

def Branch.pinSpine {tail : ℕ} (base : S.baseGroups=2^tail) :
    Spine (active b.origin.source base radix) (active b.target base radix)
      (host b.origin.source) (host b.target) b.path.frozen :=
  b.path.pinSpine base radix p hp b.origin.archive b.recorded
    b.origin.particles

attribute [local irreducible] Branch.pinSpine

theorem Branch.source_bits {tail : ℕ} (base : S.baseGroups=2^tail) (pin : SeedPin) :
    active b.origin.source base radix pin=copyBits S base radix pin.1 :=
  activeOfSeedPosition G S b.origin.source base radix pin pin.1 (b.origin.pinCoordinates pin)

/-- The original copy ordinal is exactly the binary input of the path layout. -/
theorem Branch.pinInput {tail : ℕ} (base : S.baseGroups=2^tail) (pin : _) :
    (address _ (active b.origin.source base radix pin)).val=pin.1.val := by
  rw [Branch.source_bits X G S b base pin]
  simp only [copyBits, Equiv.trans_apply, Equiv.apply_symm_apply, AtomSchedule.resetInputDigits,
    AtomSchedule.initialDigits, Equiv.symm_trans_apply, Equiv.symm_symm]
  rfl

/-- A given exterior slab uses the same seed host in every copy. -/
theorem Branch.pinHost {a b' : SeedPin} (same : a.2=b'.2) :
    host b.origin.source a=host b.origin.source b' := b.origin.pinHosts same

theorem Branch.seedRank (pin : SeedPin) :
    (b.origin.source.vertex (host b.origin.source pin)).val=
      (Fintype.equivFin (Site X.network.copyGraph) (.inr pin.2)).val :=
  readSeedRank G S b.origin.source pin _ (b.origin.pinRanks pin)

include hp in
/-- Equal final hosts carry copies of a single original exterior slab. -/
theorem Branch.originalSlab_eq {a a' : SeedPin} (eqn : host b.target a=host b.target a') :
    a.2=a'.2 := by
  have origin := b.path.previous_host_of_equal p hp b.origin.archive b.recorded
    b.origin.particles eqn
  have ranks := congrArg (fun v=>(b.origin.source.vertex v).val) origin
  change (b.origin.source.vertex (host b.origin.source a)).val=(b.origin.source.vertex (host b.origin.source a')).val at ranks
  rw [Branch.seedRank X G S b a, Branch.seedRank X G S b a'] at ranks
  exact Sum.inr_injective ((Fintype.equivFin (Site X.network.copyGraph)).injective (Fin.ext ranks))

private def pinFromCoordinates {copies slabs a live frozen : ℕ} (copy : Fin copies ≃ Bits a)
    (cut : Bits a ≃ₗ[ZMod 2] Bits live × Bits frozen) (row : Bits live × Bits frozen)
    (slab : Fin slabs) : Σ _ : Fin copies, Fin slabs := ⟨copy.symm (cut.symm row), slab⟩

private theorem coordinatesOfPin {copies slabs a live frozen : ℕ} (copy : Fin copies ≃ Bits a)
    (cut : Bits a ≃ₗ[ZMod 2] Bits live × Bits frozen)
    (seed : (Σ _ : Fin copies, Fin slabs) → Bits a) (align : ∀ pin, seed pin = copy pin.1)
    (row : Bits live × Bits frozen) (slab : Fin slabs) :
    cut (seed (pinFromCoordinates copy cut row slab)) = row := by
  rw [align]
  simp only [pinFromCoordinates, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Read the original physical pin using the final active coordinates and the collected
coordinates from this very branch. -/
def Branch.originalPin {tail : ℕ} (base : S.baseGroups=2^tail)
    (live : Bits (S.groupWidth k tail S.length+k)) (frozen : Bits b.path.frozen)
    (slab : Fin (Fintype.card (Port P X.width))) : SeedPin :=
  pinFromCoordinates (copyBits S base radix) (Branch.pinSpine X G S b hp base).cut (live, frozen) slab

attribute [local irreducible] pinFromCoordinates

theorem Branch.pinCoordinates {tail : ℕ} (base : S.baseGroups=2^tail)
    (live : Bits (S.groupWidth k tail S.length+k)) (frozen : Bits b.path.frozen) (slab : _) :
    let pin:=Branch.originalPin X G S b hp base live frozen slab
    (Branch.pinSpine X G S b hp base).cut (active b.origin.source base radix pin)=(live,frozen) :=
  coordinatesOfPin (copyBits S base radix) (Branch.pinSpine X G S b hp base).cut
    (active b.origin.source base radix) (Branch.source_bits X G S b base) (live, frozen) slab

attribute [local irreducible] Branch.originalPin

theorem Branch.terminal_active {tail : ℕ} (base : S.baseGroups=2^tail)
    (live : Bits (S.groupWidth k tail S.length+k)) (frozen : Bits b.path.frozen) (slab : _) :
    active b.target base radix (Branch.originalPin X G S b hp base live frozen slab)=live := by
  rw [←(Branch.pinSpine X G S b hp base).active_eq]
  exact congrArg Prod.fst (Branch.pinCoordinates X G S b hp base live frozen slab)

/-- At fixed slab and frozen coordinates, all final live groups and rows have one true
host. The initial copy is read by undoing each of the physically chosen remixes. -/
theorem Branch.terminal_host {tail : ℕ} (base : S.baseGroups=2^tail)
    (x y : Bits (S.groupWidth k tail S.length+k)) (frozen : Bits b.path.frozen) (slab : _) :
    host b.target (Branch.originalPin X G S b hp base x frozen slab)=
      host b.target (Branch.originalPin X G S b hp base y frozen slab) := by
  apply (Branch.pinSpine X G S b hp base).host_eq
  · exact b.origin.pinHosts (by simp only [Branch.originalPin, pinFromCoordinates])
  · exact (congrArg Prod.snd (Branch.pinCoordinates X G S b hp base x frozen slab)).trans
      (congrArg Prod.snd (Branch.pinCoordinates X G S b hp base y frozen slab)).symm

end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

-- Preserve the local transparency of these projections while Lean indexes theorem signatures.
open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Branch.pinSpine Branch.originalPin
