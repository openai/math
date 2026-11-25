import OAI.Hierarchy.DescentPathPinSpine
import OAI.Hierarchy.DescentNormalizedEpochs

namespace OAI
/-! # Exterior coordinates of each original pin in one true final execution -/

namespace Hierarchy.DescentSixParty
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
      (t := S.rounds) S.height (initialGroup X S.copies (S.firstWidth G.b p))}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p)

open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))

def NativeBranch.pinSpine {tail : ℕ} (base : S.baseGroups=2^tail) :
    Spine (active b.source base radix) (active b.target base radix)
      (host b.source) (host b.target) b.path.frozen :=
  b.path.pinSpine base radix p hp _ b.recorded
    (Chronology.seed_particles X (Chronology.epochsSource G r c) b.source (S.initialDigits radix) b.seed)

/-- The original copy ordinal is exactly the binary input of the path layout. -/
theorem NativeBranch.pinInput {tail : ℕ} (base : S.baseGroups=2^tail) (pin : _) :
    (address _ (active b.source base radix pin)).val=pin.1.val := by
  simp only [active,Equiv.apply_symm_apply]
  rw [b.seed.pinCoordinates]
  simp only [AtomSchedule.resetInputDigits,AtomSchedule.initialDigits,Equiv.symm_trans_apply,
    Equiv.trans_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  rfl

/-- A given exterior slab uses the same seed host in every copy. -/
theorem NativeBranch.pinHost {a b' : SeedPin} (same : a.2=b'.2) :
    host b.source a=host b.source b' := b.seed.pinHosts a b' same

theorem NativeBranch.seedRank (pin : SeedPin) :
    (b.source.vertex (host b.source pin)).val=
      (Fintype.equivFin (Site X.network.copyGraph) (.inr pin.2)).val := b.seed.pinRanks pin

include hp in
/-- Equal final hosts carry copies of a single original exterior slab. -/
theorem NativeBranch.originalSlab_eq {a a' : SeedPin} (eqn : host b.target a=host b.target a') :
    a.2=a'.2 := by
  have origin := b.path.previous_host_of_equal p hp _ b.recorded
    (Chronology.seed_particles X (Chronology.epochsSource G r c) b.source (S.initialDigits radix) b.seed) eqn
  have ranks := congrArg (fun v=>(b.source.vertex v).val) origin
  change (b.source.vertex (host b.source a)).val=(b.source.vertex (host b.source a')).val at ranks
  rw [NativeBranch.seedRank X G S b a, NativeBranch.seedRank X G S b a'] at ranks
  exact Sum.inr_injective ((Fintype.equivFin (Site X.network.copyGraph)).injective (Fin.ext ranks))

/-- Convert a physical copy ordinal to all initial group and local-row bits. -/
def copyBits {tail : ℕ} (base : S.baseGroups=2^tail) (radix : S.radix=2^k) :
    Fin S.copies ≃ Bits (S.groupWidth k tail 0+k) :=
  (S.initialDigits radix).trans ((S.resetInputDigits base radix 0).symm.trans (address _).symm)

theorem NativeBranch.source_bits {tail : ℕ} (base : S.baseGroups=2^tail) (pin : SeedPin) :
    active b.source base radix pin=copyBits S base radix pin.1 := by
  simp only [active]
  rw [b.seed.pinCoordinates]
  rfl

/-- Read the original physical pin using the final active coordinates and the collected
coordinates from this very branch. -/
def NativeBranch.originalPin {tail : ℕ} (base : S.baseGroups=2^tail)
    (live : Bits (S.groupWidth k tail S.length+k)) (frozen : Bits b.path.frozen)
    (slab : Fin (Fintype.card (Port P X.width))) : SeedPin :=
  ⟨(copyBits S base radix).symm ((NativeBranch.pinSpine X G S b hp base).cut.symm (live,frozen)),slab⟩

theorem NativeBranch.pinCoordinates {tail : ℕ} (base : S.baseGroups=2^tail)
    (live : Bits (S.groupWidth k tail S.length+k)) (frozen : Bits b.path.frozen) (slab : _) :
    let pin:=NativeBranch.originalPin X G S b hp base live frozen slab
    (NativeBranch.pinSpine X G S b hp base).cut (active b.source base radix pin)=(live,frozen) := by
  intro pin
  rw [NativeBranch.source_bits X G S b base pin]
  change (NativeBranch.pinSpine X G S b hp base).cut ((copyBits S base radix) ((copyBits S base radix).symm _))=_
  rw [Equiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

theorem NativeBranch.terminal_active {tail : ℕ} (base : S.baseGroups=2^tail)
    (live : Bits (S.groupWidth k tail S.length+k)) (frozen : Bits b.path.frozen) (slab : _) :
    active b.target base radix (NativeBranch.originalPin X G S b hp base live frozen slab)=live := by
  rw [←(NativeBranch.pinSpine X G S b hp base).active_eq]
  exact congrArg Prod.fst (NativeBranch.pinCoordinates X G S b hp base live frozen slab)

/-- At fixed slab and frozen coordinates, all final live groups and rows have one true
host. The initial copy is read by undoing each of the physically chosen remixes. -/
theorem NativeBranch.terminal_host {tail : ℕ} (base : S.baseGroups=2^tail)
    (x y : Bits (S.groupWidth k tail S.length+k)) (frozen : Bits b.path.frozen) (slab : _) :
    host b.target (NativeBranch.originalPin X G S b hp base x frozen slab)=
      host b.target (NativeBranch.originalPin X G S b hp base y frozen slab) := by
  apply (NativeBranch.pinSpine X G S b hp base).host_eq
  · exact b.seed.pinHosts _ _ rfl
  · exact (congrArg Prod.snd (NativeBranch.pinCoordinates X G S b hp base x frozen slab)).trans
      (congrArg Prod.snd (NativeBranch.pinCoordinates X G S b hp base y frozen slab)).symm

end
end Hierarchy.DescentSixParty

end OAI
