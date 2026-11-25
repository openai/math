import OAI.Hierarchy.DescentPhysicalResetTailTariff
import OAI.Hierarchy.DescentDatedNodeMetadataVolume
import OAI.Hierarchy.DescentRetainedMovementBits
import OAI.Hierarchy.DescentDatedLocalScale
import OAI.Hierarchy.DescentGlobalControlRoom

namespace OAI
/-! # The numerical metadata charge in the compiled reset suffix -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentCompiler DescentCompiler.TerminalScale DescentDatedNodeMetadata DescentResetRetainedSetup
open DescentSIMDLookup Filter
noncomputable section

def metadataUnits (c : DescentDatedNodeMetadata.Chart) (args : ℕ) :=
  let work:=Chart.tallyWork args 7
  c.inputClock+c.loopUnits 1 work+7*(c.inputNames+c.labelUnits work)

/-- The expression used in the dated tail price includes the full word times
both control names and clocks. A short last row is paid by its actual host. -/
theorem metadataCharge_bits (c : DescentDatedNodeMetadata.Chart) (a b args w h ratio u : ℕ)
    (pack : (c.bits*c.nodes+c.bits)*c.lanes≤h/2) (key : max a (b+c.bits)*c.lanes≤h/2)
    (positive : 0<c.lanes) (density : c.groups≤c.lanes ∨ h≤c.lanes*u) (bus : w≤ratio*h) :
    metadataCharge c a b args*w≤(metadataUnits c args*ratio)*
      (c.hosts*h+c.hosts*c.groups*u+(2^(h/2)+1)*h):=by
  let U:=c.rows+2^(h/2)+1
  let work:=Chart.tallyWork args 7
  have lut : 2^(h/2) ≤ U := (Nat.le_add_left _ _).trans (Nat.le_succ _)
  have physical : c.rows ≤ U := (Nat.le_add_right _ _).trans (Nat.le_succ _)
  have upper := c.wordInvoices U h a b work 1 (Nat.succ_pos _) lut pack key
    (by simpa only [one_mul] using physical)
  have spent : metadataCharge c a b args≤ metadataUnits c args*U:=calc
    _ ≤ (c.inputClock+c.loopUnits 1 work)*U+7*((c.inputNames+c.labelUnits work)*U):=
      Nat.add_le_add upper.1 (Nat.mul_le_mul_left 7 upper.2)
    _ = _:=by unfold metadataUnits;dsimp only [work];ring
  have rows:=Layout.bounded_pitch_rows (H:=c.hosts) positive density
  have trace : U*h≤c.hosts*h+c.hosts*c.groups*u+(2^(h/2)+1)*h:=by
    change c.rows*h≤_ at rows
    dsimp only [U];simp only [Nat.add_mul,Nat.one_mul];omega
  calc
    _ ≤ (metadataUnits c args*U)*(ratio*h):=Nat.mul_le_mul spent bus
    _ = (metadataUnits c args*ratio)*(U*h):=by ring
    _ ≤ _:=Nat.mul_le_mul_left _ trace

theorem metadata_units_scale {ι : ℕ→Type*} (J : ℕ→ℕ) (c : ∀h,ι h→DescentDatedNodeMetadata.Chart)
    (args : ∀h,ι h→ℕ) (blocks : SmallAt J fun h i=>(c h i).blocks) (nodes : SmallAt J fun h i=>(c h i).nodes)
    (operands : SmallAt J args) : SmallAt J (fun h i=>metadataUnits (c h i) (args h i)):=by
  simp only [metadataUnits,Chart.inputClock,Chart.inputNames,Chart.loopUnits,Chart.labelUnits,Chart.jobs,
    Chart.names,Chart.tallyWork]
  repeat' first | assumption | exact SmallAt.const J _ | apply SmallAt.add | apply SmallAt.mul

theorem metadata_shared (rate saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀ (c : DescentDatedNodeMetadata.Chart) (a b args w J M ratio u : ℕ),
      J≤Nat.log 2 h → 2^h≤M → metadataUnits c args*ratio≤ scale J rate →
      (c.bits*c.nodes+c.bits)*c.lanes≤h/2 → max a (b+c.bits)*c.lanes≤h/2 → 0<c.lanes →
      (c.groups≤c.lanes ∨ h≤c.lanes*u) → w≤ratio*h →
      metadataCharge c a b args*w≤c.hosts*h*(metadataUnits c args*ratio)+
        c.hosts*c.groups*(metadataUnits c args*ratio*u)+M/(2^J)^saving:=by
  filter_upwards [global_control_shared 2 1 rate 1 saving] with h charged
  intro c a b args w J M ratio u height sites rates pack key positive density bus
  have extra:=charged J (rate*(J+1)) M height (by simp) sites
  let K:=metadataUnits c args*ratio
  have table : K*((2^(h/2)+1)*h)≤M/(2^J)^saving:=calc
    _ ≤ scale J rate*((2^(h/2)+2^(h/2))*(h+1)):=by
      apply Nat.mul_le_mul rates
      exact Nat.mul_le_mul (Nat.add_le_add_left (Nat.two_pow_pos _) _) (Nat.le_succ _)
    _ = (2*(h+1)^1*2^(rate*(J+1)))*2^(h/2):=by unfold scale;ring
    _ ≤ _:=extra
  apply (metadataCharge_bits c a b args w h ratio u pack key positive density bus).trans
  calc
    _ = c.hosts*h*K+c.hosts*c.groups*(K*u)+K*((2^(h/2)+1)*h):=by dsimp only [K];ring
    _ ≤ _:=Nat.add_le_add_left table _

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
