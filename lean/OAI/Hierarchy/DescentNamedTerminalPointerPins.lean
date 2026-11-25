import OAI.Hierarchy.DescentTerminalFrozenLength
import OAI.Hierarchy.DescentNamedNativeCaps
import OAI.Hierarchy.DescentExteriorLookup
import OAI.Hierarchy.DescentExteriorSpinePromotion

namespace OAI
/-! # A packed original copy, matrix and actual host list name the final local port -/
namespace Hierarchy.DescentExterior
open DescentGL DescentColonies Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
/-- The table's parameters are public bit widths. Its three data inputs are
the true cumulative matrix, the short home word and the original copy number. -/
def terminalPin (a b f matrix frozen copy : ℕ) : ℕ :=
  if width:b+f=a then
    let basis:=storedLayout a (matrix:Word (a*a))
    let parts:Bits b×Bits f:=(Spine.store width).symm (basis ((address a).symm (copy:Fin (2^a))))
    DescentTerminalFrozenRoster.dense f frozen (address f parts.2).val
  else 0

private theorem terminalPin_spine {I B C : Type} {a b f : ℕ}
    {initial : I → Bits a} {current : I → Bits b} {first : I → B} {last : I → C}
    (x : Spine initial current first last f) (bits : Bits a) (code copy : ℕ)
    (correct : (address a bits).val = copy) :
    terminalPin a b f (matrixCode x.matrix).val code copy =
      DescentTerminalFrozenRoster.dense f code (address f (x.cut bits).2).val := by
  have castMatrix : (((matrixCode x.matrix).val : ℕ) : Word (a*a)) = matrixCode x.matrix :=
    Fin.ext (Nat.mod_eq_of_lt (matrixCode x.matrix).isLt)
  have castCopy : (copy : Fin (2^a)) = address a bits := by
    rw [← correct]
    exact Fin.ext (Nat.mod_eq_of_lt (address a bits).isLt)
  rw [terminalPin, dite_eq_left x.width]
  change DescentTerminalFrozenRoster.dense f code ((address f)
    (((Spine.store x.width).symm ((storedLayout a ((matrixCode x.matrix).val : Word (a*a)))
      ((address a).symm (copy : Fin (2^a))))).2)).val = _
  rw [castMatrix, stored_matrixCode, castCopy, Equiv.symm_apply_apply]
  change DescentTerminalFrozenRoster.dense f code ((address f)
    (((Spine.store x.width).symm ((Spine.store x.width) (x.cut bits))).2)).val = _
  rw [LinearEquiv.symm_apply_apply]

private theorem terminalPin_spine_book {I B C : Type} {a b f num H : ℕ}
    {initial : I → Bits a} {current : I → Bits b} {first : I → B} {last : I → C}
    (x : Spine initial current first last f) (bits : Bits a) (copy : ℕ)
    (correct : (address a bits).val = copy)
    (homes : Fin num → Fin H) (frozen : Fin num → Fin (2^f)) (atHome : Fin H) :
    terminalPin a b f (matrixCode x.matrix).val
      (DescentTerminalFrozenRoster.book homes frozen atHome).val copy =
      DescentTerminalFrozenRoster.lookup f (Computability.BorderVNP.FragmentBucket.count homes atHome)
        (DescentTerminalFrozenRoster.book homes frozen atHome).val
        (address f (x.cut bits).2).val := by
  rw [terminalPin_spine x bits _ _ correct, DescentTerminalFrozenRoster.dense,
    DescentTerminalFrozenRoster.length_read]
end
end Hierarchy.DescentExterior

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical Fin.CommRing
noncomputable section
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)

open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace Branch
variable {tail : ℕ} (base : S.baseGroups=2^tail)
local notation "trace" => pinSpine X G S b hp base
local notation "E" => Fintype.card (Port P X.width)
local notation "H" => S.hostSize S.length
local notation "a" => S.groupWidth k tail S.length+k
local notation "N" => ((Epochs.finish G hu he r).state c).graph
local notation "A" => b.target.placement
local notation "f" => b.path.frozen
local notation "Cohort" => Fin (E*2^f)



local notation "homes" => cohortHome X G S b hp base
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "old" => b.origin.source
local notation "frozen" => (fun t:Cohort=>(finProdFinEquiv.symm t : Fin E×Fin (2^f)).2)
local notation "codeAt" => DescentTerminalFrozenRoster.book homes frozen
/-- The exact natural stored in a reached host's original frozen-cohort roster cell. -/
def frozenRosterCode (i:Fin H) : ℕ := (codeAt i).val

attribute [local irreducible] Branch.cohortHome Branch.densePin Branch.cohort Branch.densePinEquiv
  DescentTerminalFrozenRoster.book
theorem actual_pin_count (v:(N).Site) :
    DescentTerminalFrozenRoster.length f (codeAt (b.target.home v)).val=Fintype.card (Attached (N) v) := by
  rw [DescentTerminalFrozenRoster.length_read]
  simpa only [Fintype.card_fin] using (Fintype.card_congr (densePinEquiv X G S b hp base v)).symm

theorem decode_published_pin (v:(N).Site) (pin:Attached (N) v) :
    terminalPin initialBits a f (matrixCode (trace).matrix).val (codeAt (b.target.home v)).val pin.val.1.val=
      densePin X G S b hp base v pin := by
  exact (terminalPin_spine_book (pinSpine X G S b hp base) (active old base radix pin.val)
    pin.val.1.val (pinInput X G S b base pin.val) homes frozen (b.target.home v)).trans
    (pinOrdinalFromCopy X G S b hp base v pin)

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

-- Keep the named projections opaque while Lean indexes theorem signatures.
open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
  Branch.cohortHome Branch.cohort Branch.atCohort Branch.densePin
