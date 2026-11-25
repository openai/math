import OAI.Hierarchy.DescentNamedTerminalPointerPins
import OAI.Hierarchy.DescentTerminalPointerPages

namespace OAI
/-! # Reading the genuine two shared exterior fields from the live terminal machine -/
namespace Hierarchy.DescentSixParty.SeedNamed
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
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S radix R r c) (hp : 0<p)

open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace Branch
variable {tail : ℕ} (base : S.baseGroups=2^tail)
local notation "trace" => pinSpine X G S b hp base
local notation "portCount" => Fintype.card (Port P X.width)
local notation "H" => S.hostSize S.length
local notation "N" => ((Epochs.finish G hu he r).state c).graph
local notation "A" => b.target.placement
local notation "f" => b.path.frozen
local notation "Cohort" => Fin (portCount*2^f)



local notation "homes" => cohortHome X G S b hp base
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "old" => b.origin.source
local notation "frozen" => (fun t:Cohort=>(finProdFinEquiv.symm t : Fin portCount×Fin (2^f)).2)
local notation "codeAt" => DescentTerminalFrozenRoster.book homes frozen

open DescentTerminalPointerDigits ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
variable {blocks cap Nslots slots d wb : ℕ} (pages : Gather.Pages blocks cap slots)
    (memory : Memory wb) (block : Fin blocks)
local notation "row_" => pages.source («N»:=Nslots) (d:=d) memory block
local notation "cap_" => 2^(8+S.capGain*S.length)
variable (raw : ∀ v : Fin (S.hostSize S.length), memory (pages.frozen.base+v.val) =
      ((DescentTerminalFrozenRoster.book (cohortHome X G S b hp base)
        (fun t : Fin (Fintype.card (Port P X.width) * 2^b.path.frozen) =>
          (finProdFinEquiv.symm t : Fin (Fintype.card (Port P X.width)) × Fin (2^b.path.frozen)).2) v).val :
        Computability.VPVNP.BurstRAM.Word wb))
    (frozenFits : (b.path.frozen+1)*2^(8+S.capGain*S.length) ≤ d) (word : d≤wb)

theorem frozenRosterCode_lt (v:Fin H) : frozenRosterCode X G S b hp base v < 2^((f+1)*cap_) := by
  have order : (codeAt v).val < 2^((f+1)*Computability.BorderVNP.FragmentBucket.count homes v) := by
    simpa only [pow_mul] using (codeAt v).isLt
  exact order.trans_le (Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_left _ (cohort_cap X G S b hp base v)))

include raw frozenFits word in
theorem memory_frozen (v:Fin H) : (row_ v fcol).val=(codeAt v).val := by
  have order: (codeAt v).val < 2^((f+1)*Computability.BorderVNP.FragmentBucket.count homes v) := by
    simpa only [pow_mul] using (codeAt v).isLt
  have fits: (codeAt v).val < 2^d :=order.trans_le (Nat.pow_le_pow_right (by decide)
    ((Nat.mul_le_mul_left _ (cohort_cap X G S b hp base v)).trans frozenFits))
  have whole:=fits.trans_le (Nat.pow_le_pow_right (by decide) word)
  change ((memory ((pages.address («N»:=Nslots) fcol block).atHost v)).val:DescentSIMDLookup.Cell d).val=_
  rw [(pages.fixed («N»:=Nslots) block).2.2]
  change ((memory (pages.frozen.base+v.val)).val:DescentSIMDLookup.Cell d).val=_
  rw [raw v,Fin.val_cast_of_lt whole,Fin.val_cast_of_lt fits]

include raw frozenFits word in
theorem memory_pin_count (v:(N).Site) :
    DescentTerminalFrozenRoster.length f (row_ (b.target.home v) fcol).val=Fintype.card (Attached (N) v) := by
  rw [memory_frozen X G S b hp base pages memory block raw frozenFits word]
  exact actual_pin_count X G S b hp base v

include word in
/-- Matrix column of the actual gathered source, at every host address. -/
theorem memory_matrix (h : Fin H) (width : initialBits*initialBits≤d)
    (mat : memory pages.matrix=((matrixCode (trace).matrix).val:Computability.VPVNP.BurstRAM.Word wb)) :
    (row_ h mcol).val=(matrixCode (trace).matrix).val :=by
  have fit : (matrixCode (trace).matrix).val<2^d:=(matrixCode (trace).matrix).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) width)
  have full:=fit.trans_le (Nat.pow_le_pow_right (by decide) word)
  change ((memory ((pages.address («N»:=Nslots) mcol block).atHost h)).val:DescentSIMDLookup.Cell d).val=_
  rw [(pages.fixed («N»:=Nslots) block).2.1]
  change ((memory pages.matrix).val:DescentSIMDLookup.Cell d).val=_
  rw [mat,Fin.val_cast_of_lt full,Fin.val_cast_of_lt fit]

include raw frozenFits word in
/-- The two physical scalar words used by the intersection of the cumulative
matrix and the frozen roster at the same host of the same gathered source. -/
theorem gathered_exterior_words (h : Fin H) (width : initialBits*initialBits≤d)
    (mat : memory pages.matrix=((matrixCode (trace).matrix).val:Computability.VPVNP.BurstRAM.Word wb)) :
    (row_ h mcol).val=(matrixCode (trace).matrix).val ∧
      (row_ h fcol).val=frozenRosterCode X G S b hp base h :=
  ⟨memory_matrix X G S b hp base pages memory block word h width mat,
    memory_frozen X G S b hp base pages memory block raw frozenFits word h⟩

include raw frozenFits word in
theorem memory_pin (v:(N).Site) (pin:Attached (N) v)
    (width : initialBits*initialBits≤d)
    (mat : memory pages.matrix=((matrixCode (trace).matrix).val:Computability.VPVNP.BurstRAM.Word wb)) :
    terminalPin initialBits (S.groupWidth k tail S.length+k) f (row_ (b.target.home v) mcol).val
      (row_ (b.target.home v) fcol).val pin.val.1.val=densePin X G S b hp base v pin := by
  obtain ⟨matrixRead,frozenRead⟩:=gathered_exterior_words (Nslots:=Nslots) X G S b hp base pages memory block
    raw frozenFits word (b.target.home v) width mat
  rw [matrixRead,frozenRead]
  exact decode_published_pin X G S b hp base v pin

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Branch.pinSpine Branch.cohortHome Branch.frozenRosterCode
