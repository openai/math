import OAI.Computability.VPVNP.PairShrinkResidentHeaderWords
import OAI.Computability.VPVNP.PairShrinkSiteBank
import OAI.Computability.VPVNP.PairShrinkResidentSources

/-!
# Recovering both native party contracts in the retained memory

The old and new DFS layer words select the actual node addresses. The
two contracts use the same party, selected term, private arena and
register bank. The surviving endpoints use the next pass's pitch word.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkResidentPublication

open BurstRAM BurstRAM.PrivateRAM Compression Compression.ShrinkMotif CompressorRecords
open DescriptorSpace ShrinkBlockInputs ShrinkSlots ShrinkPartyNative
open scoped Fin.CommRing

variable {K : Type*} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} {δ : ℝ} (X : State (a i) (packingLaneBits (a i) g))
variable (ready : Ready (2 ^ a i) (Shrink.colors (a i)) (2 ^ b i) δ)
variable (sel : SelectedScore.Selection B X) (m : X.packingData.Motif) (party : Fin 6)
variable (base : Word w) (positions blocks cur : ℕ)
variable (bounds : ShrinkResidentSources.Bounds B i X base positions blocks cur)
variable (n rowEnd older later : ℕ)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "here" => levelStart L cur
local notation "next" => levelStart L (cur + 1)
local notation "cut" => tableBase L cur (0 : Fin 6)
local notation "term" => ShrinkInput.termHead (w := w) X cut
local notation "sh" => levelShape (b := b i) X
local notation "heads" => ShrinkOutput.heads sh (SelectedArena.roleBase X term 10)
  (tableBase L cur (3 : Fin 6))
local notation "absolute" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X cut) w
local notation "T" => packedIncidence L w cur (DemandRAM.oldCount X)
local notation "U" => packedIncidence L w (cur + 1) (actualCount sh)
local notation "side" => selectedLayout X B.shrink sel
local notation "Y" => X.shrinkNext B.shrink ready sel
local notation "site" => X.packingData.shrinkPartySite side m party
local notation "degree" => slotDegree S
local notation "R" => TerminalLayout.privateRegions degree n rowEnd (Fintype.card B.Entry)

variable (child : ShrinkCallDemandCells.Old X (selectedLayout X B.shrink sel) m party)
variable (parent : (X.shrinkNext B.shrink ready sel).network.Half
  (X.packingData.shrinkPartySite (selectedLayout X B.shrink sel) m party))
local notation "J" => ShrinkCanonicalJob.job B i X ready sel m party base positions blocks cur
  bounds n rowEnd older later child parent
variable (mem : Memory w)
local notation "O" => ShrinkCallABI.operands degree

section Bank
variable (P : Fin 5 → Word w) (state : Word w)

set_option maxHeartbeats 1500000 in
-- The old and successor graph types reduce through the canonical job and both slot directories.
/-- Decode the old and successor party headers from the selected payload and
the DFS locator's live inputs. All table and field capacity bounds come
from the shrinking level allocation. -/
private theorem bank (words : ShrinkResidentHeaders.Words B i X sel base positions blocks cur n mem)
    (data : ShrinkResidentSources.Data B i X ready sel base positions blocks cur mem)
    (oldLayer : mem (here + 14) = (older : Word w))
    (newLayer : mem (next + 14) = (later : Word w))
    (newStride : mem (next + 15) = ((B.recordLimit + 2 : ℕ) : Word w))
    (locator : P 0 = (here : Word w))
    (motif : state.val = (ShrinkMotifOrder.stateNumber X m).val)
    (hidden : P 4 = (ShrinkCallABI.hiddenBase R n : Word w))
    (hist : P 3 = ((R).histBase : Word w))
    (node : P 1 = ((J).node : Word w)) :
    (J).OldPublished O P state mem (here : Word w) T cut ∧
      (J).SupplyPublished O ShrinkCallABI.node P state mem heads absolute U later
        (B.recordLimit + 2) := by
  have geom := ShrinkCanonicalJob.geometry B i X ready sel m base positions blocks cur bounds
  have word (k : ℕ) (small : k ≤ 65) : (((here : Word w) + (k : Word w))).val = here + k := by
    have room := words.oldRoom
    rw [← Nat.cast_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have baseVal : (here : Word w).val = here := Nat.mod_eq_of_lt (by have := words.oldRoom; omega)
  have layer : mem ((here : Word w) + 14).val = (older : Word w) := by
    rw [show (14 : Word w) = ((14 : ℕ) : Word w) from rfl, word 14 (by decide)]
    exact oldLayer
  have len : mem ((here : Word w) + 17).val = (n : Word w) := by
    rw [show (17 : Word w) = ((17 : ℕ) : Word w) from rfl, word 17 (by decide)]
    exact words.length
  have lengthAt : mem (P 0 + 17).val = (n : Word w) := by rw [locator, len]
  have live : ShrinkCallHeader.Live X m O P state (here : Word w) mem (R).arguments
      (ShrinkCallABI.hiddenBase R n) (n ^ 2) (R).histBase := by
    refine ⟨locator, motif, lengthAt, ?_, hidden, ?_, hist⟩
    · change ((2 * degree : ℕ) : Word w) * mem (P 0 + 17).val + 1 =
        ((2 * degree * n + 1 : ℕ) : Word w)
      simp only [lengthAt, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    · change mem (P 0 + 17).val * mem (P 0 + 17).val = ((n ^ 2 : ℕ) : Word w)
      rw [lengthAt, pow_two, Nat.cast_mul]
  have old : (J).OldPublished O P state mem (here : Word w) T cut :=
    ⟨{words.level with oldLayer := layer},
      live,
      rfl, data.old, geom.rank, geom.ab, data.slices.abFields _⟩
  refine ⟨old, Job.SupplyPublished.of_header (J) O ShrinkCallABI.node old heads U next later
    (B.recordLimit + 2) ?_ ?_ ?_ ?_ ?_ ?_ newLayer newStride ?_ ?_ ?_ data.absolute data.sorted
    geom.absolute geom.slot geom.degree geom.two geom.lanes geom.allocation ?_ data.successor
    geom.capacity node⟩
  · rw [baseVal]; have := words.oldRoom; omega
  · have := words.nextRoom; omega
  · rw [baseVal]; exact words.supply.absolute
  · rw [baseVal]; exact words.supply.successor
  · rw [baseVal]; exact words.supply.inverse
  · rw [baseVal]; exact words.supply.interval
  · exact words.successor.incidence (3 : Fin 6)
  · exact words.successor.incidence (4 : Fin 6)
  · exact words.successor.incidence (5 : Fin 6)
  · intro j
    have h := data.slices.intervals j
    rw [geom.split_eq] at h
    exact h

end Bank

local notation "P" => ShrinkSiteBank.pub (here : Word w) (Job.node J : Word w) R n
local notation "idx" => Fin.val (ShrinkMotifOrder.stateNumber X m)
local notation "stateWord" => (idx : Word w)

/-- The static five-word bank gives the same two native contracts for each
resident party, whether its map is reached during a scan or read as a row. -/
theorem published_words
    (words : ShrinkResidentHeaders.Words B i X sel base positions blocks cur n mem)
    (data : ShrinkResidentSources.Data B i X ready sel base positions blocks cur mem)
    (oldLayer : mem (here + 14) = (older : Word w))
    (newLayer : mem (next + 14) = (later : Word w))
    (newStride : mem (next + 15) = ((B.recordLimit + 2 : ℕ) : Word w)) :
    (J).OldPublished O P stateWord mem (here : Word w) T cut ∧
      (J).SupplyPublished O ShrinkCallABI.node P stateWord mem heads absolute U later
        (B.recordLimit + 2) := by
  have fit := (ShrinkCanonicalJob.geometry B i X ready sel m base positions blocks cur
    bounds).absolute
  apply bank B i X ready sel m party base positions blocks cur bounds n rowEnd older later child
    parent mem P stateWord words data oldLayer newLayer newStride rfl _ rfl rfl rfl
  exact Nat.mod_eq_of_lt (by omega : idx < 2 ^ w)

variable {p r : ℕ} (cfg : Config w p r) (common : Fin 24 ↪ Fin r)
local notation "regPub" => ShrinkCallABI.pub cfg common
local notation "regState" => ShrinkCallABI.state cfg common

/-- The locator and map-loop registers instantiate the same resident operands. -/
theorem published
    (words : ShrinkResidentHeaders.Words B i X sel base positions blocks cur n mem)
    (data : ShrinkResidentSources.Data B i X ready sel base positions blocks cur mem)
    (oldLayer : mem (here + 14) = (older : Word w))
    (newLayer : mem (next + 14) = (later : Word w))
    (newStride : mem (next + 15) = ((B.recordLimit + 2 : ℕ) : Word w))
    (locator : cfg.reg (common 11) = (here : Word w))
    (motif : (cfg.reg (common 18)).val = idx)
    (hidden : cfg.reg (common 8) = (ShrinkCallABI.hiddenBase R n : Word w))
    (hist : cfg.reg (common 10) = ((R).histBase : Word w))
    (node : cfg.reg (common 0) = ((J).node : Word w)) :
    (J).OldPublished O regPub regState mem (here : Word w) T cut ∧
      (J).SupplyPublished O ShrinkCallABI.node regPub regState mem heads absolute U later
        (B.recordLimit + 2) :=
  bank B i X ready sel m party base positions blocks cur bounds n rowEnd older later child parent
    mem regPub regState words data oldLayer newLayer newStride locator motif hidden hist node

end PairSimulation.ShrinkResidentPublication

end

end VPVNP
end Computability
end OAI
