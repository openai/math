import OAI.Computability.VPVNP.CompressorCompiledResident
import OAI.Computability.VPVNP.PairShrinkRoleMapStart
import OAI.Computability.VPVNP.PairShrinkCallABI
import OAI.Computability.VPVNP.PairShrinkHiddenRows
import OAI.Computability.VPVNP.PairShrinkHiddenInputs

/-!
# The selected shrinking site's hidden arguments in the packed calendar

The compressor stores the count and identifier row for each owner. The same
level stores the selected term words and the five pointers used by the site's
hidden-field reader. A zero assignment supplies the parser with the exact
field lengths and identifiers for arbitrary later guesses.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkRole.PackedHidden

open BurstRAM Compression Compression.ShrinkMotif CompressorRecords DescriptorSpace
open ShrinkBlockInputs ShrinkSliceSweep ShrinkHistoryRows ShrinkHiddenGuess NetworkKernel
open scoped Fin.CommRing
set_option quotPrecheck false

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) (i : Fin S.steps)
  {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
  (base : Word w) (positions blocks cur n : ℕ)

local notation "D" => BlockProgram.layout B base.val positions blocks
local notation "head" => levelStart D cur
local notation "tab" => (fun j : Fin 6 => tableBase D cur j)
local notation "term" => ShrinkInput.termHead (w := w) X (tab 0)
local notation "role" => SelectedArena.roleBase X term (10 : Word w)
local notation "side" => SelectedFinish.chosen B X sel
local notation "widths" => ShrinkHiddenRows.widths X B.shrink sel
local notation "L" => ShrinkResidentLayout.layout X (tab 5)
local notation "params" => (L).params (a i) false w
local notation "T" => ShrinkOutput.splitBank (b := b i) X B.shrink sel term 10 role (tab 2)
local notation "siteType" => MapResidentRows.Site X

/-- These words are obtained from the current level, the packed site ordinal,
and the argument frame at the actual vertex. -/
abbrev arguments (R : LeafArena.Regions) (v : siteType) : Args w :=
  ShrinkHiddenRows.args X T params v (ShrinkCallABI.hiddenBase R n) (n * n)

/-- The identifiers and lengths are independent of the guessed hidden values. -/
def zeroRows (v : siteType) : List Row :=
  ShrinkHiddenSlots.rows X side widths v (fun _ _ => ⟨0, Nat.two_pow_pos _⟩)

variable (R : LeafArena.Regions) (v : MapResidentRows.Site X)
local notation "arg" => arguments B i X sel base positions blocks cur n R v
local notation "seed" => zeroRows B i X sel v

/-- Inputs required by the physical hidden reader, for this exact packed site. -/
structure Facts (m : Memory w) : Prop where
  selectors : (arg).selectorBits = (B.shrink.selectorBits : Word w)
  rowStride : (arg).rowStride = ShrinkVertexImage.hiddenStride i
  headRoom : head + 38 < 2 ^ w
  headers : Header.Published arg head m
  countFit : (arg).countBase + (arg).owner < 2 ^ w
  count : (m ((arg).countBase + (arg).owner)).val = (seed).length
  valid : ValidRows arg m seed
  scratch : (arg).scratchBase = ShrinkCallABI.hiddenBase R n
  pitch : (arg).slotStride = n * n
  owner : (arg).owner = (MapResidentRows.siteIndex X v).val

set_option maxHeartbeats 2000000 in
-- The selected split bank and packed owner order are dependent on the stage exponent.
/-- Recover every external input from the native compressor payload. The only
additional bounds here concern the post-stack private reservation and the
fixed selector literal. -/
theorem of_payload (m : Memory w)
    (payload : CompiledResident.ShrinkPayload B base positions blocks n cur i X sel m)
    (selectors : B.shrink.selectorBits < 2 ^ w)
    (slots : ∀ motif t, widths motif (!side, t) ≤ n * n)
    (space : ShrinkCallABI.hiddenBase R n + (hiddenOrder X).length * (n * n) < 2 ^ w) :
    Facts B i X sel base positions blocks cur n R v m := by
  classical
  have room := payload.words.oldRoom
  have h10 : (10 : Word w).val = 10 := Nat.mod_eq_of_lt (show 10 < 2 ^ w by omega)
  have splitRoom := payload.bounds.packedRoom
  rw [h10] at splitRoom
  have allocation : (T).Fits := ShrinkOutput.fits X B.shrink sel term 10 role (tab 2)
    (S.shrink i) (by decide) splitRoom
  have residentFit : (L).endAddr < 2 ^ w :=
    payload.bounds.residentEnd.trans_lt
      ((levelStart_mono D payload.bounds.nextLive.le).trans_lt payload.bounds.room)
  have terms : Terms X.packingData X.shrinkNumber (Shrink.packedIndex X.baseIndex) T
      B.shrink X.packingWidth sel m := by
    intro idx
    let motif := (ShrinkMotifOrder.stateNumber X).symm idx
    have h := payload.sources.terms motif
    have e : ShrinkTermSelection.rowBase X term 10 motif =
        Fin.ofNat (2 ^ w) ((term).val + idx.val * 10) := by
      simp only [ShrinkTermSelection.rowBase, motif, Equiv.apply_symm_apply]
    rw [e] at h
    exact h
  have dir : Directory (hiddenOrder X) (packedOrder X) (X.packingData.shrinkInternalOwner side)
      params m := payload.sources.residents false
  have selected : (T).selectors.val = B.shrink.selectorBits := Nat.mod_eq_of_lt selectors
  let h : Placed (X.packingData.shrinkInternalOwner side) (internalLabel widths side) v :=
    fun _ _ => ⟨0, Nat.two_pow_pos _⟩
  obtain ⟨countFit, rowFit⟩ := ShrinkHiddenRows.directory_fit X T (tab 5) v residentFit
    (ShrinkCallABI.hiddenBase R n) (n * n) widths h
  obtain ⟨_, _, _, _, counts, stride, rows⟩ :=
    ShrinkResidentLayout.frame X (tab 5) false residentFit
  have headAt (j : ℕ) (hj : j ≤ 65) : ((head : Word w) + (j : Word w)).val = head + j := by
    rw [← Nat.cast_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hdr : Header.Published arg head m := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change m (head + 31) = (((params 3).val : ℕ) : Word w)
      rw [counts]
      exact payload.words.residentHeads 1
    · change m (head + 32) = (((params 5).val : ℕ) : Word w)
      rw [rows]
      exact payload.words.residentHeads 2
    · rw [← headAt 36 (by decide)]
      exact payload.words.level.termHead.trans (Fin.cast_val_eq_self _).symm
    · rw [← headAt 37 (by decide)]
      exact payload.words.level.termStride
    · rw [← headAt 38 (by decide)]
      exact payload.words.level.layout
  exact ⟨rfl, stride, by omega, hdr, countFit,
    ShrinkHiddenRows.count X T params m dir widths v h _ _,
    ShrinkHiddenRows.valid_rows X B.shrink sel T params m terms allocation selected dir v h
      _ _ slots space rowFit.le, rfl, rfl, rfl⟩

end PairSimulation.ShrinkRole.PackedHidden

end

end VPVNP
end Computability
end OAI
