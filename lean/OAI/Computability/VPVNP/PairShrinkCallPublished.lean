import OAI.Computability.VPVNP.PairShrinkCallHeader
import OAI.Computability.VPVNP.CompressorShrinkHeaderReads
import OAI.Computability.VPVNP.CompressorBlockHeadStability

/-!
# A resident map's header after the native level publications

Four term words are written first, followed by fourteen data heads. Their
reports keep the old incidence and DFS metadata outside those intervals.
The bundle ranker and term recipe identify the addresses stored at the
actual offsets for AB slices and the selected term.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCallHeader

open Compression Compression.PackingData CompressorRecords BurstRAM CompressorRecords.PhaseRecipe
open CompressorRecords.DescriptorSpace
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ}
local notation "a" => ShrinkBlockInputs.a i
variable (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
variable (sel : X.ShrinkSelection B.shrink) (T : IncidenceDirectory w) (origin : ℕ)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

local notation "term" => ShrinkInput.termHead (w := w) X origin
local notation "dense" => ShrinkInput.demandHead (w := w) X origin
local notation "side" => X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth sel
local notation "Z" => ShrinkInput.plan X origin
local notation "q" => ShrinkRankSpace.Shape.collectBank Z w
local notation "wb" => ShrinkInput.widthBase X origin
local notation "abStart" => ShrinkWidthArena.abBase X q wb
local notation "F" => BlockProgram.geometry B
local notation "initial" => BlockProgram.arena B i.val 0
local notation "tr" => BlockHeadStability.shrinkTerms B i
local notation "dr" => BlockDataHeads.values B F i initial (BlockProgram.arena B i.val 1)
  (BlockProgram.arena B i.val 2) (BlockProgram.arena B i.val 3)

variable (L : Layout) (first : ℕ) (pub : Fin 5 → Word w) (state : Word w) (before : Memory w)
local notation "here" => levelStart L (first + i.val)
local notation "mid" => PublishedHeads.image pub state before (here + 36) tr
local notation "out" => PublishedHeads.image pub state mid (here + 40) dr

private theorem recipe_heads {mem : Memory w}
    (h : ShrinkBundlePlan.Reads X F i.val initial pub state mem origin T)
    (space : (Z).stop < 2 ^ w) :
    (ShrinkTermRecipe.term a (ShrinkBundlePlan.termInputs i.val a initial)).eval pub state mem =
      term ∧
    (ShrinkTermRecipe.dense a (ShrinkBundlePlan.termInputs i.val a initial)).eval pub state mem =
      dense := by
  let pars := ShrinkBundlePlan.termInputs i.val a initial
  have described := ShrinkBundlePlan.term_input X h space
  have dt := ShrinkTermRecipe.eval_term pars X pub state mem described
  have dd := ShrinkTermRecipe.eval_dense pars X pub state mem described
  have size := (Z).values T (ShrinkInput.placementBank X T origin) Fintype.card_pos space
  have stride : (q 4).val = (Z).Q := size.stride
  have startEq : abStart + 2 * ShrinkTermRecipe.M X = ShrinkInput.stop X origin := by
    change (wb + 2 * ((Z).B * (q 4).val) + 2 * ((Z).B * (q 4).val) + 2 * (Z).B) +
      2 * ((Z).B * (Z).Q) = wb + 6 * ((Z).B * (Z).Q) + 2 * (Z).B
    rw [stride]; ring
  rw [startEq] at dt dd
  exact ⟨dt, dd⟩

set_option maxHeartbeats 1200000 in
-- Identify every selected field in the two dependent publication walks.
/-- The two chronological publication walks give the canonical resident
header. The chosen score cell and the two DFS pointers are read at their
own actual locations in the preceding memory. -/
theorem Level.of_publications (older stride bankBase : ℕ)
    (header : ShrinkHeaderReads.Header i X T origin L first before)
    (entry : LevelFields.Entry L first pub state before)
    (pitch : (pub 1 - 1).val < here + 36)
    (dfs : before (here + 14) = (older : Word w) ∧ before (here + 15) = (stride : Word w))
    (scoreWord : before (((ShrinkInput.termEnd X origin 10 + 2 : ℕ) : Word w)).val =
      ((side).toNat : Word w))
    (tableFit : here + 61 < 2 ^ w) (tableWord : before (here + 61) = (bankBase : Word w))
    (space : (Z).stop < 2 ^ w)
    (terms : PublishedHeads.Published L pub state before (here + 36)
      (fun j : Fin 4 ↦ LevelFields.address i.val (36 + j.val)) tr)
    (data : PublishedHeads.Published L pub state mid (here + 40)
      (fun j : Fin 14 ↦ LevelFields.address i.val (40 + j.val)) dr) :
    Level X B.shrink sel (here : Word w) out T origin older stride bankBase := by
  have unchanged (n : ℕ) (hn : n < 36 ∨ 54 ≤ n) : out (here + n) = before (here + n) := by
    exact (data.outside _ (by unfold PublishedHeads.Outside; omega)).trans
      (terms.outside _ (by unfold PublishedHeads.Outside; omega))
  have atTerm (j : Fin 4) : out (here + (36 + j.val)) = (tr j).eval pub state before := by
    rw [← Nat.add_assoc]
    exact (data.outside _ (.inl (by have := j.isLt; omega))).trans (terms.stored j)
  have atData (j : Fin 14) : out (here + (40 + j.val)) = (dr j).eval pub state mid := by
    rw [← Nat.add_assoc]; exact data.stored j
  have middle (n : ℕ) (hn : n < 36 ∨ 40 ≤ n) : mid (here + n) = before (here + n) :=
    terms.outside _ (by unfold PublishedHeads.Outside; omega)
  have readMid : ShrinkHeaderReads.Header i X T origin L first mid :=
    ⟨header.room, (middle _ (by decide)).trans header.vertices, (middle _ (by decide)).trans
      header.degree, (middle _ (by decide)).trans header.lanes,
      (middle _ (by decide)).trans header.residual, fun j ↦ (middle _ (Or.inr (by omega))).trans
      (header.incidence j), (middle _ (by decide)).trans header.scratch⟩
  have entered : LevelFields.Entry L first pub state mid :=
    ⟨entry.pointer, (terms.outside _ (.inl pitch)).trans entry.pitch⟩
  have read := header.reads B entry
  have read' := readMid.reads B entered
  have th := (recipe_heads B i X T origin pub state read space).1
  have dh := (recipe_heads B i X T origin pub state read' space).2
  have ranks := ShrinkBundlePlan.head_values X read'
  let pars := ShrinkBundlePlan.termInputs i.val a initial
  have n := ShrinkTermRecipe.eval_count pars X pub state before
    (ShrinkBundlePlan.term_input X read space)
  have score : (SelectedPlan.layout (ShrinkBlockInputs.selectedInputs B F i initial)).eval
      pub state before = ((side).toNat : Word w) := by
    change before (((ShrinkTermRecipe.term a pars).eval pub state before +
      (ShrinkTermRecipe.count a pars).eval pub state before * ((10 : ℕ) : Word w)) + 2).val = _
    rw [th, n]
    have address : (term + (ShrinkTermRecipe.M X : Word w) * ((10 : ℕ) : Word w)) + 2 =
        ((ShrinkInput.termEnd X origin 10 + 2 : ℕ) : Word w) := by
      change ((((ShrinkInput.stop X origin + 2 * ShrinkTermRecipe.M X : ℕ) : Word w) +
        (ShrinkTermRecipe.M X : Word w) * ((10 : ℕ) : Word w)) + 2) =
        ((ShrinkInput.stop X origin + 2 * ShrinkTermRecipe.M X + ShrinkTermRecipe.M X * 10 + 2 :
          ℕ) : Word w)
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [address]
    exact scoreWord
  have abHead : (BlockProgram.arena B i.val 1).eval pub state mid = (bankBase : Word w) :=
    (LevelFields.eval_scalar entered i.val 61 tableFit).trans
      ((middle _ (by decide)).trans tableWord)
  have addr (n : ℕ) (hn : n ≤ 59) : (((here : Word w) + (n : Word w))).val = here + n := by
    rw [← Nat.cast_add, Fin.val_natCast, Nat.mod_eq_of_lt (by have := header.room; omega)]
  have ten : (tr 1).eval pub state before = ((10 : ℕ) : Word w) := rfl
  have co : T.column 3 = T.actualOut := rfl
  have ci : T.column 4 = T.actualIn := rfl
  have cw : T.column 5 = T.width := rfl
  constructor
  · simpa only [Nat.cast_zero] using (congrArg out (addr 0 (by decide))).trans
      ((unchanged _ (by decide)).trans header.vertices)
  · simpa only [Nat.cast_one] using (congrArg out (addr 1 (by decide))).trans
      ((unchanged _ (by decide)).trans header.degree)
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 2 (by decide))).trans
      ((unchanged _ (by decide)).trans header.lanes)
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 3 (by decide))).trans
      ((unchanged _ (by decide)).trans header.residual)
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 14 (by decide))).trans
      ((unchanged _ (by decide)).trans dfs.1)
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 15 (by decide))).trans
      ((unchanged _ (by decide)).trans dfs.2)
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 36 (by decide))).trans
      ((atTerm 0).trans th)
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 37 (by decide))).trans
      ((atTerm 1).trans ten)
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 38 (by decide))).trans
      ((atTerm 2).trans score)
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 43 (by decide))).trans
      ((atData 3).trans abHead)
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 44 (by decide))).trans
      ((atData 4).trans ranks.owner)
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 45 (by decide))).trans
      ((atData 5).trans ranks.ranks)
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 46 (by decide))).trans
      ((atData 6).trans ranks.ids)
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 47 (by decide))).trans
      ((atData 7).trans dh)
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 57 (by decide))).trans
      ((unchanged _ (by decide)).trans ((header.incidence 3).trans co))
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 58 (by decide))).trans
      ((unchanged _ (by decide)).trans ((header.incidence 4).trans ci))
  · simpa only [Nat.cast_ofNat] using (congrArg out (addr 59 (by decide))).trans
      ((unchanged _ (by decide)).trans ((header.incidence 5).trans cw))

end PairSimulation.ShrinkCallHeader

end VPVNP
end Computability
end OAI
