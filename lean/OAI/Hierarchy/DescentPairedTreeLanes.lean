import OAI.Hierarchy.DescentMeasuredFallbackLane

namespace OAI
/-! # Both operands at every level of the installed ordered tree -/
namespace Hierarchy.DescentTreeLaneProgram
open Computability.BorderVNP.Crossing DescentKernelHistory DescentRouterSlots DescentContactTree DescentResetGates
open DescentOrderedReset DescentOrderedWords DescentTreeGateRefs DescentNamedContact
open DescentFallbackOperandBranch DescentFallbackItemSelect
open scoped BigOperators Classical
noncomputable section
set_option quotPrecheck false
variable {I C R W : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W]
variable (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (cfg : Config) (p : ℕ) (hp : 0<p)
variable (s : Bool) (w : W) {depth n : ℕ} (book : LinkId owner s w ↪ Node depth) (key : I↪Fin n)
local notation "wt" => fun _ : I=>cfg.batches*p
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "lp" => link contact owner s w
local notation "N" => DescentFixedExceptionalRouter.device D contact input site owner wt s w book
local notation "code" => DescentFixedNamedContact.code book lp
local notation "ids" => itemKey key contact owner s w
local notation "ops" => program D contact input site owner align cfg.batches p hp s w book key
local notation "atNode" k:arg i:arg => (⟨k,prefixAt code (k).val i⟩ : Physical.Site depth)

def nextLevel {depth : ℕ} (level : Fin (depth+1)) : Fin (depth+1) :=
  Fin.lastCases (Fin.last depth) (fun t=>t.succ) level

variable (Y : ℕ) (e : DescentRouterSlots.Item contact owner s w) (b : Fin cfg.batches)
variable (items : Fin cfg.count→DescentFallbackItemSelect.Item) (sets : Fin (depth+1)→Finset (Fin cfg.count))
variable (j : Fin cfg.count) (node : ℕ) (phase : node%cfg.batches=b.val)
local notation "lane" k:arg a:arg => (((ops Y (atNode k e)).op (⟨e,rfl⟩,b)).arg (a : Fin 2))

include phase
omit [Fintype R] in
theorem paired_words (sole : Subsingleton (InputId site s w))
    (complete : ∀level : Fin (depth+1), (sets level).card=Fintype.card (Cell code level.val (prefixAt code level.val e)) ∧
      rank items (sets level) j=(DescentOrderedWords.before (Contact.cellKey ids code level.val (prefixAt code level.val e)) ⟨e,rfl⟩).card)
    (level : Fin (depth+1)) :
    measuredWord cfg p (lane level 0) items (sets level) j node ∧
      measuredWord cfg p (lane level 1) items (sets (nextLevel level)) j node :=by
  constructor
  · induction level using Fin.cases with
    | zero =>
      exact previous_root_words D contact input site owner align cfg p hp s w book key Y e b
        items (sets 0) j node phase sole (complete 0).1 (complete 0).2
    | succ t =>
      exact previous_cell_words D contact input site owner align cfg p hp s w book key Y e b
        items (sets t.succ) j node phase t (complete t.succ).1 (complete t.succ).2
  · induction level using Fin.lastCases with
    | last=>
      simp only [nextLevel,Fin.lastCases_last]
      exact following_leaf_words D contact input site owner align cfg p hp s w book key Y e b
        items (sets (Fin.last depth)) j node phase (complete (Fin.last depth)).1 (complete (Fin.last depth)).2
    | cast t=>
      simp only [nextLevel,Fin.lastCases_castSucc]
      exact following_cell_words D contact input site owner align cfg p hp s w book key Y e b
        items (sets t.succ) j node phase t (complete t.succ).1 (complete t.succ).2

end
end Hierarchy.DescentTreeLaneProgram

end OAI
