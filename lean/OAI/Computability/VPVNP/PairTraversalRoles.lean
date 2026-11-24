import OAI.Computability.VPVNP.PairTraversalStageSize
import OAI.Computability.VPVNP.PairTraversalRoleNative

/-!
# Routing local vertex visits by their actual compressor pass

A cursor input is visited as a leaf. Each later descriptor belongs to the
output of a particular selected shrinking or refresh pass. Its tag comes from
that pass's origin before the state and its term are erased to a history.
The resulting tagged layers retain the same order and placement fibers as the
selected local parsers used by the native depth-first traversal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRoles

open CompressorRecords Compression LocalHistory TraversalRows BurstRAM
open scoped Fin.CommRing

/-- The three cases of a vertex visit. -/
inductive Role where
  | cursor
  | shrink
  | refresh
  deriving DecidableEq

/-- Numerical DFS dispatch tag, assigning zero to a cursor leaf, one to a shrink, and two to a
refresh. -/
def Role.code : Role → ℕ
  | .cursor => 0
  | .shrink => 1
  | .refresh => 2

theorem Role.code_le_two (r : Role) : r.code ≤ 2 := by cases r <;> decide

theorem Role.word_injective (w : ℕ) (fit : 2 < 2 ^ w) :
    Function.Injective (fun r : Role => (r.code : Word w)) := by
  intro r t h
  have hr := r.code_le_two.trans_lt fit
  have ht := t.code_le_two.trans_lt fit
  have eq := congrArg Fin.val h
  simp only [Fin.val_natCast, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt ht] at eq
  cases r <;> cases t <;> simp_all [Role.code]

/-- Row identifiers and the visit operation for one layer. -/
structure TaggedLayer where
  /-- The selected DFS layer of site rows and their child ordinals. -/
  layer : Layer
  /-- Producing role used to dispatch visits to the rows of this tagged layer. -/
  role : Role

/-- Header bases in the tag table use the exact prefix of selected output sizes. -/
def layerBase (cap base : ℕ) (ls : List TaggedLayer) (i : ℕ) : ℕ :=
  base + words cap ((ls.take i).map TaggedLayer.layer)

theorem layerBase_zero (cap base : ℕ) (ls : List TaggedLayer) : layerBase cap base ls 0 = base := by
  simp [layerBase, words]

theorem layerBase_cons (cap base : ℕ) (L : TaggedLayer) (ls : List TaggedLayer) (i : ℕ) :
    layerBase cap base (L :: ls) (i + 1) = layerBase cap (endPos cap base L.layer) ls i := by
  simp [layerBase, words, endPos, address, Nat.mul_add, Nat.add_assoc]

/-- Tags live at a fixed public offset from descriptor headers. -/
def Reads (w : ℕ) (m : Memory w) (offset cap base : ℕ) : List TaggedLayer → Prop
  | [] => True
  | L :: ls => (∀ i : Fin L.layer.count,
      m (offset + address cap base i.val) = (L.role.code : Word w)) ∧
    Reads w m offset cap (endPos cap base L.layer) ls

theorem Reads.at_layer {w : ℕ} {m : Memory w} {offset cap base : ℕ} {ls : List TaggedLayer}
    (h : Reads w m offset cap base ls) (i : Fin ls.length) (j : Fin (ls[i].layer.count)) :
    m (offset + address cap (layerBase cap base ls i.val) j.val) = (ls[i].role.code : Word w) := by
  induction ls generalizing base with
  | nil => exact Fin.elim0 i
  | cons L ls ih =>
    cases i using Fin.cases with
    | zero =>
      simpa only [Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero, layerBase_zero] using h.1 j
    | succ i =>
      simpa only [Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ, layerBase_cons] using
        (ih h.2 i j)

variable {k R : Type*} [Field k] [CommRing R] {S : BlockSchedule k}
variable {B : S.Templates} {f : B.Entry → R} {hf : B.IsSolution f}

/-- Pattern-match on the actual scheduled pass, including its input state and
proof that it is the corresponding shrinking or refresh operation. -/
def ofOrigin {a g b n : ℕ} {X : State a g} {p : StatePass R X b n} :
    PassOrigin B f hf p → Role
  | .shrink _ _ _ => .shrink
  | .refresh _ => .refresh

variable (B f hf)

/-- Recover a selected output layer's role from the origin of its elementary compression pass. -/
def tagLevel (v : SelectedLevel B f hf) : Role := ofOrigin v.origin

variable {n : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices)

/-- One tag per physical layer. The initial layer is the cursor. Subsequent
layers are indexed by the real, branch-specific `SelectedLevel` records. -/
noncomputable def selected : List TaggedLayer :=
  ⟨leafLayer (siteOrder X), .cursor⟩ :: (executeLevels B f hf T hT X z).map
    (fun v => ⟨levelLayer B f hf v, tagLevel B f hf v⟩)

/-- Dropping just the tag gives precisely the layers consumed by the selected
parsers, including every old-site identifier in the order of the true fiber. -/
theorem selected_layers : (selected B f hf T hT X z).map TaggedLayer.layer =
    selectedLayers B f hf T hT X z := by
  simp only [selectedLayers_eq_levels, selected, List.map_cons, List.map_map, Function.comp_def]

/-- Reading a concrete output tag routes to the selected shrink or refresh pass
that supplied that position's kernel reader. -/
theorem reads_selected_level {w : ℕ} (m : Memory w) (offset base : ℕ)
    (hr : Reads w m offset B.recordLimit base (selected B f hf T hT X z))
    (i : Fin (executeLevels B f hf T hT X z).length)
    (j : Fin ((executeLevels B f hf T hT X z)[i].outputSites)) :
    m (offset + address B.recordLimit (layerBase B.recordLimit base (selected B f hf T hT X z)
      (i.val + 1)) j.val) =
      ((tagLevel B f hf (executeLevels B f hf T hT X z)[i]).code : Word w) := by
  let stage : Fin (selected B f hf T hT X z).length := ⟨i.val + 1, by simp [selected]⟩
  have count : ((selected B f hf T hT X z)[stage]).layer.count =
      ((executeLevels B f hf T hT X z)[i]).outputSites := by
    simp [stage, selected, levelLayer_count]
  let row : Fin (selected B f hf T hT X z)[stage].layer.count :=
    ⟨j.val, by rw [count]; exact j.isLt⟩
  have h := Reads.at_layer (base := base) (h := hr) stage row
  simpa [row, stage, selected] using h

/-- The cursor leaves always select the initial-vertex reader. -/
theorem reads_cursor {w : ℕ} (m : Memory w) (offset base : ℕ)
    (hr : Reads w m offset B.recordLimit base (selected B f hf T hT X z)) (v : X.network.Site) :
    m (offset + (sitePointers B.recordLimit base (siteOrder X) v).1) = 0 :=
  hr.1 ((siteOrder X).entries.symm v)

end PairSimulation.TraversalRoles

end VPVNP
end Computability
end OAI
