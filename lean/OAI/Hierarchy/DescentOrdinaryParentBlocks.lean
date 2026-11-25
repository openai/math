import OAI.Hierarchy.DescentParallelBase
import OAI.Hierarchy.DescentRawCableRoster
import OAI.Hierarchy.DescentOrdinarySiblingSerial

namespace OAI
/-! # Actual retained ordinary parents partition the new network’s grain tape -/
namespace Hierarchy.DescentOrdinaryParentTape
open DescentPacking
noncomputable section
set_option quotPrecheck false

variable {E : Type} {n : ℕ} (weight : E → ℕ)
variable (stream : (Σ u, Fin (weight u)) → Fin n)

/-- First time in a parent's fiber, or zero for an empty fiber. -/
def first (u : E) : ℕ :=
  if live : 0 < weight u then (stream ⟨u, ⟨0, live⟩⟩).val else 0

theorem block_time
    (step : ∀ (u : E) (j t : Fin (weight u)), t.val = j.val + 1 →
      (stream ⟨u, t⟩).val = (stream ⟨u, j⟩).val + 1)
    (u : E) (j : Fin (weight u)) :
    (stream ⟨u, j⟩).val = first weight stream u + j.val := by
  obtain ⟨m, limit⟩ := j
  induction m with
  | zero => simp [first, limit]
  | succ m ih =>
    let a : Fin (weight u) := ⟨m, Nat.lt_of_succ_lt limit⟩
    exact (step u a ⟨m + 1, limit⟩ rfl).trans (congrArg Nat.succ (ih a.isLt))

variable {D : Type} [Fintype D] (width : D → ℕ) (rank : D ↪ ℕ)
local notation "ordered" => orderedUnits width rank rank.injective

/-- A singleton fiber followed immediately by another fiber has adjacent heads. -/
theorem adjacent_heads (x y : D) (one : width x = 1) (live : 0 < width y)
    (order : ∀ a, rank a < rank y ↔ rank a < rank x ∨ a = x) :
    (ordered ⟨y, ⟨0, live⟩⟩).val = (ordered ⟨x, ⟨0, by omega⟩⟩).val + 1 := by
  simp only [orderedUnits_val, Nat.add_zero]
  rw [DescentSharedCableNames.Siblings.prefix_next width rank x y order, one]

/-- Successive offsets in a single fiber have successive stream times. -/
theorem adjacent_within (x : D) (j t : Fin (width x)) (step : t.val = j.val + 1) :
    (ordered ⟨x, t⟩).val = (ordered ⟨x, j⟩).val + 1 := by
  simp only [orderedUnits_val, step, Nat.add_assoc]

/-- The two occupied fiber heads appear in exactly the order of their ranks. -/
theorem head_before (x y : Σ d, Fin (width d)) (zx : x.2.val = 0) (zy : y.2.val = 0) :
    (ordered x).val < (ordered y).val ↔ rank x.1 < rank y.1 := by
  obtain ⟨a, i⟩ := x
  obtain ⟨b, j⟩ := y
  change i.val = 0 at zx
  change j.val = 0 at zy
  change (ordered ⟨a, i⟩).val < (ordered ⟨b, j⟩).val ↔ rank a < rank b
  simp only [orderedUnits_val, zx, zy, Nat.add_zero]
  rcases lt_trichotomy (rank a) (rank b) with lt | eqn | gt
  · have disjoint := ProtocolRAMPortRanks.prefix_disjoint width rank lt
    have live : 0 < width a := Nat.zero_lt_of_lt i.isLt
    omega
  · have same := rank.injective eqn
    rw [same]
    simp
  · have disjoint := ProtocolRAMPortRanks.prefix_disjoint width rank gt
    have live : 0 < width b := Nat.zero_lt_of_lt j.isLt
    omega

/-- Given zero-offset emitted heads, first times compare by emitted edge ranks. -/
theorem first_before (emit : (Σ u, Fin (weight u)) → (Σ d, Fin (width d)))
    (u v : E) (up : 0 < weight u) (vp : 0 < weight v)
    (zu : (emit ⟨u, ⟨0, up⟩⟩).2.val = 0)
    (zv : (emit ⟨v, ⟨0, vp⟩⟩).2.val = 0) :
    first weight (fun t => ordered (emit t)) u < first weight (fun t => ordered (emit t)) v ↔
      rank (emit ⟨u, ⟨0, up⟩⟩).1 < rank (emit ⟨v, ⟨0, vp⟩⟩).1 := by
  simpa only [first, dite_eq_left up, dite_eq_left vp] using
    (head_before width rank (emit ⟨u, ⟨0, up⟩⟩) (emit ⟨v, ⟨0, vp⟩⟩) zu zv)

end
end Hierarchy.DescentOrdinaryParentTape

namespace Hierarchy.DescentOrdinaryParentBlocks
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentPhysicalOrder
open DescentHostDirectory DescentColonies DescentStageEdgeReceipt DescentPacking DescentCableDonorNames
open DescentSharedCableNames DescentSharedCableNames.Siblings DescentOrdinarySiblingSerial DescentParallelBase
open private DescentOrdinarySiblingSerial.physicalBase DescentOrdinarySiblingSerial.physicalKey
  from OAI.Hierarchy.DescentOrdinarySiblingSerial
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option Elab.async false

private theorem renamed_order {E : Type} [Fintype E] (rank : E ↪ ℕ) (x y : E) :
    originalId E (rename rank x) < originalId E (rename rank y) ↔ rank x < rank y := by
  change (Fintype.equivFin E (rename rank x)).val < (Fintype.equivFin E (rename rank y)).val ↔ _
  rw [code_rename,code_rename]
  exact physical_lt_iff rank x y


namespace Fibers

variable {E Z : Type} (marked : E → Prop) (copies : E → ℕ)

abbrev Raw := {u : E // ¬marked u} ⊕ (Σ u : {u : E // marked u}, Fin (copies u.val))

def original : Raw marked copies → E
  | .inl u => u.val
  | .inr v => v.1.val

def offset : Raw marked copies → ℕ
  | .inl _ => 0
  | .inr v => v.2.val

variable [DecidablePred marked] (name : Raw marked copies ≃ Z) (count : Z → ℕ)

def weight (u : E) : ℕ :=
  if h : marked u then copies u else count (name (.inl ⟨u,h⟩))

local notation "wgt" => weight marked copies name count

def copyIndex (u : E) (h : marked u) (j : Fin (wgt u)) : Fin (copies u) :=
  ⟨j.val, by simpa only [weight, dite_eq_left h] using j.isLt⟩

def freeIndex (u : E) (h : ¬marked u) (j : Fin (wgt u)) :
    Fin (count (name (.inl ⟨u,h⟩))) :=
  ⟨j.val, by simpa only [weight, dite_eq_right h] using j.isLt⟩

variable (one : ∀ (u : {u : E // marked u}) (j : Fin (copies u.val)),
  count (name (.inr ⟨u,j⟩)) = 1)

def emit (a : Σ u : E, Fin (wgt u)) : Σ z : Z, Fin (count z) :=
  if h : marked a.1 then
    let u : {u : E // marked u} := ⟨a.1,h⟩
    let i := copyIndex marked copies name count a.1 h a.2
    ⟨name (.inr ⟨u,i⟩), ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one (one u i).ge⟩⟩
  else
    ⟨name (.inl ⟨a.1,h⟩), freeIndex marked copies name count a.1 h a.2⟩

local notation "send" => emit marked copies name count one

theorem emit_marked (u : E) (h : marked u) (j : Fin (wgt u)) :
    let i := copyIndex marked copies name count u h j
    send ⟨u,j⟩ = ⟨name (.inr ⟨⟨u,h⟩,i⟩),
      ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one (one ⟨u,h⟩ i).ge⟩⟩ := by
  simp only [emit, dite_eq_left h]

theorem emit_free (u : E) (h : ¬marked u) (j : Fin (wgt u)) :
    send ⟨u,j⟩ = ⟨name (.inl ⟨u,h⟩), freeIndex marked copies name count u h j⟩ := by
  simp only [emit, dite_eq_right h]

theorem within (u : E) (j : Fin (wgt u)) :
    (send ⟨u,j⟩).2.val = if marked u then 0 else j.val := by
  by_cases h : marked u
  · exact (congrArg (fun r : Σ z : Z, Fin (count z) => r.2.val)
      (emit_marked marked copies name count one u h j)).trans (ite_eq_left h).symm
  · exact (congrArg (fun r : Σ z : Z, Fin (count z) => r.2.val)
      (emit_free marked copies name count one u h j)).trans (ite_eq_right h).symm

def firstGrain (u : E) (j : Fin (wgt u)) : Fin (wgt u) :=
  if marked u then j else ⟨0, Nat.zero_lt_of_lt j.isLt⟩

theorem first_of_edge (u : E) (j : Fin (wgt u)) :
    send ⟨u,firstGrain marked copies name count u j⟩ =
      ⟨(send ⟨u,j⟩).1, ⟨0,Nat.zero_lt_of_lt (send ⟨u,j⟩).2.isLt⟩⟩ := by
  let grain := firstGrain marked copies name count u j
  have site : (send ⟨u, grain⟩).1 = (send ⟨u, j⟩).1 := by
    by_cases h : marked u
    · have same : grain = j := ite_eq_left h
      rw [same]
    · exact (congrArg Sigma.fst (emit_free marked copies name count one u h grain)).trans
        (congrArg Sigma.fst (emit_free marked copies name count one u h j)).symm
  have zero : (send ⟨u, grain⟩).2.val = 0 := by
    let index := fun x : Σ z : Z, Fin (count z) => x.2.val
    by_cases h : marked u
    · exact congrArg index (emit_marked marked copies name count one u h grain)
    · exact (congrArg index (emit_free marked copies name count one u h grain)).trans
        (show grain.val = 0 by simp only [grain, firstGrain, ite_eq_right h])
  exact Sigma.ext site ((Fin.heq_ext_iff (congrArg count site)).2 zero)

def recover (a : Σ z : Z, Fin (count z)) : E × ℕ :=
  match name.symm a.1 with
  | .inl u => (u.val,a.2.val)
  | .inr v => (v.1.val,v.2.val)

theorem recover_emit (a : Σ u : E, Fin (wgt u)) :
    recover marked copies name count (send a) = (a.1,a.2.val) := by
  obtain ⟨u,j⟩ := a
  by_cases h : marked u
  · rw [emit_marked marked copies name count one u h j]
    simp only [recover, Equiv.symm_apply_apply, copyIndex]
  · rw [emit_free marked copies name count one u h j]
    simp only [recover, Equiv.symm_apply_apply, freeIndex]

theorem parent_emit (u : E) (j : Fin (wgt u)) :
    original marked copies (name.symm (send ⟨u,j⟩).1) = u := by
  by_cases h : marked u <;> simp [emit, original, h]

theorem offset_zero (u : E) (live : 0 < wgt u) :
    offset marked copies (name.symm (send ⟨u,⟨0,live⟩⟩).1) = 0 := by
  by_cases h : marked u <;> simp [emit, copyIndex, offset, h]

def units : (Σ u : E, Fin (wgt u)) ≃ (Σ z : Z, Fin (count z)) :=
  Equiv.ofBijective send (by
    constructor
    · intro x y eqn
      have same := congrArg (recover marked copies name count) eqn
      simp only [recover_emit] at same
      have parent := congrArg Prod.fst same
      exact Sigma.ext parent
        ((Fin.heq_ext_iff (congrArg wgt parent)).mpr (congrArg Prod.snd same))
    · rintro ⟨z,j⟩
      obtain ⟨r,rfl⟩ := name.surjective z
      rcases r with u | ⟨u,k⟩
      · let i : Fin (wgt u.val) := ⟨j.val, by
          simpa only [weight, dite_eq_right u.property] using j.isLt⟩
        refine ⟨⟨u.val,i⟩,?_⟩
        simp only [emit, dite_eq_right u.property, freeIndex, i]
      · let i : Fin (wgt u.val) := ⟨k.val, by
          simpa only [weight, dite_eq_left u.property] using k.isLt⟩
        have bound : j.val < 1 := lt_of_lt_of_eq j.isLt (one u k)
        have zero : j.val = 0 := by omega
        have atZero : j = ⟨0,Nat.lt_of_lt_of_le Nat.zero_lt_one (one u k).ge⟩ := Fin.ext zero
        subst j
        refine ⟨⟨u.val,i⟩,?_⟩
        simp only [emit, dite_eq_left u.property, copyIndex, i])

end Fibers

namespace Fibers
open DescentPacking
open scoped Classical
noncomputable section

/-- Consecutive copies of a marked parent occupy consecutive singleton fibers.
An unmarked parent's consecutive grains occupy consecutive offsets of one fiber. -/
theorem time_next {E Z : Type} [finiteZ : Fintype Z]
    (marked : E → Prop) [DecidablePred marked] (copies : E → ℕ) (name : Raw marked copies ≃ Z)
    (count : Z → ℕ)
    (one : ∀ (p : {u : E // marked u}) (i : Fin (copies p.1)),
      count (name (.inr ⟨p, i⟩)) = 1)
    (raw : Raw marked copies ↪ ℕ) (rank : Z ↪ ℕ)
    (names : ∀ x y, rank (name x) < rank (name y) ↔ raw x < raw y)
    (gap : ∀ (p : {u : E // marked u}) (a b : Fin (copies p.1)),
      b.val = a.val + 1 → raw (.inr ⟨p, b⟩) = raw (.inr ⟨p, a⟩) + 1)
    (u : E) (j t : Fin (weight marked copies name count u)) (step : t.val = j.val + 1) :
    ((@orderedUnits Z finiteZ count rank rank.injective)
      (emit marked copies name count one ⟨u, t⟩)).val =
      ((@orderedUnits Z finiteZ count rank rank.injective)
        (emit marked copies name count one ⟨u, j⟩)).val + 1 := by
  by_cases h : marked u
  · let p : {v : E // marked v} := ⟨u, h⟩
    let a := copyIndex marked copies name count u h j
    let b := copyIndex marked copies name count u h t
    let : Fintype (Raw marked copies) := Fintype.ofEquiv Z name.symm
    have order := DescentSharedCableNames.Siblings.before name raw rank names (gap p a b step)
    rw [emit_marked marked copies name count one u h t, emit_marked marked copies name count one u h j]
    exact DescentOrdinaryParentTape.adjacent_heads count rank
      (name (.inr ⟨p, a⟩)) (name (.inr ⟨p, b⟩)) (one p a)
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (one p b).ge) order
  · rw [emit_free marked copies name count one u h t, emit_free marked copies name count one u h j]
    exact DescentOrdinaryParentTape.adjacent_within count rank _ _ _ step

end
end Fibers

namespace Endpoints

variable {F P : Type} [Field F] {d : ℕ} {bits : P → ℕ}
variable (M : MarkedWorld F d P bits) (q : ℕ) (copies : M.graph.Edge → ℕ)
variable (cut : ∀ u ∈ M.core, M.graph.width u = copies u * q)
local notation "splitWorld" => M.pieces q copies cut
local notation "markedEdge" => (fun u : M.graph.Edge => u ∈ M.core)

omit [Field F] in
/-- A split edge retains both endpoints of its original edge. -/
theorem head_ends (e : (splitWorld).graph.Edge) (u : M.graph.Edge)
    (parent : Fibers.original markedEdge copies e = u) :
    (splitWorld).graph.src e = M.graph.src u ∧ (splitWorld).graph.dst e = M.graph.dst u := by
  have same : DescentCableUnbundling.original M.graph M.core copies e = u := by
    rcases e with ⟨v,hv⟩ | ⟨⟨v,hv⟩,j⟩ <;> exact parent
  exact ⟨congrArg M.graph.src same, congrArg M.graph.dst same⟩

omit [Field F] in
/-- The physical tape records the piece index on a marked edge and zero on a tether. -/
theorem piece_offset (e : (splitWorld).graph.Edge) :
    (DescentCableUnbundling.pieceUnit M.graph M.core copies q e).2.val =
      Fibers.offset markedEdge copies e := by
  rcases e with ⟨u,hu⟩ | ⟨⟨u,hu⟩,j⟩ <;> rfl

variable (site : M.graph.Site ↪ ℕ) (raw : (M.pieces q copies cut).graph.Edge ↪ ℕ)
local notation "rankWorld" => PhysicalRename.rankedWorld splitWorld site raw
local notation "siteName" => @rename (splitWorld).graph.Site (splitWorld).graph.finiteSite site
local notation "edgeName" => @rename (splitWorld).graph.Edge (splitWorld).graph.finiteEdge raw
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {stage : ℕ} {price ε : ℝ} {G : PoweredGadget F}
variable (A : GroupStage (PhysicalRename.rankedWorld (M.pieces q copies cut) site raw) G price ε J V stage)

/-- The raw edge underlying any occupied grain has positive physical width. -/
theorem head_width {i : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (a : Stage.Grain A) : 0 < (splitWorld).graph.width ((edgeName).symm a.1) := by
  change 0 < (rankWorld).graph.width a.1
  rw [A.grainCount_fit S ready a.1]
  exact Nat.mul_pos (Nat.zero_lt_of_lt a.2.isLt) (Nat.mul_pos A.unitPos G.base_pos)

/-- Looking up an occupied grain in the stream returns the hosts of its original endpoints. -/
theorem stream_ends (order : (rankWorld).graph.Edge ↪ ℕ) (a : Stage.Grain A) (u : M.graph.Edge)
    (parent : Fibers.original markedEdge copies ((edgeName).symm a.1) = u) :
    (Stage.source A order).src (Stage.stream A order a) = Stage.home A (siteName (M.graph.src u)) ∧
    (Stage.source A order).dst (Stage.stream A order a) = Stage.home A (siteName (M.graph.dst u)) := by
  have ends := head_ends M q copies cut ((edgeName).symm a.1) u parent
  simp only [Stage.source, Equiv.symm_apply_apply]
  exact ⟨congrArg (fun v => Stage.home A (siteName v)) ends.1,
    congrArg (fun v => Stage.home A (siteName v)) ends.2⟩

end Endpoints

namespace Mount

variable {F P : Type} [Field F] {d : ℕ} {bits : P → ℕ}
variable (M : MarkedWorld F d P bits) (q : ℕ) (copies : M.graph.Edge → ℕ)
variable (cut : ∀ u ∈ M.core, M.graph.width u = copies u * q)
local notation "marks" => (fun u : M.graph.Edge => u ∈ M.core)
local notation "splitBoard" => M.pieces q copies cut
variable (site : M.graph.Site ↪ ℕ) (raw : (M.pieces q copies cut).graph.Edge ↪ ℕ)
local notation "siteName" => @rename (splitBoard).graph.Site (splitBoard).graph.finiteSite site
local notation "edgeName" => @rename (splitBoard).graph.Edge (splitBoard).graph.finiteEdge raw
local notation "board" => PhysicalRename.rankedWorld splitBoard site raw
local notation "nativeRank" => @originalId (board).graph.Edge (board).graph.finiteEdge

private def naming : Fibers.Raw marks copies ≃ (board).graph.Edge := edgeName
local notation "nm" => naming M q copies cut site raw

variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {stage : ℕ} {price ε : ℝ} {G : PoweredGadget F}
variable (A : GroupStage (PhysicalRename.rankedWorld (M.pieces q copies cut) site raw) G price ε J V stage)

omit [Field F] in
private theorem original_eq (r : Fibers.Raw marks copies) :
    DescentCableUnbundling.original M.graph M.core copies r = Fibers.original marks copies r := by
  rcases r with a | ⟨a,j⟩ <;> rfl

omit [Field F] in
private theorem named_mem (e : (board).graph.Edge) :
    e ∈ (board).core ↔ Fibers.original marks copies ((nm).symm e) ∈ M.core := by
  obtain ⟨r, rfl⟩ := (nm).surjective e
  rw [Equiv.symm_apply_apply, ← original_eq M copies r]
  exact (PhysicalRename.core_mem splitBoard siteName edgeName r).trans
    (DescentCableUnbundling.mem_nextCore M.graph M.core copies q r)

private theorem single (u : {a : M.graph.Edge // marks a}) (j : Fin (copies u.1)) :
    A.grainCount (nm (Sum.inr ⟨u,j⟩)) = 1 := by
  apply Siblings.paid_one A
  apply (PhysicalRename.core_mem splitBoard siteName edgeName _).2
  exact (DescentCableUnbundling.mem_nextCore M.graph M.core copies q (Sum.inr ⟨u,j⟩)).2 u.property

local notation "oneGrain" => single M q copies cut site raw A
local notation "wgt" => Fibers.weight marks copies nm A.grainCount
local notation "go" => Fibers.emit marks copies nm A.grainCount oneGrain
local notation "nativeStream" => Stage.stream A nativeRank
local notation "headTime" => DescentOrdinaryParentTape.first wgt (fun t => nativeStream (go t))
private def weight : M.graph.Edge → ℕ := wgt
private def emit : (Σ u : M.graph.Edge, Fin (wgt u)) → Stage.Grain A := go
private def firstGrain (u : M.graph.Edge) (j : Fin (wgt u)) : Fin (wgt u) :=
  Fibers.firstGrain marks copies nm A.grainCount u j
private def recover (r : Stage.Grain A) : M.graph.Edge × ℕ := Fibers.recover marks copies nm A.grainCount r
private def units : (Σ u : M.graph.Edge, Fin (wgt u)) ≃ Stage.Grain A := Fibers.units marks copies nm A.grainCount oneGrain
private def timeAt (u : M.graph.Edge) (j : Fin (wgt u)) : ℕ := (nativeStream (go ⟨u,j⟩)).val
private def first (u : M.graph.Edge) : ℕ := headTime u
private def head (u : M.graph.Edge) (live : 0 < wgt u) : (splitBoard).graph.Edge := (nm).symm (go ⟨u,⟨0,live⟩⟩).1

private theorem weight_width {i : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (grain : A.z * G.b = q) (u : M.graph.Edge) : wgt u * q = M.graph.width u := by
  by_cases yes : marks u
  · rw [Fibers.weight, dite_eq_left yes]
    exact (cut u yes).symm
  · rw [Fibers.weight, dite_eq_right yes]
    let r : Fibers.Raw marks copies := Sum.inl ⟨u,yes⟩
    have h := A.grainCount_fit S ready (nm r)
    rw [grain] at h
    have width : (board).graph.width (nm r) = M.graph.width u :=
      PhysicalRename.width (splitBoard).graph siteName edgeName r
    exact h.symm.trans width

private theorem weight_eq {i : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (grain : A.z * G.b = q) (qp : 0 < q) (u : M.graph.Edge) (stated : ℕ)
    (physical : stated*q=M.graph.width u) : wgt u=stated :=
  Nat.eq_of_mul_eq_mul_right qp ((weight_width M q copies cut site raw A S ready grain u).trans physical.symm)

private theorem within_at (u : M.graph.Edge) (j : Fin (wgt u)) :
    (go ⟨u,j⟩).2.val = (if marks u then 0 else j.val) :=
  Fibers.within marks copies nm A.grainCount oneGrain u j
private theorem core_at (u : M.graph.Edge) (j : Fin (wgt u)) : (go ⟨u,j⟩).1 ∈ (board).core ↔ marks u := by
  rw [named_mem M q copies cut site raw, Fibers.parent_emit marks copies nm A.grainCount oneGrain u j]
private theorem first_of_edge (u : M.graph.Edge) (j : Fin (wgt u)) :
    go ⟨u,firstGrain M q copies cut site raw A u j⟩ =
      ⟨(go ⟨u,j⟩).1,⟨0,Nat.zero_lt_of_lt (go ⟨u,j⟩).2.isLt⟩⟩ :=
  Fibers.first_of_edge marks copies nm A.grainCount oneGrain u j
private theorem recover_emit (e : Σ u : M.graph.Edge, Fin (wgt u)) :
    recover M q copies cut site raw A (go e) = (e.1,e.2.val) :=
  Fibers.recover_emit marks copies nm A.grainCount oneGrain e

private theorem head_zero (u : M.graph.Edge) (live : 0 < wgt u) : (go ⟨u,⟨0,live⟩⟩).2.val = 0 := by
  rw [within_at M q copies cut site raw A]
  simp

private theorem first_before (u v : M.graph.Edge) (up : 0 < wgt u) (vp : 0 < wgt v) :
    headTime u < headTime v ↔ raw ((nm).symm (go ⟨u,⟨0,up⟩⟩).1) < raw ((nm).symm (go ⟨v,⟨0,vp⟩⟩).1) := by
  have h := DescentOrdinaryParentTape.first_before wgt A.grainCount nativeRank go u v up vp
    (head_zero M q copies cut site raw A u up) (head_zero M q copies cut site raw A v vp)
  apply h.trans
  have names := @renamed_order (splitBoard).graph.Edge (splitBoard).graph.finiteEdge raw
  let x := (go ⟨u,⟨0,up⟩⟩).1
  let y := (go ⟨v,⟨0,vp⟩⟩).1
  have pair := names ((nm).symm x) ((nm).symm y)
  change nativeRank (nm ((nm).symm x)) < nativeRank (nm ((nm).symm y)) ↔ _ at pair
  simpa only [Equiv.apply_symm_apply] using pair

private def Gaps : Prop := ∀ (u : {e : M.graph.Edge // marks e}) (a b : Fin (copies u.1)),
  b.val=a.val+1 → raw (Sum.inr ⟨u,b⟩)=raw (Sum.inr ⟨u,a⟩)+1
private theorem block_time (gap : Gaps M q copies cut raw) (u : M.graph.Edge) (j : Fin (wgt u)) :
    (nativeStream (go ⟨u,j⟩)).val = headTime u + j.val :=
  DescentOrdinaryParentTape.block_time wgt (fun t => nativeStream (go t))
    (Fibers.time_next marks copies nm A.grainCount oneGrain raw nativeRank
      (@renamed_order (splitBoard).graph.Edge (splitBoard).graph.finiteEdge raw) gap) u j

private theorem head_ends (u : M.graph.Edge) (live : 0 < wgt u) :
    (splitBoard).graph.src (head M q copies cut site raw A u live)=M.graph.src u ∧
    (splitBoard).graph.dst (head M q copies cut site raw A u live)=M.graph.dst u :=
  Endpoints.head_ends M q copies cut _ u (Fibers.parent_emit marks copies nm A.grainCount oneGrain u ⟨0,live⟩)

private theorem head_width {i : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (u : M.graph.Edge) (live : 0 < wgt u) : 0 < (splitBoard).graph.width (head M q copies cut site raw A u live) :=
  Endpoints.head_width M q copies cut site raw A S ready (go ⟨u,⟨0,live⟩⟩)

private theorem head_owner (u : M.graph.Edge) (live : 0 < wgt u) :
    (DescentCableUnbundling.pieceUnit M.graph M.core copies q (head M q copies cut site raw A u live)).1=u := by
  have owner (r : (splitBoard).graph.Edge) :
      (DescentCableUnbundling.pieceUnit M.graph M.core copies q r).1 = Fibers.original marks copies r := by
    rcases r with ⟨a,ha⟩ | ⟨⟨a,ha⟩,j⟩ <;> rfl
  exact (owner _).trans (Fibers.parent_emit marks copies nm A.grainCount oneGrain u ⟨0,live⟩)

private theorem head_offset (u : M.graph.Edge) (live : 0 < wgt u) :
    (DescentCableUnbundling.pieceUnit M.graph M.core copies q (head M q copies cut site raw A u live)).2.val=0 :=
  (Endpoints.piece_offset M q copies cut _).trans (Fibers.offset_zero marks copies nm A.grainCount oneGrain u live)

private def blocks (gap : Gaps M q copies cut raw) : Blocks (Stage.source A nativeRank) M.graph.Edge where
  count := wgt
  first := headTime
  src u := Stage.home A (siteName (M.graph.src u))
  dst u := Stage.home A (siteName (M.graph.dst u))
  order := (Fibers.units marks copies nm A.grainCount oneGrain).trans nativeStream
  consecutive := block_time M q copies cut site raw A gap
  atSource u j := (Endpoints.stream_ends M q copies cut site raw A nativeRank (go ⟨u,j⟩) u
    (Fibers.parent_emit marks copies nm A.grainCount oneGrain u j)).1
  atTarget u j := (Endpoints.stream_ends M q copies cut site raw A nativeRank (go ⟨u,j⟩) u
    (Fibers.parent_emit marks copies nm A.grainCount oneGrain u j)).2

end Mount

private def liveParents {H E R : Type} {n : ℕ} {B : DescentSharedCableNames.Ends H n}
    (C : Blocks B E) (home : H) (parent : E ↪ R)
    (width units : R → ℕ) (q : ℕ) (qp : 0 < q)
    (measure : ∀ e, C.count e * q = width (parent e))
    (omitted : ∀ r, ¬0 < units r → width r = 0) :
    Local C home ↪ {r : R // 0 < units r} where
  toFun e := ⟨parent e.val, by
    by_contra h
    exact (Nat.mul_pos e.property.1 qp).ne'
      ((measure e.val).trans (omitted (parent e.val) h))⟩
  inj' := fun _ _ eqn => Subtype.ext (parent.injective (congrArg Subtype.val eqn))


variable {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
local notation "sel" => W.selected G pick z hz fit pack p
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g q : ℕ)
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
local notation "coarse" => coalesced sel key flag k g
local notation "rep" => repetitions W G pick z hz fit pack p key flag k g q
local notation "world" => DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected
local notation "tape" => ordinary W G edge pair pick z hz fit pack p key flag k g q old picked affected
variable (site : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site ↪ ℕ)
local notation "sparse" => DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site
local notation "next" => PhysicalRename.rankedWorld world site sparse
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {stage : ℕ} {price ε : ℝ}
variable (A : GroupStage
    (PhysicalRename.rankedWorld
      (DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
      (DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site))
    G price ε J V stage)

local notation "cutWidth" => repetition_width W G pick z hz fit pack p key flag k g q old picked affected
local notation "adjacentKey" => DescentOrdinarySiblingSerial.key_next W G edge pair pick z hz fit pack p key flag k g q old picked affected site
/-- A marked parent has one finer grain per normalized cable. An unmarked
tether keeps all of its finer grains on its single physical child. -/
def weight (u : (coarse).graph.Edge) : ℕ :=
  Mount.weight coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A u
local notation "wt" => weight W G edge pair pick z hz fit pack p key flag k g q old picked affected site A

/-- The physical multiplicity is exactly the number of paid next-stage
grains of its surviving raw parent, on both marked and unmarked roles. -/
theorem weight_width {i : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (grain : A.z*G.b=q) (u : (coarse).graph.Edge) : wt u*q=(coarse).graph.width u :=
  Mount.weight_width coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A S ready grain u

theorem weight_eq {i : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (grain : A.z*G.b=q) (qp:0<q) (u : (coarse).graph.Edge) (stated : ℕ) (physical : stated*q=(coarse).graph.width u) :
    wt u=stated :=
  Mount.weight_eq coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A S ready grain qp u stated physical

def emit : (Σ u : (coarse).graph.Edge, Fin (wt u))→Stage.Grain A :=
  Mount.emit coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A
local notation "grains" => emit W G edge pair pick z hz fit pack p key flag k g q old picked affected site A

theorem within_at (u : (coarse).graph.Edge) (j : Fin (wt u)) :
    (grains ⟨u,j⟩).2.val=(if u∈(coarse).core then 0 else j.val) :=
  Mount.within_at coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A u j

theorem core_at (u : (coarse).graph.Edge) (j : Fin (wt u)) : (grains ⟨u,j⟩).1∈(next).core ↔ u∈(coarse).core :=
  Mount.core_at coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A u j

def firstGrain (u : (coarse).graph.Edge) (j : Fin (wt u)) : Fin (wt u) :=
  if u ∈ (coarse).core then j else ⟨0,Nat.zero_lt_of_lt j.isLt⟩

theorem first_of_edge (u : (coarse).graph.Edge) (j : Fin (wt u)) :
    grains ⟨u,firstGrain W G edge pair pick z hz fit pack p key flag k g q old picked affected site A u j⟩=
      ⟨(grains ⟨u,j⟩).1,⟨0,Nat.zero_lt_of_lt (grains ⟨u,j⟩).2.isLt⟩⟩ :=
  Mount.first_of_edge coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A u j

def recover (row : Stage.Grain A) : (coarse).graph.Edge × ℕ :=
  Mount.recover coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A row
local notation "get" => recover W G edge pair pick z hz fit pack p key flag k g q old picked affected site A

theorem recover_emit (e : Σ u : (coarse).graph.Edge, Fin (wt u)) : get (grains e)=(e.1,e.2.val) :=
  Mount.recover_emit coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A e

def units : (Σ u : (coarse).graph.Edge, Fin (wt u))≃Stage.Grain A :=
  Mount.units coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A

def first (u : (coarse).graph.Edge) : ℕ :=
  Mount.first coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A u
local notation "base'" => DescentOrdinaryParentBlocks.first W G edge pair pick z hz fit pack p key flag k g q old picked affected site A

theorem block_time (qp : 0<q) (u : (coarse).graph.Edge) (j : Fin (wt u)) : Mount.timeAt coarse q rep cutWidth site sparse
      (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A u j = base' u + j.val :=
  Mount.block_time coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A (adjacentKey qp) u j

/-- The first surviving finer grain always occupies offset zero of its
actual physical child edge, for all cable roles. -/
theorem head_zero (u : (coarse).graph.Edge) (live:0<wt u) : (grains ⟨u,⟨0,live⟩⟩).2.val=0 :=
  Mount.head_zero coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A u live

def head (u : (coarse).graph.Edge) (live : 0<wt u) : (world).graph.Edge :=
  Mount.head coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A u live
local notation "firstEdge" => head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A

theorem head_ends (u : (coarse).graph.Edge) (live : 0<wt u) :
    (world).graph.src (firstEdge u live)=(coarse).graph.src u ∧ (world).graph.dst (firstEdge u live)=(coarse).graph.dst u :=
  Mount.head_ends coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A u live

theorem head_width {i : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (u : (coarse).graph.Edge) (live:0<wt u) : 0<(world).graph.width (firstEdge u live) :=
  Mount.head_width coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A S ready u live

/-- The tape owner of the first emitted grain is its original parent. -/
theorem head_owner (u : (coarse).graph.Edge) (live : 0<wt u) : (tape).owner (firstEdge u live)=u :=
  Mount.head_owner coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A u live

theorem head_offset (u : (coarse).graph.Edge) (live : 0<wt u) : (tape).offset (firstEdge u live)=0 :=
  Mount.head_offset coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A u live

/-- The emitted rank of the first actual physical child, expressed in the
old `Tape.sourceKey` order which `OrdinaryDonorOrder.compare` computes from
short donor-rack, original outgoing slot, eleven-way role, and offset. -/
theorem first_before (u v : (coarse).graph.Edge) (up : 0<wt u) (vp : 0<wt v) :
    base' u<base' v ↔ sparse (firstEdge u up)< sparse (firstEdge v vp) :=
  Mount.first_before coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A u v up vp

def blocks (qp : 0<q) :=
  Mount.blocks coarse q rep cutWidth site sparse
    (G := G) (J := J) (V := V) (stage := stage) (price := price) (ε := ε) A (adjacentKey qp)

/-- Use the authentic prior first-outgoing donor frame. `previous` is the
`omitted_width` law proved by the real prior-stage `grainCount_fit` for the
three actual GadgetNetwork edge cases. Zero-width parents have no slot. -/
def liveRaw {J₀ V₀ : Type} [Fintype J₀] [DecidableEq J₀] [Fintype V₀] [DecidableEq V₀] {age : ℕ}
    (oldA : GroupStage W G price ε J₀ V₀ age) {i : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (grain : A.z*G.b=q) (qp:0<q)
    (previous : ∀e:GadgetNetwork.Edge (I:=I) W.graph,¬0<oldA.grainCount (anchor pick e)→
      (GadgetNetwork.physical W.graph pick (branchWidth G z p)).width e=0) (h : Stage.Host J V stage) :
    Local (blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h ↪ DescentRawCablePanel.Live oldA pick := by
  let parent : (coarse).graph.Edge ↪ GadgetNetwork.Edge (I := I) W.graph :=
    ⟨fun e => e.val.val, fun _ _ eqn => Subtype.ext (Subtype.ext eqn)⟩
  exact liveParents (blocks W G edge pair pick z hz fit pack p key flag k g q
    old picked affected site A qp) h parent
    (GadgetNetwork.physical W.graph pick (branchWidth G z p)).width
    (fun r => oldA.grainCount (anchor pick r)) q qp
    (weight_width W G edge pair pick z hz fit pack p key flag k g q old picked
      affected site A S ready grain) previous

end
end Hierarchy.DescentOrdinaryParentBlocks

end OAI
