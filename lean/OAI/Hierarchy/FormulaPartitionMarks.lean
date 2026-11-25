import OAI.Hierarchy.FormulaPartitionThreshold
import OAI.Hierarchy.FormulaPartitionColor
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Finset.Max

namespace OAI
/-! # The first threshold crossings on a formula's heavy path -/

namespace Hierarchy.FormulaPartition

open scoped Classical

/-- The remaining slots at each gate of a heavy path. Addition steps are allowed
to keep all slots; multiplication steps retain at least half. -/
structure SlotWalk (V : Type) [Fintype V] (L : ℕ) where
  state : Fin (L+1) → Finset V
  start : state 0 = Finset.univ
  finish : (state (Fin.last L)).card = 1
  shrink : ∀ k : Fin L, state k.succ ⊆ state k.castSucc
  heavy : ∀ k : Fin L, (state k.castSucc).card ≤ 2*(state k.succ).card

namespace SlotWalk

variable {V : Type} [Fintype V] {L : ℕ} (W : SlotWalk V L)

local notation "d" => Fintype.card V
local notation "t" => Nat.log 2 d

theorem state_antitone : Antitone W.state := Fin.antitone_iff_succ_le.mpr W.shrink

include W in
theorem card_pos : 0<d := by
  have cap := Finset.card_le_univ (W.state (Fin.last L))
  rw [W.finish] at cap
  exact cap

private noncomputable def hits (j : Fin (t+1)) : Finset (Fin (L+1)) :=
  Finset.univ.filter fun k => (W.state k).card ≤ threshold d j.val

private theorem hits_nonempty (j : Fin (t+1)) : (W.hits j).Nonempty := by
  refine ⟨Fin.last L,?_⟩
  simp only [hits, Finset.mem_filter, Finset.mem_univ, true_and, W.finish]
  exact threshold_pos W.card_pos (by have := j.isLt; omega)

noncomputable def mark (j : Fin (t+1)) : Fin (L+1) := (W.hits j).min' (W.hits_nonempty j)

theorem mark_card (j : Fin (t+1)) : (W.state (W.mark j)).card ≤ threshold d j.val :=
  (Finset.mem_filter.mp (Finset.min'_mem (W.hits j) (W.hits_nonempty j))).2

theorem mark_le (j : Fin (t+1)) (k : Fin (L+1)) (hit : (W.state k).card ≤ threshold d j.val) :
    W.mark j ≤ k :=
  Finset.min'_le (W.hits j) k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩)

theorem before_mark (j : Fin (t+1)) {k : Fin (L+1)} (early : k<W.mark j) :
    threshold d j.val < (W.state k).card := lt_of_not_ge fun h => (not_le_of_gt early) (W.mark_le j k h)

theorem mark_eq_iff (j : Fin (t+1)) (k : Fin (L+1)) :
    W.mark j = k ↔ (W.state k).card ≤ threshold d j.val ∧
      ∀ i < k, threshold d j.val < (W.state i).card := by
  constructor
  · rintro rfl; exact ⟨W.mark_card j,fun _ hi=>W.before_mark j hi⟩
  · rintro ⟨hit,first⟩
    exact le_antisymm (W.mark_le j k hit) (le_of_not_gt fun h=> (first _ h).not_ge (W.mark_card j))

/-- At a noninitial gate it suffices to check the preceding gate. -/
theorem mark_eq_iff_crossing (j : Fin (t+1)) (k : Fin L) :
    W.mark j = k.succ ↔ (W.state k.succ).card ≤ threshold d j.val ∧
      threshold d j.val < (W.state k.castSucc).card := by
  rw [W.mark_eq_iff]
  constructor
  · exact fun h=>⟨h.1,h.2 _ Fin.castSucc_lt_succ⟩
  · rintro ⟨hit,old⟩
    refine ⟨hit,fun i hi=>old.trans_le (Finset.card_le_card (W.state_antitone ?_))⟩
    exact Fin.le_castSucc_iff.mpr hi

@[simp] theorem mark_zero : W.mark 0 = 0 := by
  apply le_antisymm _ (Fin.zero_le _)
  exact W.mark_le 0 0 (by simp [W.start])

noncomputable def marked (j : Fin (t+1)) : Finset V := W.state (W.mark j)

private theorem above_next (j : Fin t) : threshold d (j.val+1)<(W.marked j.castSucc).card := by
  let m := W.mark j.castSucc
  by_cases hz : m = 0
  · change threshold d (j.val+1) < (W.state m).card
    rw [hz,W.start,Finset.card_univ,threshold_succ]
    have bound : threshold d j.val≤d := Nat.div_le_self _ _
    have pos := W.card_pos
    omega
  · have nz : 0<m.val := by
      have h : m.val ≠ 0 := fun eqn => hz (Fin.ext eqn)
      omega
    let k : Fin L := ⟨m.val-1,by have := m.isLt;omega⟩
    have eqn : k.succ=m := by apply Fin.ext;change m.val-1+1=m.val;omega
    have before := W.before_mark j.castSucc (k:=k.castSucc) ((Fin.castSucc_lt_succ (i:=k)).trans_le eqn.le)
    have heavy := W.heavy k
    change threshold d j.val < (W.state k.castSucc).card at before
    change threshold d (j.val+1)<(W.state m).card
    rw [←eqn,threshold_succ]
    omega

theorem mark_strictMono : StrictMono W.mark := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro j
  by_contra! h
  have card := Finset.card_le_card (W.state_antitone h)
  exact (W.above_next j).not_ge (card.trans (W.mark_card j.succ))

theorem marked_antitone : Antitone W.marked :=
  fun _ _ h => W.state_antitone (W.mark_strictMono.monotone h)

@[simp] theorem marked_zero : W.marked 0=Finset.univ := by simp [marked,W.start]

theorem marked_drop (j : Fin t) : (W.marked j.succ).card<(W.marked j.castSucc).card :=
  (W.mark_card j.succ).trans_lt (W.above_next j)

theorem marked_last : (W.marked (Fin.last t)).card=1 := by
  have below := W.mark_card (Fin.last t)
  change (W.marked (Fin.last t)).card ≤ threshold d t at below
  rw [threshold_log W.card_pos] at below
  have above := Finset.card_le_card (W.state_antitone (Fin.le_last (W.mark (Fin.last t))))
  rw [W.finish] at above
  exact le_antisymm below above

noncomputable def color (v : V) : Fin (t+1) := chainColor W.marked W.marked_zero v

theorem mem_marked {v : V} {j : Fin (t+1)} : v∈W.marked j ↔ j≤W.color v :=
  mem_chain_iff _ _ W.marked_antitone j v

theorem color_surjective : Function.Surjective W.color :=
  chainColor_surjective W.marked W.marked_zero W.marked_antitone W.marked_drop
    (Finset.card_pos.mp (by rw [W.marked_last];decide))

theorem marked_eq_color_tail (j : Fin (t+1)) :
    W.marked j = Finset.univ.filter (fun v => j≤W.color v) := by
  ext v
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,W.mem_marked]

/-- The slots emitted on a marked segment are exactly one color class. -/
theorem mem_difference_iff {v : V} (j : Fin t) :
    v ∈ W.marked j.castSucc \ W.marked j.succ ↔ W.color v = j.castSucc := by
  rw [Finset.mem_sdiff,W.mem_marked,W.mem_marked]
  constructor
  · rintro ⟨lo,hi⟩
    apply Fin.ext
    change j.val≤(W.color v).val at lo
    change ¬ j.val+1≤(W.color v).val at hi
    change (W.color v).val=j.val
    omega
  · rintro h
    rw [h]
    exact ⟨le_rfl,(Fin.castSucc_lt_succ (i:=j)).not_ge⟩

theorem mem_last_iff {v : V} : v∈W.marked (Fin.last t) ↔ W.color v=Fin.last t := by
  rw [W.mem_marked]
  exact ⟨fun h=>le_antisymm (Fin.le_last _) h,fun h=>h.ge⟩

end SlotWalk
end Hierarchy.FormulaPartition

end OAI
