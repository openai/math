import OAI.ThreeFlat.Routing.SortStagesBridge
import OAI.ThreeFlat.Routing.StableCompactionOrder
import OAI.Computability.VPVNP.RAMTapeSortReplaySlot

namespace OAI
/-! # Unique site-by-site comparator histories for stable compaction -/

noncomputable section
namespace ThreeFlat.Routing.StableCompactStages

open Computability.VPVNP.RAMSort
open StableCompaction (record masked compact)

def mate {m : ℕ} (s : Stage m) (v : Fin (2^m)) : Fin (2^m) :=
  ⟨partner s.stride v, partner_lt v.isLt (s.stride_lt.trans_le s.phase_le)⟩

theorem mate_val {m : ℕ} (s : Stage m) (v : Fin (2^m)) : (mate s v).val = v.val ^^^ 2^s.stride := rfl

def strideMask {m : ℕ} (s : Stage m) : Fin (2^m) :=
  ⟨2^s.stride, Nat.pow_lt_pow_right (by decide) (s.stride_lt.trans_le s.phase_le)⟩

theorem mate_eq_xor {m : ℕ} (s : Stage m) (v : Fin (2^m)) : mate s v = v ^^^ strideMask s := by
  apply Fin.ext
  change (v.val ^^^ 2^s.stride) = (v.val ^^^ 2^s.stride) % 2^m
  exact (Nat.mod_eq_of_lt (mate s v).isLt).symm

def next {m u : ℕ} (s : Stage m) (v : Fin (2^m)) (own other : Fin u → Bool) : Fin u → Bool :=
  let a := addressEquiv u
  a.symm (if v.val.testBit s.stride = v.val.testBit s.phase then min (a own) (a other)
    else max (a own) (a other))

abbrev Values (m u : ℕ) := Fin (steps m).length.succ → Fin (2^m) → Fin u → Bool

def Accepts {m : ℕ} (M X Y : Fin (2^m) → Bool) (H : Values m ((1+m)+1)) : Prop :=
  (∀ v, H 0 v = record M X v) ∧
  (∀ (r : Fin (steps m).length) v,
    H r.succ v = next ((steps m)[r.val]) v (H r.castSucc v) (H r.castSucc (mate ((steps m)[r.val]) v))) ∧
  ∀ v, Y v = masked (H (Fin.last _) v)

private theorem next_layer {m u : ℕ} (s : Stage m) (v : Fin (2^m)) (x : ℕ → Fin (2^u)) :
    (addressEquiv u).symm (comparatorLayer s.stride (phaseDirection s.phase) x v) =
      next s v ((addressEquiv u).symm (x v)) ((addressEquiv u).symm (x (mate s v))) := by
  have orient : (v.val.testBit s.stride = v.val.testBit s.phase) ↔
      (decide (v.val < partner s.stride v.val) == phaseDirection s.phase v.val) = true := by
    rw [Computability.VPVNP.RAMTape.SortReplay.orientation]
    simp
  simp only [next, Equiv.apply_symm_apply, orient]
  by_cases h : v.val < partner s.stride v.val <;> cases hd : phaseDirection s.phase v.val <;>
    simp [comparatorLayer,h,hd,upper,lower,mate,min_comm,max_comm]

private def inputs {m : ℕ} (M X : Fin (2^m) → Bool) (i : ℕ) : Fin (2^((1+m)+1)) :=
  addressEquiv _ (record M X (Fin.ofNat _ i))

@[simp] private theorem inputs_at {m : ℕ} (M X : Fin (2^m) → Bool) (v : Fin (2^m)) :
    inputs M X v = addressEquiv _ (record M X v) := by
  have eq : Fin.ofNat (2^m) v.val = v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
  simp only [inputs,eq]

def history {m : ℕ} (M X : Fin (2^m) → Bool) : Values m ((1+m)+1) :=
  fun r v => (addressEquiv _).symm (run ((steps m).take r.val) (inputs M X) v.val)

private theorem first {m : ℕ} (M X : Fin (2^m) → Bool) (v : Fin (2^m)) :
    history M X 0 v = record M X v := by simp [history,run]

private theorem update {m : ℕ} (M X : Fin (2^m) → Bool) (r : Fin (steps m).length) (v : Fin (2^m)) :
    history M X r.succ v = next ((steps m)[r.val]) v (history M X r.castSucc v)
      (history M X r.castSucc (mate ((steps m)[r.val]) v)) := by
  simp only [history,Fin.val_succ,Fin.val_castSucc,List.take_succ_eq_append_getElem r.isLt,
    run,List.foldl_append,List.foldl_cons,List.foldl_nil]
  exact next_layer ..

private theorem last {m : ℕ} (M X : Fin (2^m) → Bool) (v : Fin (2^m)) :
    masked (history M X (Fin.last _) v) = compact M X v := by
  have init : block m 0 (inputs M X) = fun i => addressEquiv _ (record M X i) := by
    funext i
    simp [block]
  have sorted := congrFun (sorted_block m (inputs M X)) v
  simp only [init,block,Nat.zero_mul,Nat.zero_add] at sorted
  rw [← StableCompaction.masked_sorted M X v]
  simp only [history,Fin.val_last,List.take_length,sorted,StableCompaction.sortedRecord]

private theorem forced {m : ℕ} {M X Y : Fin (2^m) → Bool} {H : Values m ((1+m)+1)}
    (h : Accepts M X Y H) : H = history M X := by
  funext r
  induction r using Fin.induction with
  | zero => exact funext (fun v => (h.1 v).trans (first M X v).symm)
  | succ r ih =>
    funext v
    rw [h.2.1 r v,update M X r v,ih]

theorem sound_history {m : ℕ} {M X Y : Fin (2^m) → Bool} {H : Values m ((1+m)+1)}
    (h : Accepts M X Y H) : Y = compact M X := by
  funext v
  exact (h.2.2 v).trans (by rw [forced h]; exact last M X v)

theorem existsUnique_history {m : ℕ} (M X Y : Fin (2^m) → Bool) :
    (∃! H, Accepts M X Y H) ↔ Y = compact M X := by
  constructor
  · rintro ⟨_,ok,_⟩
    exact sound_history ok
  · rintro rfl
    exact ⟨history M X,⟨first M X,update M X,fun v => (last M X v).symm⟩,fun _ h => forced h⟩

end ThreeFlat.Routing.StableCompactStages

end
end OAI
