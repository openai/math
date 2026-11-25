import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range

namespace OAI
/-! # Physical ordinals of the two prefix scans -/

namespace Hierarchy.GridPinPrefixMemory

theorem range_from_fin (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  simp

/-- At ordinal `c*N+f` the quotient selects a class and the remainder a factor. -/
def classRow {N : ℕ} (key : Fin N → ℕ) (i : ℕ) : Option (Fin N) :=
  if h : i%N<N then Option.guard (fun f => decide (key f=i/N)) ⟨i%N,h⟩ else none

theorem classRow_at {N : ℕ} (key : Fin N → ℕ) (c : ℕ) (f : Fin N) :
    classRow key (c*N+f.val) = Option.guard (fun s => decide (key s=c)) f := by
  have modAt := Nat.mul_add_mod_of_lt (a:=c) f.isLt
  have pos : 0<N := Nat.zero_lt_of_lt f.isLt
  have divAt : (c*N+f.val)/N=c := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ pos,Nat.div_eq_of_lt f.isLt,Nat.zero_add]
  simp [classRow,modAt,divAt,f.isLt]

def byClass {N : ℕ} (key : Fin N → ℕ) (classes : ℕ) : List (Fin N) :=
  (List.range classes).flatMap fun c => (List.finRange N).filter fun f => decide (key f=c)

theorem class_rows {N : ℕ} (key : Fin N → ℕ) (classes : ℕ) :
    (List.range (classes*N)).filterMap (classRow key) = byClass key classes := by
  induction classes with
  | zero => simp [byClass]
  | succ c ih =>
    rw [Nat.succ_mul,List.range_add,List.filterMap_append,ih]
    have block : ((List.range N).map (c*N+·)).filterMap (classRow key) =
        (List.finRange N).filter (fun f => decide (key f=c)) := by
      rw [←range_from_fin N,List.map_map,List.filterMap_map,←List.filterMap_eq_filter]
      apply List.filterMap_congr
      intro f _
      exact classRow_at key c f
    rw [block]
    simp [byClass,List.range_succ]

theorem byClass_nodup {N : ℕ} (key : Fin N → ℕ) (classes : ℕ) :
    (byClass key classes).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun c _ => (List.nodup_finRange N).filter _,?_⟩
  apply List.nodup_range.imp
  intro c b cb
  apply List.disjoint_left.mpr
  intro f h1 h2
  exact cb ((of_decide_eq_true (List.mem_filter.mp h1).2).symm.trans
    (of_decide_eq_true (List.mem_filter.mp h2).2))

def bucketRow (L i : ℕ) : Option (Fin L) := if hi : i<L then some ⟨i,hi⟩ else none

theorem bucket_rows (L : ℕ) : (List.range L).filterMap (bucketRow L)=List.finRange L := by
  rw [←range_from_fin L,List.filterMap_map]
  trans (List.finRange L).map id
  · apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro b _
    simp [bucketRow,b.isLt]
  · simp

end Hierarchy.GridPinPrefixMemory

end OAI
