import OAI.Hierarchy.ProbeStageLocations

namespace OAI
/-! # Disjoint locations used by a native chronology record -/

namespace Hierarchy.ProbeStage.Native

/-- A written output is identified by its column and ordinal. The private scratch area and
all sixteen literal/counter/mask regions have separate tagged address spaces. -/
inductive Cell (h d : ℕ) where
  | rank (k : Fin 3) (i : Fin (2^h))
  | temp (k : Fin 12)
  | area (k : Fin 16) (off : Fin (regionSize h d))
  deriving DecidableEq

def rankAddr (h d j : ℕ) (k : Fin 3) (i : Fin (2^h)) := bankBase h d copies j k.val+i.val

def Cell.addr {h d : ℕ} (j : ℕ) : Cell h d → ℕ
  | .rank k i => rankAddr h d j k i
  | .temp k => scratch h d j k
  | .area k o => region h d j k+o.val

private theorem ordinal_extent (h d : ℕ) : 2^h≤extent h d := by
  change 2^h≤2^roomBits h d
  exact Nat.pow_le_pow_right (by decide) (by unfold roomBits;omega)

theorem rank_scratch (h d j : ℕ) (k : Fin 3) (i : Fin (2^h)) (q : Fin 12) :
    rankAddr h d j k i<scratch h d j q := by
  have sep := separate h d copies j k.val 14 (by omega)
  have ii := i.isLt.trans_le (ordinal_extent h d)
  unfold rankAddr scratch
  omega

private theorem rank_before_rank {h d j : ℕ} {k q : Fin 3} (lt : k<q) (i l : Fin (2^h)) :
    rankAddr h d j k i<rankAddr h d j q l := by
  have sep := separate h d copies j k.val q.val lt
  have ii := i.isLt.trans_le (ordinal_extent h d)
  unfold rankAddr
  omega

theorem cell_injective (h d j : ℕ) : Function.Injective (Cell.addr (h:=h) (d:=d) j) := by
  intro x y eqn
  cases x with
  | rank k i =>
    cases y with
    | rank k' i' =>
      change rankAddr h d j k i=rankAddr h d j k' i' at eqn
      have ke : k=k' := by
        by_contra ne
        exact (lt_or_gt_of_ne ne).elim (fun lt=>(rank_before_rank (d:=d) (j:=j) lt i i').ne eqn)
          (fun gt=>(rank_before_rank (d:=d) (j:=j) gt i' i).ne eqn.symm)
      subst k'
      have ie : i=i' := Fin.ext (Nat.add_left_cancel eqn)
      subst i';rfl
    | temp q => exact False.elim ((rank_scratch h d j k i q).ne eqn)
    | area q o => exact False.elim ((((rank_scratch h d j k i 0).trans (scratch_separate h d j 0 q)).trans_le
        (Nat.le_add_right _ o.val)).ne eqn)
  | temp k =>
    cases y with
    | rank q i => exact False.elim ((rank_scratch h d j q i k).ne eqn.symm)
    | temp k' =>
      have kk : k=k' := Fin.ext (Nat.add_left_cancel eqn)
      subst k';rfl
    | area q o => exact False.elim (((scratch_separate h d j k q).trans_le (Nat.le_add_right _ o.val)).ne eqn)
  | area k o =>
    cases y with
    | rank q i => exact False.elim ((((rank_scratch h d j q i 0).trans (scratch_separate h d j 0 k)).trans_le
        (Nat.le_add_right _ o.val)).ne eqn.symm)
    | temp q => exact False.elim (((scratch_separate h d j q k).trans_le (Nat.le_add_right _ o.val)).ne eqn.symm)
    | area k' o' =>
      have ke : k=k' := by
        by_contra hn
        exact (region_address_ne (h:=h) (d:=d) (j:=j) o.isLt o'.isLt hn) eqn
      subst k'
      have oe : o=o' := Fin.ext (Nat.add_left_cancel eqn)
      subst o';rfl

end Hierarchy.ProbeStage.Native

end OAI
