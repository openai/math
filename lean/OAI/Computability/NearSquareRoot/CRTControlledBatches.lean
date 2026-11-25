import OAI.Computability.NearSquareRoot.CRTControlledBudget
import OAI.Computability.NearSquareRoot.CRTControlledBenes

/-! # Allocating address space for synchronized switch stages

A batch contains a bounded number of blocks even when every block has width one. This
leaves enough unused positions for two guarded chunks and an aligned payload. A single
division of the block number computes its batch index.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

/-- `j` is a fixed reciprocal free-space fraction and `g` bounds both the guard width
and the number of bits in any target block. -/
def blocksPerBatch (k j g : ℕ) : ℕ := k / (8*j*g)

def batchCount (d k j g : ℕ) : ℕ := d ⌈/⌉ blocksPerBatch k j g

theorem batch_count_le {d k j g : ℕ} (hj : 0 < j) (hg : 0 < g) (hd : d ≤ k)
    (hroom : 8*j*g ≤ k) :
    batchCount d k j g ≤ 16*j*g := by
  let t := 8*j*g
  have ht : 0 < t := by dsimp [t]; positivity
  have hq : 0 < k / t := Nat.div_pos hroom ht
  have hk := Nat.div_add_mod k t
  have hr := Nat.mod_lt k ht
  have hb : t ≤ t * (k/t) := Nat.le_mul_of_pos_right _ hq
  unfold batchCount blocksPerBatch
  apply (ceilDiv_le_iff_le_mul (by exact hq)).mpr
  calc
    d ≤ k := hd
    _ ≤ 2 * t * (k / t) := by rw [Nat.mul_assoc]; omega
    _ = _ := by dsimp [t]; ring

/-- A short final batch uses the same allowance as a full one. `e` of the `k` positions
are external controls. In addition to these, reserve one entire block per target for
its internal control bits, two guarded chunks, and the low payload positions. -/
theorem batch_space {k e b j g r : ℕ} (hj : 0 < j) (he : e + k / j ≤ k)
    (hb : b ≤ blocksPerBatch k j g) (hr : r ≤ k / (2*j)) :
    e + b*g + b*g + b*g + r ≤ k := by
  have ha : b * (8*j*g) ≤ k := (Nat.mul_le_mul_right _ hb).trans (Nat.div_mul_le_self ..)
  have hx : r * (2*j) ≤ k := (Nat.mul_le_mul_right _ hr).trans (Nat.div_mul_le_self ..)
  have ha' : 2*((b*g + b*g + b*g) * j) ≤ k := by
    calc
      _ ≤ b*(8*j*g) := by nlinarith only [Nat.zero_le (b*g*j)]
      _ ≤ k := ha
  have hx' : 2*(r*j) ≤ k := by convert hx using 1; ring
  have hs : b*g + b*g + b*g + r ≤ k / j := by
    apply (Nat.le_div_iff_mul_le hj).2
    rw [Nat.add_mul]
    omega
  omega

/-- Every target block is assigned a legal batch and a distinct local slot. -/
def batchAddress {d k j g : ℕ} (hcap : 0 < blocksPerBatch k j g) :
    Fin d ↪ Fin (batchCount d k j g) × Fin (blocksPerBatch k j g) where
  toFun v := (⟨v.val / blocksPerBatch k j g, by
    apply (Nat.div_lt_iff_lt_mul hcap).2
    exact v.isLt.trans_le (by simpa [batchCount, Nat.mul_comm] using (le_smul_ceilDiv (b := d) hcap))⟩,
    ⟨v.val % blocksPerBatch k j g, Nat.mod_lt _ hcap⟩)
  inj' x y h := by
    apply Fin.ext
    have h₁ := congrArg (fun q : Fin (batchCount d k j g) × Fin (blocksPerBatch k j g) => q.1.val) h
    have h₂ := congrArg (fun q : Fin (batchCount d k j g) × Fin (blocksPerBatch k j g) => q.2.val) h
    change x.val / _ = y.val / _ at h₁
    change x.val % _ = y.val % _ at h₂
    calc
      x.val = (blocksPerBatch k j g) * (x.val / blocksPerBatch k j g) + x.val % blocksPerBatch k j g :=
        (Nat.div_add_mod ..).symm
      _ = (blocksPerBatch k j g) * (y.val / blocksPerBatch k j g) + y.val % blocksPerBatch k j g := by rw [h₁,h₂]
      _ = y.val := Nat.div_add_mod ..

/-- Each physical chunk also has a leading unused segment. -/
theorem batch_space_with_heads {k e b j g r : ℕ} (hj : 0 < j)
    (he : e + k / j ≤ k) (hb : b ≤ blocksPerBatch k j g) (hroom : 8*j*g ≤ k)
    (hr : r ≤ k / (4*j)) :
    e + b*g + (b+1)*g + (b+1)*g + r ≤ k := by
  have ha : b*(8*j*g) ≤ k := (Nat.mul_le_mul_right _ hb).trans (Nat.div_mul_le_self ..)
  have hx : r*(4*j) ≤ k := (Nat.mul_le_mul_right _ hr).trans (Nat.div_mul_le_self ..)
  have h : b*g + (b+1)*g + (b+1)*g + r ≤ k / j := by
    apply (Nat.le_div_iff_mul_le hj).2
    nlinarith only [ha, hroom, hx, Nat.zero_le k]
  omega

def stageSchedule (batches stages : ℕ) : List (ℕ × ℕ) :=
  (List.range stages).flatMap (fun t => (List.range batches).map (t, ·))

theorem stageSchedule_length (batches stages : ℕ) :
    (stageSchedule batches stages).length = stages*batches := by
  induction stages with
  | zero => simp [stageSchedule]
  | succ n ih => simp [stageSchedule, List.range_succ, Nat.succ_mul]

open Benes

/-- Only the blocks assigned to the current batch execute this switch. -/
def restrictedStage {d : ℕ} {X : Type*} (which : Fin d → ℕ) (width : Fin d → ℕ)
    (perm : (i : Fin d) → X → Equiv.Perm (Word (width i))) (q : X)
    (data : (i : Fin d) → Word (width i)) (pass : ℕ × ℕ) :
    (i : Fin d) → Word (width i) :=
  fun i => if which i = pass.2 then (compile _ (perm i q)).val.stage pass.1 (data i) else data i

private theorem restricted_fold {d : ℕ} {X : Type*} (which : Fin d → ℕ) (width : Fin d → ℕ)
    (perm : (i : Fin d) → X → Equiv.Perm (Word (width i))) (q : X)
    (data : (i : Fin d) → Word (width i)) (batch t : ℕ) (i : Fin d) :
    ((List.range batch).map (t, ·)).foldl (restrictedStage which width perm q) data i =
      if which i < batch then (compile _ (perm i q)).val.stage t (data i) else data i := by
  induction batch with
  | zero => simp
  | succ b ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil, restrictedStage]
    rw [ih]
    split_ifs <;> (first | rfl | omega)

theorem stageSchedule_routes {d : ℕ} {X : Type*} (which : Fin d → ℕ) (width : Fin d → ℕ)
    (perm : (i : Fin d) → X → Equiv.Perm (Word (width i))) (q : X)
    (data : (i : Fin d) → Word (width i)) (batches stages : ℕ)
    (hw : ∀ i, which i < batches) (hs : ∀ i, 2*width i - 1 ≤ stages) :
    (stageSchedule batches stages).foldl (restrictedStage which width perm q) data =
      fun i => perm i q (data i) := by
  have fold_eq (st : List ℕ) (v : (i : Fin d) → Word (width i)) :
      (st.flatMap fun t => (List.range batches).map (t, ·)).foldl
        (restrictedStage which width perm q) v =
          st.foldl (fun x t => blockStage width perm q t x) v := by
    induction st generalizing v with
    | nil => rfl
    | cons t st ih =>
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons, ih]
      congr 1
      funext i
      rw [restricted_fold]
      simp only [hw, ↓reduceIte]
      rfl
  exact (fold_eq (List.range stages) data).trans (parallel_routing width perm q stages hs data)

end Controlled

end NearSquareRoot
end Computability
end OAI
