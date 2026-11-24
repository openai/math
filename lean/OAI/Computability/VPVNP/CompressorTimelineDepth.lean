import OAI.Computability.VPVNP.CompressorPassTimeline

/-! # The stored level number of each chronological block visit

A pass advances the stored history by one level, while its calendar ordinal
advances by its number of physical rows. The current history length agrees
with the block number and shrinking or refresh index at every pass.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PassTimeline

variable {steps : ℕ}

/-- History level of a pass, counting all previous blocks and the preceding passes in the
current block. -/
def Located.depth (loc : Located steps) : ℕ :=
  loc.block*(steps+1) + match loc.pass with | .shrink i => i.val | .refresh => steps

/-- Every pass in the list has its position plus `first` as its stored history depth. -/
def Numbered (first : ℕ) (xs : List (Located steps)) : Prop :=
  ∀ i : Fin xs.length, xs[i.val].depth = first+i.val

theorem Numbered.head {s : Located steps} {ss : List (Located steps)} {first : ℕ}
    (h : Numbered first (s::ss)) : s.depth = first := by simpa using h 0

theorem Numbered.tail {s : Located steps} {ss : List (Located steps)} {first : ℕ}
    (h : Numbered first (s::ss)) : Numbered (first+1) ss := by
  intro i
  have eq := h i.succ
  simp only [Fin.val_succ,List.getElem_cons_succ] at eq
  rw [eq]
  omega

theorem Numbered.append {xs ys : List (Located steps)} {first : ℕ}
    (hx : Numbered first xs) (hy : Numbered (first+xs.length) ys) : Numbered first (xs++ys) := by
  intro i
  by_cases lt : i.val < xs.length
  · rw [List.getElem_append_left lt]
    exact hx ⟨i.val,lt⟩
  · have hi : i.val-xs.length < ys.length := by have := i.isLt; simp only [List.length_append] at this; omega
    rw [List.getElem_append_right (Nat.le_of_not_lt lt),hy ⟨_,hi⟩]
    change first+xs.length+(i.val-xs.length) = first+i.val
    omega

@[simp] theorem oneBlock_length (steps t : ℕ) : (oneBlock steps t).length = steps+1 := by simp [oneBlock]

theorem oneBlock_numbered (steps t : ℕ) : Numbered (t*(steps+1)) (oneBlock steps t) := by
  intro i
  have hi : i.val < steps+1 := i.isLt.trans_le (oneBlock_length steps t).le
  by_cases lt : i.val < steps
  · have hl : i.val < ((List.finRange steps).map (fun j => Located.mk t (Pass.shrink j))).length := by simpa using lt
    simp only [oneBlock,List.getElem_append_left hl,List.getElem_map,List.getElem_finRange,Located.depth,Fin.val_cast]
  · have eq : i.val = steps := by omega
    simp [oneBlock,eq,List.getElem_append_right,Located.depth]

@[simp] theorem timeline_length (steps T : ℕ) : (timeline steps T).length = T*(steps+1) := by
  induction T with
  | zero => simp [timeline]
  | succ t ih =>
    simp only [timeline,List.range_succ,List.flatMap_append,List.flatMap_singleton,List.length_append,oneBlock_length]
    change (timeline steps t).length+_ = _
    rw [ih,Nat.succ_mul]

theorem timeline_numbered (steps T : ℕ) : Numbered 0 (timeline steps T) := by
  induction T with
  | zero => intro i; exact i.elim0
  | succ t ih =>
    simp only [timeline,List.range_succ,List.flatMap_append,List.flatMap_singleton]
    apply ih.append
    simpa only [Nat.zero_add,timeline_length] using oneBlock_numbered steps t

theorem block_lt_of_mem {T : ℕ} {loc : Located steps} (h : loc ∈ timeline steps T) : loc.block < T := by
  obtain ⟨t,ht,hl⟩ := List.mem_flatMap.mp h
  have eq : loc.block = t := by
    rcases List.mem_append.mp hl with left|right
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp left
      rfl
    · exact congrArg Located.block (List.mem_singleton.mp right)
  exact eq ▸ List.mem_range.mp ht

end CompressorRecords.PassTimeline

end VPVNP
end Computability
end OAI
