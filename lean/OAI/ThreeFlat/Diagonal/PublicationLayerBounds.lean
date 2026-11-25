import OAI.ThreeFlat.Diagonal.NavigationNodeArchive
import OAI.ThreeFlat.Diagonal.PhysicalRegisterSpace

namespace OAI
/-! # Owner, child, and chronological header bounds for the physical node publisher -/

namespace ThreeFlat.Diagonal.NavigationPass

open RAM RAM.NavigationNodeRows NavigationDirectory PhysicalStage
open CompressorPacking.Native.ShrinkStage

/-- The owner array in field 44 occupies the last words of the stage allocation. -/
theorem owner_end_eq_next_heap (K : ℕ) (c : Cursor) (step : Stage) :
    (allocate K c step).words 44 + step.nodes = (allocate K c step).next.heap := by
  cases step <;> rfl

private theorem owner_before_finish (K : ℕ) (c : Cursor) (t : Stage) (rest : List Stage)
    (l : Layer) (count : l.count=t.nodes) :
    (allocate K c t).words 44+l.count ≤ (finish K (t::rest) c).heap := by
  rw [count,owner_end_eq_next_heap,finish,heap_finish]
  exact Nat.le_add_right _ _

/-- For a real physical stage directory, the layer being published has exactly the
number of inputs of the following stage. Its owner array ends inside the final heap. -/
theorem program_ownerEnd {F : Type} [Field F] {degree : ℕ} (P : Program F degree) (K rem v : ℕ)
    (c : Cursor) (l : Layer) (count : l.count = v*2^(P.charge+rem))
    (row : Layers) (mem : row ∈ nodeLayers K (P.directory rem v) c l)
    (nonfinal : row.parent.finalLayer = false) :
    row.parent.owners+row.actual.count ≤ (finish K (P.directory rem v) c).heap := by
  induction P generalizing v c l row with
  | done s =>
    simp only [Program.directory,nodeLayers,List.mem_singleton] at mem
    subst row
    contradiction
  | shrink s t T small tail ih =>
    let tag := 2^CompressorPacking.tagBits (2^s)
    let x : Dimensions := ⟨v,2^s,2*2^s+1,tag,2^(tail.charge+rem),2^t⟩
    let stage := Stage.shrink x
    let rest := tail.directory rem (v*tag)
    change row ∈ ⟨l,⟨false,(allocate K c stage).next.node,(allocate K c stage).words 44⟩⟩ ::
      nodeLayers K rest (allocate K c stage).next (nodeLayer K c stage) at mem
    change _ ≤ (finish K (stage::rest) c).heap
    rcases List.mem_cons.mp mem with h | h
    · subst row
      apply owner_before_finish K c stage rest l
      have input := (Program.shrink_positions s t (tail.charge+rem) v).1
      exact count.trans (by simpa only [stage,Stage.nodes,x,tag,Program.charge,Nat.add_assoc] using input.symm)
    · apply ih (v:=v*tag) (c:=(allocate K c stage).next) (l:=nodeLayer K c stage) (row:=row) <;>
        first | rfl | exact h | exact nonfinal
  | refresh s t h pad coeff γ C T two pos sym degree zero conn newDegree tail ih =>
    let stage := Stage.refresh v (2^s) (2^(tail.charge+rem)) h pad
    let rest := tail.directory rem (v*2^s)
    change row ∈ ⟨l,⟨false,(allocate K c stage).next.node,(allocate K c stage).words 44⟩⟩ ::
      nodeLayers K rest (allocate K c stage).next (nodeLayer K c stage) at mem
    change _ ≤ (finish K (stage::rest) c).heap
    rcases List.mem_cons.mp mem with eq | after
    · subst row
      apply owner_before_finish K c stage rest l
      have input := (Program.refresh_positions s (tail.charge+rem) v h pad).1
      exact count.trans (by simpa only [stage,Stage.nodes,Program.charge,Nat.add_assoc] using input.symm)
    · apply ih (v:=v*2^s) (c:=(allocate K c stage).next) (l:=nodeLayer K c stage) (row:=row) <;>
        first | rfl | exact after | exact nonfinal

private theorem member_le_maxRows (steps : List Stage) (t : Stage) (mem : t∈steps) :
    childArity t ≤ maxRows childArity 0 steps := by
  induction steps with
  | nil => simp at mem
  | cons s tail ih =>
    rcases List.mem_cons.mp mem with eq|after
    · subst t
      exact le_max_left ..
    · exact (ih after).trans (le_max_right ..)

private theorem layer_arity_le (K cap : ℕ) (steps : List Stage) (c : Cursor) (l : Layer)
    (initial : l.childCount≤cap) (bound : ∀ t∈steps,childArity t≤cap)
    (row : Layers) (mem : row∈nodeLayers K steps c l) : row.actual.childCount≤cap := by
  induction steps generalizing c l with
  | nil =>
    simp only [nodeLayers,List.mem_singleton] at mem
    subst row
    exact initial
  | cons t rest ih =>
    rcases List.mem_cons.mp mem with eq|after
    · subst row
      exact initial
    · exact ih (allocate K c t).next (nodeLayer K c t) (bound _ List.mem_cons_self)
        (fun s hs => bound s (List.mem_cons_of_mem _ hs)) after

/-- The child cap in the installed node archive bounds the arity of every real layer. -/
theorem seed_childArity (A : Archive) (steps : List Stage) (row : Layers)
    (mem : row∈nodeLayers A.K steps A.cursor A.seedLayer) :
    row.actual.childCount≤ maxRows childArity 0 steps :=
  layer_arity_le _ _ _ _ _ (Nat.zero_le _) (member_le_maxRows steps) row mem

/-- Every allocation in the repeated physical program stays within a single scratch
region from the initial heap. The public cursor starts this heap at region 22. -/
theorem cursor_heap_end {F : Type} [Field F] (B : Block F) {u rem low : ℕ} (hu : 40≤u)
    (levels : B.levels+1≤u) (factor : B.allocations.sum≤u) (half : low=u^10/2)
    (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6) (K : ℕ) (c : Cursor) :
    (finish K ((B.repeat (u^8)).directory rem ((B.repeat (u^8)).charge+rem)) c).heap ≤
      c.heap+TickWorkspace.stride u := by
  rw [heap_finish]
  apply Nat.add_le_add_left
  have total := B.cursor_heap_space hu levels factor half depth
  dsimp only at total
  have smaller : (2:ℕ)^(u^10-u^4)≤2^(u^10) :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have wide : (2:ℕ)^(u^10)≤TickWorkspace.stride u := Nat.le_self_pow (by decide) _
  omega

/-- The sixteen words addressed by a published layer are part of the mounted header tape. -/
theorem node_header_end (first : ℕ) (rows : List Layers) (i : Fin rows.length) :
    first+16*i.val+16≤first+16*rows.length := by
  have := i.isLt
  omega


end ThreeFlat.Diagonal.NavigationPass

end OAI
