import OAI.Computability.BorderVNP.CellSparseTable

/-! # Scanning original private boxes while retaining their copy multiplicities -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro

/-- A single public descriptor referencing a one-copy site description. -/
structure BoxBlock where
  /-- Base index of the first copy in the original bank. -/
  base : ℕ
  /-- Number of co-located copies. -/
  copies : ℕ
  /-- Distance between the banks of consecutive copies. -/
  stride : ℕ
  /-- Original private one-copy factor records. -/
  factors : List Factor

/-- Resolve each sparse site reference once, in record order. -/
def Directory.blocks (D : Directory) : List BoxBlock :=
  D.records.filterMap fun r => match r with
    | .box id base copies stride => some ⟨base, copies, stride, D.boxes.getD id []⟩
    | _ => none

/-- Ordered factor occurrences in one block. -/
def BoxBlock.visits (b : BoxBlock) : List Occurrence :=
  (List.range b.copies).flatMap fun i => b.factors.map (fun f => ⟨f, b.base + i * b.stride, i⟩)

/-- A block contributes exactly one occurrence per factor and copy. -/
theorem BoxBlock.length_visits (b : BoxBlock) : b.visits.length = b.copies * b.factors.length := by
  simp [visits, List.length_flatMap, List.map_const']

/-- The sparse directory visits exactly the local factors in the specified cell semantics. -/
theorem Directory.blocks_visits (D : Directory) : D.blocks.flatMap BoxBlock.visits = D.occurrences := by
  rcases D with ⟨boxes, rs, counts⟩
  induction rs with
  | nil => rfl
  | cons r rs ih => cases r <;> simp [blocks, occurrences, BoxBlock.visits] at ih ⊢ <;> exact ih

/-- Compiled actions can update guard and sign while preserving the original value bank. -/
def Acts (s : Stmt) (e : List ℕ) (step : (ℕ → Bool) → Flags → Flags) : Prop :=
  ∀ ops f v, value (s.expand e ++ ops) f v = value ops (step (lookup v) f) v

private theorem flatActs {α : Type*} (xs : List α) (emit : α → List Op)
    (step : (ℕ → Bool) → Flags → α → Flags)
    (h : ∀ x ∈ xs, ∀ ops f v, value (emit x ++ ops) f v = value ops (step (lookup v) f x) v)
    (ops : List Op) (f : Flags) (v : List Bool) :
    value (xs.flatMap emit ++ ops) f v = value ops (xs.foldl (step (lookup v)) f) v := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.append_assoc, List.foldl_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- Folding a sequence of compact fragments composes their flag updates. -/
theorem sequence_acts {α : Type*} (xs : List α) (s : α → Stmt) (e : List ℕ)
    (step : (ℕ → Bool) → Flags → α → Flags)
    (h : ∀ x ∈ xs, Acts (s x) e (fun bank f => step bank f x)) :
    Acts (sequence (xs.map s)) e (fun bank f => xs.foldl (step bank) f) := by
  intro ops f v
  rw [expand_sequence, List.flatMap_map]
  exact flatActs xs _ step h ops f v

/-- One loop body suffices for every copy in an interval. -/
theorem loop_acts (n : ℕ) (s : Stmt) (e : List ℕ) (step : (ℕ → Bool) → Flags → ℕ → Flags)
    (h : ∀ i < n, Acts s (i :: e) (fun bank f => step bank f i)) :
    Acts (.loop (.lit n) s) e (fun bank f => (List.range n).foldl (step bank) f) :=
  fun ops f v => flatActs _ _ _ (fun i hi => h i (List.mem_range.mp hi)) ops f v

/-- A factor body takes the global occurrence number, copy base, and copy number. -/
abbrev FactorBody := Factor → NatExpr → NatExpr → NatExpr → Stmt

/-- Store each one-copy factor fragment once, inside the copy loop. -/
def BoxBlock.fragment (b : BoxBlock) (start : ℕ) (body : FactorBody) : Stmt :=
  let i := NatExpr.index 0
  let off := NatExpr.add (.lit b.base) (.mul i (.lit b.stride))
  let row := NatExpr.add (.lit start) (.mul i (.lit b.factors.length))
  .loop (.lit b.copies) (sequence (b.factors.zipIdx.map fun fj => body fj.1 (.add row (.lit fj.2)) off i))

/-- Compact traversal over public box descriptors, retaining consecutive global occurrence numbers. -/
def sweep (body : FactorBody) : List BoxBlock → ℕ → Stmt
  | [], _ => .nil
  | b :: bs, start => .seq (b.fragment start body) (sweep body bs (start + b.copies * b.factors.length))

private theorem shift_zip {α : Type*} (xs : List α) (n k : ℕ) :
    xs.zipIdx (n+k) = (xs.zipIdx k).map (fun z => (z.1, n + z.2)) := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.map_cons, Nat.add_assoc]
    exact congrArg _ (ih (k + 1))

private theorem indexedVisits (base stride count start : ℕ) (fs : List Factor) :
    ((List.range count).flatMap (fun i => fs.map (fun f => (⟨f, base+i*stride, i⟩ : Occurrence)))).zipIdx start =
      (List.range count).flatMap (fun i => fs.zipIdx.map (fun fj =>
        ((⟨fj.1, base+i*stride, i⟩ : Occurrence), start+i*fs.length+fj.2))) := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.zipIdx_append, ih]
    congr 1
    have hl := BoxBlock.length_visits (⟨base, n, stride, fs⟩ : BoxBlock)
    simp only [BoxBlock.visits] at hl
    rw [hl, List.zipIdx_map, ← Nat.add_zero (start + n * fs.length),
      shift_zip fs (start + n * fs.length) 0]
    simp [List.map_map, Function.comp_def]

private theorem block_acts (b : BoxBlock) (start : ℕ) (body : FactorBody) (e : List ℕ)
    (step : (ℕ → Bool) → Flags → Occurrence × ℕ → Flags)
    (h : ∀ f j off i env, Acts (body f j off i) env (fun bank st =>
      step bank st (⟨f, off.eval env, i.eval env⟩, j.eval env))) :
    Acts (b.fragment start body) e (fun bank st => (b.visits.zipIdx start).foldl (step bank) st) := by
  let g (i : ℕ) (z : Factor × ℕ) : Occurrence × ℕ :=
    (⟨z.1, b.base + i * b.stride, i⟩, start + i * b.factors.length + z.2)
  have hk := loop_acts b.copies _ e (fun bank st i =>
    b.factors.zipIdx.foldl (fun s z => step bank s (g i z)) st) (fun i _ => sequence_acts
      b.factors.zipIdx _ (i :: e) (fun bank st z => step bank st (g i z)) (fun z _ =>
        h z.1 (.add (.add (.lit start) (.mul (.index 0) (.lit b.factors.length))) (.lit z.2))
          (.add (.lit b.base) (.mul (.index 0) (.lit b.stride))) (.index 0) (i :: e)))
  intro ops st v
  unfold BoxBlock.fragment
  rw [hk ops st v]
  simp only [BoxBlock.visits, indexedVisits, List.foldl_flatMap, List.foldl_map, g]

/-- The unexpanded sparse scan produces the same signed guard-state update as
visiting the complete list of indexed factor occurrences. -/
theorem sweep_acts (body : FactorBody) (bs : List BoxBlock) (start : ℕ) (e : List ℕ)
    (step : (ℕ → Bool) → Flags → Occurrence × ℕ → Flags)
    (h : ∀ f j off i env, Acts (body f j off i) env (fun bank st =>
      step bank st (⟨f, off.eval env, i.eval env⟩, j.eval env))) :
    Acts (sweep body bs start) e (fun bank st =>
      ((bs.flatMap BoxBlock.visits).zipIdx start).foldl (step bank) st) := by
  induction bs generalizing start with
  | nil => intro _ _ _; rfl
  | cons b bs ih =>
    intro ops f v
    simp only [sweep, Stmt.expand, List.append_assoc, List.flatMap_cons, List.zipIdx_append,
      List.foldl_append, BoxBlock.length_visits]
    rw [block_acts b start body e step h, ih]

end CellSparse

end BorderVNP
end Computability
end OAI
