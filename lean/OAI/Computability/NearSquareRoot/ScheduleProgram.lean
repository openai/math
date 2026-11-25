import OAI.Computability.NearSquareRoot.ScheduleUniversal
import Mathlib.Data.List.FinRange

/-!
# ROM encoding for the fixed interpreter

Each finite-control candidate contributes one row per control state. A row stores
a literal branch per possible read tuple, followed by the unary destination for a
moving transition. The list of read tuples is supplied explicitly, so the encoder
computes from an effectively enumerated alphabet and fixed tape set.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Universal

open IntegerMultiplication
variable {A I : Type} {m : ℕ}

/-- Encode the simultaneous tape actions in the branch tag. -/
def commands (step : Option (Fin m × (I → A × TM.Move))) : Option (I → A × TM.Move) :=
  step.map Prod.snd

/-- A halted branch has no destination. -/
def target (step : Option (Fin m × (I → A × TM.Move))) : ℕ :=
  (step.map (fun p => p.1.val)).getD 0

def entryCode (machine : TM.Rule A (Fin m) I) (q : Fin m) (read : I → A) :
    List (Tag A I) :=
  let step := machine q read
  .branch read (commands step) :: List.replicate (target step) .tick

def rowCode (machine : TM.Rule A (Fin m) I) (reads : List (I → A)) (q : Fin m) :
    List (Tag A I) := .row :: reads.flatMap (entryCode machine q)

/-- Both interpreter program tapes carry this same list. -/
def program (machine : TM.Rule A (Fin m) I) (reads : List (I → A)) : List (Tag A I) :=
  .origin :: ((List.finRange m).flatMap (rowCode machine reads) ++ [.endCode])

/-- All ROM cells outside the finite image read as end markers. -/
def fetch (code : List (Tag A I)) : ℤ → Tag A I
  | .ofNat i => code[i]?.getD .endCode
  | .negSucc _ => .endCode

@[simp] theorem fetch_at_split (before after : List (Tag A I)) (x : Tag A I) :
    fetch (before ++ x :: after) before.length = x := by
  simp [fetch]

/-- Rows strictly preceding a given state's row. -/
def beforeRows (machine : TM.Rule A (Fin m) I) (reads : List (I → A)) (q : Fin m) :=
  ((List.finRange m).take q.val).flatMap (rowCode machine reads)

/-- The tail after the entire current row, including the terminal marker. -/
def afterRow (machine : TM.Rule A (Fin m) I) (reads : List (I → A)) (q : Fin m) :=
  ((List.finRange m).drop (q.val+1)).flatMap (rowCode machine reads) ++ [.endCode]

theorem program_row (machine : TM.Rule A (Fin m) I) (reads : List (I → A)) (q : Fin m) :
    program machine reads =
      .origin :: (beforeRows machine reads q ++ rowCode machine reads q ++ afterRow machine reads q) := by
  have hi : q.val < (List.finRange m).length := by simp
  have h := List.take_append_drop q.val (List.finRange m)
  rw [List.drop_eq_getElem_cons hi] at h
  have e : (List.finRange m)[q.val] = q := Fin.ext (by simp)
  rw [e] at h
  unfold program beforeRows afterRow
  conv_lhs => rw [← h]
  simp [List.flatMap_append, List.append_assoc]

def isRow : Tag A I → Bool
  | .row => true
  | _ => false

def isBranchOf (read : I → A) (t : Tag A I) : Prop :=
  ∃ op, t = .branch read op

private theorem entry_classify (machine : TM.Rule A (Fin m) I) (q : Fin m)
    (r : I → A) {x : Tag A I} (hx : x ∈ entryCode machine q r) :
    x = .branch r (commands (machine q r)) ∨ x = .tick := by
  simpa [entryCode, List.mem_replicate] using
    (List.mem_cons.mp hx).imp_right (fun h => (List.mem_replicate.mp h).2)

private theorem row_classify (machine : TM.Rule A (Fin m) I) (rs : List (I → A)) (q : Fin m)
    {x : Tag A I} (h : x ∈ rowCode machine rs q) :
    x = .row ∨ (∃ r op, x = .branch r op) ∨ x = .tick := by
  rcases List.mem_cons.mp h with eq | more
  · exact .inl eq
  obtain ⟨r,_,hx⟩ := List.mem_flatMap.mp more
  rcases entry_classify machine q r hx with e | e
  · exact .inr (.inl ⟨_, _, e⟩)
  · exact .inr (.inr e)

/-- Rewind sees an origin marker only at program cell zero. -/
theorem program_no_other_origin (machine : TM.Rule A (Fin m) I) (rs : List (I → A)) :
    Tag.origin ∉ (program machine rs).tail := by
  unfold program
  simp only [List.tail_cons, List.mem_append, List.mem_singleton, reduceCtorEq, or_false]
  intro h
  obtain ⟨q,_,hq⟩ := List.mem_flatMap.mp h
  rcases row_classify machine rs q hq with e | ⟨_,_,e⟩ | e <;> cases e

private theorem entries_count (machine : TM.Rule A (Fin m) I) (rs : List (I → A)) (q : Fin m) :
    (rs.flatMap (entryCode machine q)).countP isRow = 0 := by
  apply List.countP_eq_zero.mpr
  intro x hx
  obtain ⟨r,_,hx⟩ := List.mem_flatMap.mp hx
  rcases entry_classify machine q r hx with rfl | rfl <;> simp [isRow]

/-- A destination `q` skips exactly `q.val` prior rows. -/
theorem beforeRows_count (machine : TM.Rule A (Fin m) I) (rs : List (I → A)) (q : Fin m) :
    (beforeRows machine rs q).countP isRow = q.val := by
  have count_rows (qs : List (Fin m)) :
      (qs.flatMap (rowCode machine rs)).countP isRow = qs.length := by
    induction qs with
    | nil => rfl
    | cons a l ih => simp [rowCode, List.countP_cons, entries_count, isRow, ih]
  simp [beforeRows, count_rows]

theorem beforeRows_classify (machine : TM.Rule A (Fin m) I) (rs : List (I → A)) (q : Fin m)
    {x : Tag A I} (hx : x ∈ beforeRows machine rs q) :
    x = .row ∨ (∃ r op, x = .branch r op) ∨ x = .tick := by
  obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp hx
  exact row_classify machine rs p hp

private theorem first_occurrence {β : Type*} {b : β} {bs : List β} (hb : b ∈ bs) :
    ∃ pre post, bs = pre ++ b :: post ∧ b ∉ pre := by
  classical
  induction bs with
  | nil => simp at hb
  | cons a bs ih =>
    by_cases h : b = a
    · exact ⟨[],bs,by simp [h],by simp⟩
    obtain ⟨pre,post,eq,absent⟩ := ih ((List.mem_cons.mp hb).resolve_left h)
    exact ⟨a :: pre,post,by simp [eq],by simp [h,absent]⟩

private theorem post_non_tick (machine : TM.Rule A (Fin m) I) (rs post : List (I → A))
    (q : Fin m) :
    ∃ tag rest, post.flatMap (entryCode machine q) ++ afterRow machine rs q = tag :: rest ∧
      tag ≠ .tick := by
  cases post with
  | cons r l => exact ⟨_,_,rfl,by intro h; cases h⟩
  | nil =>
    unfold afterRow
    cases h : (List.finRange m).drop (q.val + 1) with
    | nil => exact ⟨_,_,rfl,by intro h; cases h⟩
    | cons l ls => exact ⟨_,_,rfl,by intro h; cases h⟩

/-- Scanning from the row marker finds the selected physical instruction. Its unary
destination is self-delimited even for the final branch of the final row. -/
theorem program_branch (machine : TM.Rule A (Fin m) I) (rs : List (I → A))
    (q : Fin m) (read : I → A) (hr : read ∈ rs) :
    ∃ skipped next rest,
      program machine rs = .origin :: (beforeRows machine rs q ++ .row ::
        (skipped ++ .branch read (commands (machine q read)) ::
          (List.replicate (target (machine q read)) .tick ++ next :: rest))) ∧
      (∀ x ∈ skipped, ¬ isBranchOf read x ∧ x ≠ .row ∧ x ≠ .origin ∧ x ≠ .endCode) ∧
      next ≠ .tick := by
  obtain ⟨pre,post,split,absent⟩ := first_occurrence hr
  obtain ⟨next,rest,tailEq,ne⟩ := post_non_tick machine rs post q
  refine ⟨pre.flatMap (entryCode machine q), next, rest, ?_, ?_, ne⟩
  · rw [program_row machine rs q]
    simp only [rowCode]
    rw [show rs.flatMap (entryCode machine q) =
        pre.flatMap (entryCode machine q) ++ entryCode machine q read ++
        post.flatMap (entryCode machine q) by simp [split,List.append_assoc]]
    simp only [entryCode, List.append_assoc, List.cons_append, tailEq]
  · intro x hx
    obtain ⟨r,hr',hx⟩ := List.mem_flatMap.mp hx
    have ne : r ≠ read := fun eq => absent (eq ▸ hr')
    rcases entry_classify machine q r hx with rfl | rfl <;> simp [isBranchOf,ne]

/-- The literal row address at which the next simulated instruction begins. -/
def rowAddress (machine : TM.Rule A (Fin m) I) (rs : List (I → A)) (q : Fin m) :=
  (beforeRows machine rs q).length + 1

theorem fetch_row (machine : TM.Rule A (Fin m) I) (rs : List (I → A)) (q : Fin m) :
    fetch (program machine rs) (rowAddress machine rs q) = .row := by
  rw [program_row machine rs q]
  simpa [rowAddress,rowCode,List.append_assoc] using
    (fetch_at_split (.origin :: beforeRows machine rs q)
      (rs.flatMap (entryCode machine q) ++ afterRow machine rs q) (.row : Tag A I))

/-- Read a cell inside a known consecutive segment of the ROM. -/
theorem fetch_inside (pre xs post : List (Tag A I)) (k : ℕ) (hk : k < xs.length) :
    fetch (pre ++ (xs ++ post)) (pre.length + k : ℕ) = xs[k] := by
  change ((pre ++ (xs ++ post))[pre.length+k]?).getD .endCode = xs[k]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hk, List.getElem?_eq_getElem hk]
  rfl

@[simp] theorem rowAddress_first (machine : TM.Rule A (Fin m) I) (rs : List (I → A))
    (hm : 0 < m) : rowAddress machine rs ⟨0,hm⟩ = 1 := by
  simp [rowAddress,beforeRows]

theorem fetch_origin (machine : TM.Rule A (Fin m) I) (rs : List (I → A)) :
    fetch (program machine rs) 0 = .origin := rfl

theorem fetch_no_origin (machine : TM.Rule A (Fin m) I) (rs : List (I → A)) (x : ℕ)
    (hx : 0 < x) : fetch (program machine rs) x ≠ .origin := by
  cases x with
  | zero => omega
  | succ x =>
    intro e
    change ((program machine rs).tail[x]?).getD .endCode = .origin at e
    cases hg : (program machine rs).tail[x]? with
    | none => simp [hg] at e
    | some c =>
      simp only [hg, Option.getD_some] at e
      subst c
      exact program_no_other_origin machine rs (List.mem_of_getElem? hg)

theorem rowAddress_le (machine : TM.Rule A (Fin m) I) (rs : List (I → A)) (q : Fin m) :
    rowAddress machine rs q ≤ (program machine rs).length := by
  rw [program_row machine rs q]
  simp [rowAddress]

/-- Exactly the branch tags and their unary payloads separate neighbouring row markers. -/
theorem rowAddress_next (machine : TM.Rule A (Fin m) I) (rs : List (I → A)) (q : Fin m)
    (hq : q.val + 1 < m) :
    rowAddress machine rs q < rowAddress machine rs ⟨q.val+1,hq⟩ ∧
      ∀ x : ℕ, rowAddress machine rs q < x → x < rowAddress machine rs ⟨q.val+1,hq⟩ →
        fetch (program machine rs) x ≠ .row := by
  let pre := Tag.origin :: beforeRows machine rs q
  let entries := rs.flatMap (entryCode machine q)
  have lo : pre.length = rowAddress machine rs q := rfl
  have hi : rowAddress machine rs ⟨q.val+1,hq⟩ = pre.length + 1 + entries.length := by
    have hlt : q.val < (List.finRange m).length := by simp
    have hget : (List.finRange m)[q.val] = q := Fin.ext (by simp)
    simp [rowAddress,beforeRows,List.take_succ_eq_append_getElem hlt,hget,
      pre,entries,rowCode,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rw [hi,← lo]
  refine ⟨by omega, ?_⟩
  intro x hl hr
  let k := x - (pre.length + 1)
  have hk : k < entries.length := by dsimp [k]; omega
  have atx := fetch_inside (pre ++ [.row]) entries (afterRow machine rs q) k hk
  have eq : program machine rs = (pre ++ [.row]) ++ (entries ++ afterRow machine rs q) := by
    simp [program_row machine rs q,pre,entries,rowCode,List.append_assoc]
  rw [eq, show x = (pre ++ [Tag.row]).length + k by simp [k]; omega, atx]
  obtain ⟨r,_,h⟩ := List.mem_flatMap.mp (show entries[k] ∈ rs.flatMap _ from List.getElem_mem hk)
  rcases entry_classify machine q r h with e | e <;> simp [e]

theorem fetch_branch (machine : TM.Rule A (Fin m) I) (rs : List (I → A))
    (q : Fin m) (read : I → A) (hr : read ∈ rs) :
    ∃ off : ℕ, let w := rowAddress machine rs q + off
      (∀ k < off, ¬ branchReads read (fetch (program machine rs) (rowAddress machine rs q + k : ℕ))) ∧
      fetch (program machine rs) w = .branch read (commands (machine q read)) ∧
      (∀ k < target (machine q read), fetch (program machine rs) (w+1+k : ℕ) = .tick) ∧
      fetch (program machine rs) (w+1+target (machine q read) : ℕ) ≠ .tick ∧
      w+1+target (machine q read) ≤ (program machine rs).length := by
  obtain ⟨skipped,next,rest,eq,skip,ne⟩ := program_branch machine rs q read hr
  let pre := Tag.origin :: beforeRows machine rs q
  let seen := Tag.row :: skipped
  let instr := Tag.branch read (commands (machine q read))
  let ticks := List.replicate (target (machine q read)) (Tag.tick : Tag A I)
  have eq' : program machine rs = pre ++ (seen ++ instr :: (ticks ++ next :: rest)) := by
    simpa [pre,seen,instr,ticks,List.append_assoc] using eq
  change ∃ off : ℕ, _
  refine ⟨seen.length, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have atx := fetch_inside pre seen (instr :: (ticks ++ next :: rest)) k hk
    rw [eq', show rowAddress machine rs q = pre.length from rfl, atx]
    have mem := List.getElem_mem hk
    rcases List.mem_cons.mp (show seen[k] ∈ Tag.row :: skipped from mem) with e | h
    · simp [e,branchReads]
    · intro hmatch
      apply (skip _ h).1
      cases e : seen[k] with
      | branch r op =>
        rw [e] at hmatch
        exact ⟨op, by rw [show r = read from hmatch]⟩
      | _ => rw [e] at hmatch; contradiction
  · rw [show rowAddress machine rs q = pre.length from rfl]
    change fetch (program machine rs) (pre.length + seen.length : ℕ) = instr
    simpa only [eq',← List.append_assoc,List.length_append] using
      (fetch_at_split (pre ++ seen) (ticks ++ next :: rest) instr)
  · intro k hk
    have hkt : k < ticks.length := by simpa [ticks] using hk
    let p := pre ++ seen ++ [instr]
    have hcode : program machine rs = p ++ (ticks ++ next :: rest) := by
      simp [eq',p,List.append_assoc]
    have hlen : rowAddress machine rs q + seen.length + 1 = p.length := by
      simp [p,pre,rowAddress]
      omega
    rw [hcode,hlen,fetch_inside p ticks _ k hkt]
    simp [ticks]
  · let p := pre ++ seen ++ [instr] ++ ticks
    have hcode : program machine rs = p ++ next :: rest := by simp [eq',p,List.append_assoc]
    have hlen : rowAddress machine rs q + seen.length + 1 + target (machine q read) = p.length := by
      simp [p,pre,rowAddress,ticks]
      omega
    rwa [hcode,hlen,fetch_at_split]
  · rw [eq']
    simp [rowAddress,pre,seen,ticks]
    omega

private theorem flatMap_length_le {α β : Type*} (xs : List α) (f : α → List β) (K : ℕ)
    (h : ∀ a, (f a).length ≤ K) : (xs.flatMap f).length ≤ xs.length * K := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add (h a) ih

/-- Every row has one marker and at most `m` symbols per branch. -/
theorem program_length_le (machine : TM.Rule A (Fin m) I) (rs : List (I → A)) :
    (program machine rs).length ≤ 2 + m * (1 + rs.length * m) := by
  have hb (q : Fin m) (r : I → A) : (entryCode machine q r).length ≤ m := by
    unfold entryCode target
    cases machine q r with
    | none =>
      have hm := q.isLt
      simp
      omega
    | some p => simp
  have hr (q : Fin m) : (rowCode machine rs q).length ≤ 1 + rs.length * m := by
    simpa [rowCode,Nat.add_comm] using Nat.add_le_add_left (flatMap_length_le rs _ m (hb q)) 1
  have := flatMap_length_le (List.finRange m) _ _ hr
  simp [program] at *
  omega

end Universal

end NearSquareRoot
end Computability
end OAI
