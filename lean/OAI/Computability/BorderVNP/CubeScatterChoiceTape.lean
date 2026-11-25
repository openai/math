import OAI.Computability.BorderVNP.CubeISAOwnedTraceScan
import OAI.Computability.BorderVNP.CubeScatterDigits

/-! # Slicing one chronological guess tape into the private fields of an owned row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.ChoiceTape

open RoutingISA RoutingISA.Owned VPVNP.BurstRAM

/-- Consecutive bits of a tape, in execution order. -/
def segment (tape : ℕ → Bool) (start len : ℕ) := (List.range' start len).map tape

/-- Two consecutive slices of the same tape concatenate to the combined slice. -/
theorem segment_append (tape : ℕ → Bool) (start l k : ℕ) :
    segment tape start l ++ segment tape (start+l) k = segment tape start (l+k) := by
  simp only [segment,← List.map_append,List.range'_append_1]

/-- Zero-extended bits of an actual finite choice word. -/
def extend (xs : List Bool) (i : ℕ) := xs[i]?.getD false

/-- The extended tape and any finite slice starting at zero have a common continuation. -/
theorem compatible (xs : List Bool) (len : ℕ) :
    ∃ a b : List Bool, segment (extend xs) 0 len ++ a = xs ++ b := by
  have same : segment (extend xs) 0 xs.length = xs := by
    apply List.ext_getElem (by simp [segment])
    intro j _ hj
    simp [segment,extend,List.getElem?_eq_getElem hj]
  let last := max len xs.length
  refine ⟨segment (extend xs) (0+len) (last-len),segment (extend xs) (0+xs.length) (last-xs.length),?_⟩
  apply Eq.trans _ (congrArg (· ++ segment (extend xs) (0+xs.length) (last-xs.length)) same)
  rw [segment_append,segment_append]
  have h1 : len + (last-len) = last := Nat.add_sub_of_le (le_max_left ..)
  have h2 : xs.length + (last-xs.length) = last := Nat.add_sub_of_le (le_max_right ..)
  rw [h1,h2]

/-- Number of private choices consumed by a fixed digit table. -/
def privateCount : List Mode → ℕ
  | [] => 0
  | m::ms => (if m = .privateBit then 1 else 0) + privateCount ms

/-- Realize a digit table using successive tape bits only at its private positions. -/
def fill (tape : ℕ → Bool) : ℕ → List Mode → List Digit
  | _,[] => []
  | k,.selector::ms => .selector :: fill tape k ms
  | k,.crossing::ms => .crossing :: fill tape k ms
  | k,.unused::ms => .unused :: fill tape k ms
  | k,.privateBit::ms => .privateBit (tape k) :: fill tape (k+1) ms

/-- Filling a tape preserves every opcode and consumes exactly its predicted segment. -/
theorem fill_spec (tape : ℕ → Bool) (k : ℕ) (ms : List Mode) :
    (fill tape k ms).map Digit.mode = ms ∧ (fill tape k ms).flatMap Digit.choices = segment tape k (privateCount ms) := by
  induction ms generalizing k with
  | nil => simp [fill,privateCount,segment]
  | cons m ms ih =>
    cases m <;> simp [fill,privateCount,Digit.choices,Digit.mode,ih,segment,Nat.add_comm 1]
    rfl

/-- The starting tape offset for a trial. Unused finite indices contribute zero. -/
def offset {N : ℕ} (width : Fin N → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => offset width k + (if hk : k < N then width ⟨k,hk⟩ else 0)

/-- Concatenating all accepted trial slices produces precisely the initial tape word of their
total length. This includes all rejected trials as empty slices. -/
theorem row_segment {N : ℕ} (select : Fin N → Prop) [DecidablePred select] (bits : Fin N → List Bool)
    (width : Fin N → ℕ) (tape : ℕ → Bool)
    (h : ∀ t : Fin N, (if select t then bits t else []) = segment tape (offset width t.val) (width t)) :
    rowChoices select bits = segment tape 0 (offset width N) := by
  let chunk (j : ℕ) := if hj : j < N then (if select ⟨j,hj⟩ then bits ⟨j,hj⟩ else []) else []
  have loop (k : ℕ) (hk : k ≤ N) : (List.range k).flatMap chunk = segment tape 0 (offset width k) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hl : k < N := hk
      rw [List.range_succ,List.flatMap_append,ih hl.le]
      simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,chunk,hl,dite_true,h,offset]
      simpa only [Nat.zero_add] using segment_append tape 0 (offset width k) (width ⟨k,hl⟩)
  rw [← loop N le_rfl]
  unfold rowChoices
  rw [List.flatMap_def]
  apply congrArg List.flatten
  apply List.ext_getElem (by simp)
  intro j hj _
  have hl : j < N := by simpa using hj
  simp [chunk,hl]

end Cube.Scatter.ChoiceTape

end BorderVNP
end Computability
end OAI
