import OAI.Computability.NearSquareRoot.CRTPositionProgramPasses
import OAI.Computability.NearSquareRoot.CRTPositionProgramGates

/-! # Action of the serialized passes of a gathered XOR

The source is chunk two, the destination is chunk one and the residual positions
stay in place. Each destination index occurs in exactly one residue or singleton
pass. Missing and out-of-bounds reads disable the affected bit.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication IntegerMultiplication.Code PositionPreparation

variable {k n : ℕ}

private def port (n v : ℕ) : Option (Fin n) := if h : v < n then some ⟨v,h⟩ else none

private def readRow (tab : List Tally) (j : Fin n) : Option (Fin n) :=
  port n (Iter.pick (tally n) (tab,tally j.val)).length

private theorem read_normalized (t : ReadTable) (j : Fin n) :
    readRow (normalize (tally n,t)) j = decodePort t j := by
  simp only [readRow,normalize_value,Iter.pick,tally_length,List.headD_eq_head?_getD,
    List.head?_drop,List.getElem?_ofFn, j.isLt, ↓reduceDIte,Option.getD_some]
  cases h : decodePort t j with
  | none => simp [port]
  | some v => simp [port, v.isLt]

/-- A bit selector for the gathered source and destination chunks. -/
def gathered (read : Fin (k/3) → Option (Fin (k/3))) (w : Fin k → Bool) (x : Fin k) : Bool :=
  match threeChunksWithTail k x with
  | .inl (c,j) => if c = 1 then xorFrom read (chunkWord w 2) (chunkWord w 1) j else w x
  | .inr _ => w x

/-- Execute the packed or singleton XOR named by a pass descriptor. -/
def passAction (g : ℕ) (w : Fin k → Bool) : Op → Fin k → Bool
  | .inr (.inl (r,tab)) => gathered (fun j => if residuePass g j = r.length then readRow tab j else none) w
  | .inr (.inr (.inl (s,d))) => gathered (fun j => if j.val = d.length then port (k/3) s.length else none) w
  | _ => w

theorem passAction_packed (g r : ℕ) (t : ReadTable) (w : Fin k → Bool) :
    passAction g w (packed (tally r,normalize (tally (k/3),t))) =
      gathered (fun j => if residuePass g j = r then decodePort t j else none) w := by
  simp only [passAction,tally_length,read_normalized]

theorem passAction_readTable (g r : ℕ) (read : Fin (k/3) → Option (Fin (k/3))) (w : Fin k → Bool) :
    passAction g w (packed (tally r,List.ofFn fun j => tally (((read j).map Fin.val).getD (k/3)))) =
      gathered (fun j => if residuePass g j = r then read j else none) w := by
  simp only [passAction,tally_length]
  apply congrArg (fun f => gathered f w)
  funext j
  have e : readRow (List.ofFn fun i => tally (((read i).map Fin.val).getD (k/3))) j = read j := by
    simp only [readRow,Iter.pick,tally_length,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn,
      j.isLt,↓reduceDIte,Option.getD_some]
    cases h : read j with
    | none => simp [port]
    | some i => simp [port,i.isLt]
  simp only [e]

theorem passAction_highCnot (g : ℕ) (s d : Fin (k/3)) (w : Fin k → Bool) :
    passAction g w (highCnot (tally s.val,tally d.val)) =
      gathered (fun j => if j = d then some s else none) w := by
  simp only [passAction,tally_length,port,s.isLt,↓reduceDIte,Fin.mk_val,Fin.val_inj]

private theorem gathered_none (w : Fin k → Bool) : gathered (fun _ => none) w = w := by
  funext x
  obtain ⟨c,rfl⟩ := (threeChunksWithTail k).symm.surjective x
  cases c with
  | inl a =>
    obtain ⟨d,j⟩ := a
    by_cases e : d = 1 <;> simp [gathered,chunkWord,xorFrom,e]
  | inr a => simp [gathered]

private theorem highRead (n g r : ℕ) (hg : 0 < g) (hr : g ≤ r) (tab : List Tally) (j : Fin n) :
    let i := n - ((r-g)+1)
    let b := Iter.pick (tally n) (tab,tally i)
    (if r-g < n ∧ n < i + 2*g ∧ b.length < n then
       (if j.val=i then port n b.length else none) else none) =
      if residuePass g j = r then readRow tab j else none := by
  dsimp only
  let i := n - ((r-g)+1)
  let b := Iter.pick (tally n) (tab,tally i)
  change (if r-g < n ∧ n < i + 2*g ∧ b.length < n then
    (if j.val=i then port n b.length else none) else none) = _
  by_cases ej : residuePass g j = r
  · have high : ¬ j.val+2*g ≤ n := by
      intro e
      rw [residuePass, ite_eq_left e] at ej
      have hm := Nat.mod_lt j.val hg
      omega
    have eq : r = g+(n-1-j.val) := by simpa only [residuePass, ite_eq_right high] using ej.symm
    have ji : j.val = i := by dsimp [i]; omega
    have ir : r-g < n := by omega
    have upper : n < i + 2*g := by omega
    have read : readRow tab j = port n b.length := by simp only [readRow,b,ji]
    by_cases hh : b.length < n <;> simp [ej,ji,ir,upper,read,hh,port]
  · by_cases active : r-g < n ∧ n < i + 2*g ∧ b.length < n
    · have diff : j.val ≠ i := by
        intro he
        apply ej
        rw [residuePass,ite_eq_right (by omega)]
        dsimp [i] at he
        omega
      simp [ej,active,diff]
    · simp [ej,active]

private theorem pass_filtered (g r : ℕ) (hg : 0 < g) (tab : List Tally) (w : Fin k → Bool) :
    (pass ((tally (k/3),tally g,tab),tally r)).foldl (passAction g) w =
      gathered (fun j => if residuePass g j = r then readRow tab j else none) w := by
  rw [pass_value]
  by_cases er : r < g
  · simp [er,passAction]
  · simp only [ite_eq_right er]
    let n := k/3
    let i := n-((r-g)+1)
    let b := Iter.pick (tally n) (tab,tally i)
    have at_bit := highRead n g r hg (by omega) tab
    change List.foldl _ w (if r-g < n ∧ n < i + 2*g ∧ b.length < n then [highCnot (b,tally i)] else []) = _
    by_cases test : r-g < n ∧ n < i + 2*g ∧ b.length < n
    · rw [ite_eq_left test]
      simp only [List.foldl_cons,List.foldl_nil,passAction,tally_length]
      apply congrArg (fun read => gathered read w)
      funext j
      exact (ite_eq_left test).symm.trans (at_bit j)
    · rw [ite_eq_right test]
      change w = _
      calc
        w = gathered (fun _ => none) w := (gathered_none w).symm
        _ = _ := by
          apply congrArg (fun read => gathered read w)
          funext j
          exact (ite_eq_right test).symm.trans (at_bit j)

private theorem chunk_gathered (read : Fin (k/3) → Option (Fin (k/3))) (w : Fin k → Bool)
    (c : Fin 3) (j : Fin (k/3)) : chunkWord (gathered read w) c j =
      if c = 1 then xorFrom read (chunkWord w 2) (chunkWord w 1) j else chunkWord w c j := by
  simp only [chunkWord,gathered,Equiv.apply_symm_apply]

theorem gathered_twice (read : Fin (k/3) → Option (Fin (k/3))) (w : Fin k → Bool) :
    gathered read (gathered read w) = w := by
  funext x
  obtain ⟨a,rfl⟩ := (threeChunksWithTail k).symm.surjective x
  rcases a with ⟨c,j⟩ | j
  · by_cases e : c=1
    · subst c
      change gathered read (gathered read w) ((threeChunksWithTail k).symm (.inl (1,j))) = chunkWord w 1 j
      simp only [gathered,Equiv.apply_symm_apply,ite_true]
      cases h : read j <;> simp [xorFrom,h,chunk_gathered]
    · simp [gathered,e]
  · simp [gathered]

private theorem collect (g m : ℕ) (read : Fin (k/3) → Option (Fin (k/3))) (w : Fin k → Bool) :
    gathered (fun j => if residuePass g j = m then read j else none)
      (gathered (fun j => if residuePass g j < m then read j else none) w) =
    gathered (fun j => if residuePass g j < m+1 then read j else none) w := by
  funext x
  obtain ⟨a,rfl⟩ := (threeChunksWithTail k).symm.surjective x
  cases a with
  | inr v => simp [gathered]
  | inl z =>
    rcases z with ⟨c,j⟩
    by_cases ec : c=1
    · subst c
      simp only [gathered,Equiv.apply_symm_apply,ite_true]
      change xorFrom _ (chunkWord (gathered _ w) 2) (chunkWord (gathered _ w) 1) j = _
      by_cases er : residuePass g j = m
      · simp [xorFrom,er,chunk_gathered]
      · by_cases pre : residuePass g j < m
        · simp [xorFrom,er,pre,show residuePass g j < m+1 by omega,chunk_gathered]
        · simp [xorFrom,er,pre,show ¬ residuePass g j < m+1 by omega,chunk_gathered]
    · simp [gathered,ec]

/-- All generated passes realize the directed operation on the entire address word. -/
theorem passes_action (g : ℕ) (hg : 0 < g) (t : ReadTable) (w : Fin k → Bool) :
    (passes (tally (k/3),tally g,normalize (tally (k/3),t))).foldl (passAction g) w =
      directed (2,1,t) w := by
  let n := k/3
  let tab := normalize (tally n,t)
  have all (m : ℕ) : ((List.range m).flatMap (fun r => pass ((tally n,tally g,tab),tally r))).foldl
      (passAction g) w = gathered (fun j => if residuePass g j < m then readRow tab j else none) w := by
    induction m with
    | zero => simpa using (gathered_none w).symm
    | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.foldl_append, ih]
      simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
      rw [pass_filtered g m hg]
      exact collect g m (readRow tab) w
  rw [passes_range]
  change ((List.range (3*g)).flatMap (fun r => pass ((tally n,tally g,tab),tally r))).foldl _ _ = _
  rw [all]
  simp only [residuePass_lt hg, ite_true, tab, n, read_normalized]
  rfl

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
