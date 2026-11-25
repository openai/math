import OAI.Computability.BorderVNP.PackedSewnFragmentSource
import OAI.Computability.BorderVNP.FiniteSewnFieldStaging
import OAI.Computability.BorderVNP.PackedInheritedLayerEmit
import OAI.Computability.BorderVNP.PackedFrozenTapeSections

/-! # Immutable numeric records of the exterior sewing stage

Each positive maximal interval enables exactly one six-word clamp or nine-word
equality. Both possibilities read the same scalar bank. Old input positions
are relative to the work prefix and successor inputs follow the whole old site.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Sewn

open SewnField ParseBatchSort VPVNP.VerifierNetwork CellSparse
open private zero_value from OAI.Computability.BorderVNP.PackedCellAddressCircuit
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

/-- An interval ordinal and a choice of the clamp or equality record. -/
abbrev Row (n : ℕ) := Fin n × Bool
/-- A bit in one of the nine record words reserved at an interval ordinal. -/
abbrev Payload (n w : ℕ) := Fin n × Fin 9 × Fin w
/-- The fragment pins and the work and total-size words supplied for each interval. -/
abbrev Input (n w : ℕ) := Fragment.Pin n w ⊕ (Fin n × Bool × Fin w)

private def count (sourced : Bool) := if sourced then 9 else 6

private theorem count_le (b : Bool) : count b ≤ 9 := by cases b <;> decide

private def tags (b : Bool) := List.ofFn fun k : Fin (count b) => Layer.kind (k.castLE (count_le b))

/-- The two fixed row shapes at each interval ordinal share their physical nine-word bank. -/
def schema (n w : ℕ) : Schema (Row n) (Payload n w) where
  rows := (List.finRange n).flatMap fun i => [(i,false),(i,true)]
  tags r := tags r.2
  width _ := w
  pin r i j := (r.1,⟨i.val,by have h : i.val < (tags r.2).length := i.isLt; simp only [tags,List.length_ofFn] at h; exact h.trans_le (count_le _)⟩,j)

variable {n w : ℕ}

private def lit (a : ℕ) (j : Fin w) : Expr (Input n w) := .const (a.testBit (w-1-j.val))

private def raw (i : Fin n) (k : Fin 4) (j : Fin w) : Expr (Input n w) := .input (.inl (i,.inr (k,j)))

private def plus (i : Fin n) (b : Bool) (k : Fin 4) :=
  addWord (fun j : Fin w => (.input (.inr (i,b,j)) : Expr (Input n w))) (raw i k)

private def scalar (i : Fin n) (k : Fin 9) (j : Fin w) : Expr (Input n w) :=
  ![.and (.input (.inl (i,.inl true))) (lit 1 j),lit 1 j,raw i 2 j,plus i false 1 j,
    lit 0 j,lit 1 j,plus i true 3 j,lit 0 j,lit 1 j] k

private def expr : Pins (Row n) (Payload n w) w → Expr (Input n w)
  | .inl ((i,b),.inl ()) => .and (.input (.inl (i,.inl false))) (if b then .input (.inl (i,.inl true))
      else .not (.input (.inl (i,.inl true))))
  | .inl ((i,_),.inr j) => raw i 0 j
  | .inr (i,k,j) => scalar i k j

/-- The actual Boolean field emitter on the interval frame and the two looked-up prefix words. -/
noncomputable def frame (n w : ℕ) := (Frame.initial (id : Input n w → _)).step (expr (n:=n) (w:=w))

private theorem eval_expr (x : Input n w → Bool) (r) : (frame n w).eval x r = (expr r).eval x := by
  have hid : (Frame.initial (id : Input n w → _)).eval x = x := funext (Frame.initial_eval id x)
  simp only [frame,Frame.step_eval,hid]

private theorem plus_size (i : Fin n) (b : Bool) (k : Fin 4) (j : Fin w) :
    (plus i b k j).size ≤ 16*w+22 := sumWord_size_le false _ _ 1 (fun _ => le_rfl) (fun _ => le_rfl) _

/-- Every output has a direct bounded formula. Neither widths nor site capacities index gates. -/
theorem frame_size : (frame n w).size ≤ (2*n*(1+w)+9*n*w)*(16*w+22) := by
  have hb (r) : (expr (n:=n) (w:=w) r).size ≤ 16*w+22 := by
    rcases r with ⟨⟨i,b⟩,u | j⟩ | ⟨i,k,j⟩
    · cases u; cases b <;> simp [expr,StatementCircuit.Expr.size]
    · change 1 ≤ _; omega
    · fin_cases k <;> first | exact plus_size .. | (change 1 ≤ _; omega) | (change 3 ≤ _; omega)
  have h := Frame.step_size_le (Frame.initial (id : Input n w → _)) expr _ hb
  simpa only [frame,Frame.initial_size,zero_add,Pins,Row,Payload,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_bool,Fintype.card_unit,Nat.mul_comm 2 n,Nat.mul_comm 9 n,Nat.mul_assoc] using h

/-- The active slot has exactly the observed opcode. -/
theorem flag (x : Input n w → Bool) (i : Fin n) (b : Bool) :
    (frame n w).eval x (.inl ((i,b),.inl ())) = true ↔
      Fragment.active (x ∘ Sum.inl) i = true ∧ x (.inl (i,.inl true)) = b := by
  cases b <;> simp [eval_expr,expr,Fragment.active,StatementCircuit.Expr.eval]

/-- Both fixed opcode candidates carry the same actual physical site number. -/
theorem owner_eq (x : Input n w → Bool) (i : Fin n) (b : Bool) :
    owner ((frame n w).eval x) (i,b) = (Fragment.parse (x ∘ Sum.inl) i).site := by
  simp [owner,eval_expr,expr,raw,Fragment.parse,Fragment.parseRow,Fragment.word,StatementCircuit.Expr.eval]

private theorem raw_value (x : Input n w → Bool) (i : Fin n) (k : Fin 4) :
    wordValue x (raw i k) = Fragment.word (fun j => x (.inl (i,j))) k := rfl

private theorem lit_value (x : Input n w → Bool) (a : ℕ) (h : a < 2^w) : wordValue x (lit a) = a :=
  (ParseRecords.bigValue_testBit w a).trans (Nat.mod_eq_of_lt h)

private def baseWord (x : Input n w → Bool) (i : Fin n) (b : Bool) := value fun j => x (.inr (i,b,j))

private theorem plus_value (x : Input n w → Bool) (i : Fin n) (b : Bool) (k : Fin 4)
    (fit : baseWord x i b + Fragment.word (fun j => x (.inl (i,j))) k < 2^w) :
    wordValue x (plus i b k) = baseWord x i b + Fragment.word (fun j => x (.inl (i,j))) k :=
  addWord_value _ _ _ fit

private theorem scalar_values (x : Input n w → Bool) (i : Fin n) (s : Site)
    (hw : baseWord x i false = s.work) (he : baseWord x i true = s.size)
    (one : 1 < 2^w) (oldFit : s.work + Fragment.word (fun j => x (.inl (i,j))) 1 < 2^w)
    (newFit : x (.inl (i,.inl true)) = true → s.size + Fragment.word (fun j => x (.inl (i,j))) 3 < 2^w)
    (c : Fin 9) (valid : c.val < count (x (.inl (i,.inl true)))) :
    let z := Fragment.word fun j => x (.inl (i,j))
    value (fun j => (frame n w).eval x (.inr (i,c,j))) =
      ![Bool.toNat (x (.inl (i,.inl true))),1,z 2,s.work+z 1,0,1,s.size+z 3,0,1] c := by
  intro z
  simp only [eval_expr,expr]
  have old := plus_value x i false 1 (by rwa [hw])
  rw [hw] at old
  have h0 := lit_value x 0 (Nat.two_pow_pos _)
  have h1 := lit_value x 1 one
  have op : wordValue x (fun j => scalar i 0 j) = (x (.inl (i,.inl true))).toNat := by
    cases h : x (.inl (i,.inl true)) with
    | false => simpa only [wordValue,scalar,Matrix.cons_val_zero,StatementCircuit.Expr.eval,h,
        Bool.false_and,Bool.toNat_false] using (zero_value w)
    | true => simpa only [wordValue,scalar,Matrix.cons_val_zero,StatementCircuit.Expr.eval,h,
        Bool.true_and,Bool.toNat_true] using h1
  cases hs : x (.inl (i,.inl true)) with
  | false =>
    have hk : c.val < 6 := by simpa [hs,count] using valid
    fin_cases c <;> first | exact op.trans (congrArg Bool.toNat hs) | exact h0 | exact h1 | exact old | rfl | (exfalso; exact (by decide : ¬ (6:ℕ) < 6) hk)
  | true =>
    have new := plus_value x i true 3 (by rw [he]; exact newFit hs)
    rw [he] at new
    fin_cases c <;> first | exact op.trans (congrArg Bool.toNat hs) | exact h0 | exact h1 | exact old | exact new | rfl

private theorem canonical (b : Bool) (s : Site) (start wid new : ℕ) :
    List.ofFn (fun k : Fin (count b) =>
      (Layer.kind (k.castLE (count_le b)),![b.toNat,1,wid,s.work+start,0,1,s.size+new,0,1] (k.castLE (count_le b)))) =
      marked (Interval.record s ⟨start,wid,if b then some new else none⟩) := by cases b <;> rfl

/-- The immutable six or nine words and both address relocation positions describe the
actual selected interval of the retained site's input. Only a live source needs a fitting target. -/
theorem read (x : Input n w → Bool) (i : Fin n) (s : Site) (one : 1 < 2^w)
    (hw : value (fun j => x (.inr (i,false,j))) = s.work)
    (he : value (fun j => x (.inr (i,true,j))) = s.size)
    (oldFit : s.work + (Fragment.parse (x ∘ Sum.inl) i).run.oldStart < 2^w)
    (newFit : ∀ j ∈ (Fragment.parse (x ∘ Sum.inl) i).run.source, s.size+j < 2^w) :
    (schema n w).read ((frame n w).eval x) (i,x (.inl (i,.inl true))) =
      marked ((Fragment.parse (x ∘ Sum.inl) i).run.record s) := by
  let b := x (.inl (i,.inl true))
  let z := Fragment.word (fun j => x (.inl (i,j)))
  have target : b = true → s.size + z 3 < 2^w := by
    intro h
    apply newFit
    change z 3 ∈ (if b then some (z 3) else none)
    simp [h]
  change _ = marked (Interval.record s ⟨z 1,z 2,if b then some (z 3) else none⟩)
  rw [← canonical b s,Schema.read]
  apply List.ext_getElem
  · simp [schema,tags,b]
  · intro j hj hj'
    simp only [schema,List.getElem_ofFn,tags] at *
    have hlt : j < count b := by simpa using hj'
    let c : Fin 9 := ⟨j,hlt.trans_le (count_le b)⟩
    apply Prod.ext
    · change (List.ofFn _)[j]' _ = _
      rw [List.getElem_ofFn]
    · exact scalar_values x i s hw he one oldFit target c hlt

end Packing.Inherited.FrozenTape.Sewn

end BorderVNP
end Computability
end OAI
