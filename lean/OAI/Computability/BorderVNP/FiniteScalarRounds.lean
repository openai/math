import OAI.Computability.BorderVNP.FiniteScalarCell
import OAI.Computability.BorderVNP.RoutingISACompactWriteBurst

/-! # One ordinary packed burst for all finite-field subtotals

The private scalar routine receives the same packed Boolean format already
written by the team RAM. Digits occur in bit-major order, so one full round
visits every scalar at a common binary place. The current base for each
position belongs to finite control and is squared when the round finishes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteScalarRounds

open TeamPrivateTape TeamPrivateValue RoutingISA
open scoped Classical BigOperators

/-- Field-position number, current bases at every position, and product so far. -/
structure Registers (k : ℕ) where
  /-- Scalar whose binary digit is being read. -/
  position : Fin k
  /-- Current power of each field element, encoded by its ordinal. -/
  bases : Fin k → Fin k
  /-- Accumulated field product, encoded by its ordinal. -/
  product : Fin k
  deriving DecidableEq, Fintype

/-- The routine expects either the next presence bit or the following data bit. -/
inductive Phase (k : ℕ) where
  | tag (r : Registers k)
  | data (r : Registers k)
  deriving DecidableEq, Fintype

variable (F : Type*) [Field F] [Fintype F]
/-- An ordinal in the fixed enumeration of the coefficient field. -/
abbrev Index (F : Type*) [Fintype F] := Fin (Fintype.card F)
private noncomputable abbrev number (a : F) := Fintype.equivFin F a
private noncomputable abbrev element (a : Index F) := (Fintype.equivFin F).symm a
private def zero : Index F := ⟨0,Fintype.card_pos⟩

/-- Encode mathematical field registers as finite control labels. -/
noncomputable def regs (i : Index F) (bases : Index F → F) (acc : F) : Registers (Fintype.card F) :=
  ⟨i,fun j => number F (bases j),number F acc⟩

/-- Visit the next scalar and square every current base on wraparound. -/
noncomputable def advance (r : Registers (Fintype.card F)) (bit : Bool) : Registers (Fintype.card F) :=
  let acc := element F r.product * (if bit then element F (r.bases r.position) else 1)
  if h : r.position.val+1 < Fintype.card F then ⟨⟨r.position.val+1,h⟩,r.bases,number F acc⟩
  else ⟨zero F,fun j => number F ((element F (r.bases j))^2),number F acc⟩

private def move (next : Phase (Fintype.card F)) (sym : Fin 1 → Option Bool) :
    TapeChoice (Phase (Fintype.card F)) (Option Bool) 1 := .one ⟨next,sym,fun _ => some true⟩

/-- The single fixed native table used at the scalar macro identifier. A terminator
in a partial round rejects, and the final padding of a packed RAM word is ignored. -/
noncomputable def table : TapeTable (Phase (Fintype.card F)) (Option Bool) 1
  | .tag r, sym => match sym 0 with
    | none => .halt false false
    | some false => .halt (decide (r.position.val = 0)) false
    | some true => move F (.data r) sym
  | .data r, sym => match sym 0 with
    | none => .halt false false
    | some b => move F (.tag (advance F r b)) sym

/-- The authentic return value in an accepting final control. -/
noncomputable def result : FieldSelect.Return (Phase (Fintype.card F)) (Option Bool) F 1
  | .tag r, _, _ => element F r.product
  | .data _, _, _ => 0

/-- A single three-symbol, one-tape private opcode computes all scalar classes. -/
noncomputable def routine : TeamSite.Macro (Phase (Fintype.card F)) (Option Bool) 1 (Fintype.card (Option Bool)) :=
  ⟨Alphabet.ofFintype none,some,0,table F,.tag (regs F (zero F) (element F) 1)⟩

/-- Claims on the real external bank in bit-major order. -/
def stream {d : ℕ} (c : Index F → Fin d → Bool) : List Bool :=
  (List.ofFn fun j : Fin d => List.ofFn fun i : Index F => c i j).flatten

omit [Field F] in
/-- The source interval for the ordinary compact writer has exactly one bit per
scalar and binary place. -/
theorem stream_length {d : ℕ} (c : Index F → Fin d → Bool) :
    (stream F c).length = d*Fintype.card F := by
  simp [stream,List.length_flatten,List.map_ofFn,Function.comp_def]

private noncomputable def partialRow (j : ℕ) (hj : j ≤ Fintype.card F) (values : Index F → F)
    (acc : F) (bits : Index F → Bool) : Registers (Fintype.card F) :=
  let total := acc * ∏ i : Fin j, if bits (i.castLE hj) then values (i.castLE hj) else 1
  if h : j < Fintype.card F then regs F ⟨j,h⟩ values total
  else regs F (zero F) (fun i => (values i)^2) total

private theorem fold_prefix (j : ℕ) (hj : j ≤ Fintype.card F) (values : Index F → F) (acc : F)
    (bits : Index F → Bool) :
    (List.ofFn fun i : Fin j => bits (i.castLE hj)).foldl (advance F) (regs F (zero F) values acc) =
      partialRow F j hj values acc bits := by
  induction j with
  | zero => simp [partialRow,zero, Fintype.card_pos]
  | succ j ih =>
    let hle : j ≤ Fintype.card F := by omega
    have hlt : j < Fintype.card F := by omega
    let i : Index F := ⟨j,hlt⟩
    let subtot := ∏ k : Fin j, if bits (k.castLE hle) then values (k.castLE hle) else 1
    rw [List.ofFn_succ',List.concat_eq_append,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change advance F ((List.ofFn fun z : Fin j => bits (z.castLE hle)).foldl (advance F) _) (bits i) = _
    rw [ih hle]
    unfold partialRow
    rw [dite_eq_left hlt,Fin.prod_univ_castSucc]
    change advance F (regs F i values (acc*subtot)) (bits i) =
      if h : j+1 < Fintype.card F then regs F ⟨j+1,h⟩ values (acc*(subtot*(if bits i then values i else 1)))
      else regs F (zero F) (fun z => (values z)^2) (acc*(subtot*(if bits i then values i else 1)))
    simp only [advance,regs,i,number,element,Equiv.symm_apply_apply,mul_assoc]

private theorem fold_line (values : Index F → F) (acc : F) (bs : Index F → Bool) :
    (List.ofFn bs).foldl (advance F) (regs F (zero F) values acc) =
      regs F (zero F) (fun i => values i^2) (acc * ∏ i, if bs i then values i else 1) := by
  simpa only [partialRow,lt_self_iff_false,dite_false,Fin.castLE_refl] using
    fold_prefix F (Fintype.card F) le_rfl values acc bs

/-- Processing a rectangular stream returns to the first scalar position. Every
reported little-endian count has contributed the indicated power, including zero bases. -/
theorem fold_stream {d : ℕ} (c : Index F → Fin d → Bool) (values : Index F → F) (acc : F) :
    (stream F c).foldl (advance F) (regs F (zero F) values acc) =
      regs F (zero F) (fun i => values i^(2^d))
        (acc*∏ i, values i ^ FieldPowers.digits (List.ofFn (c i))) := by
  induction d generalizing values acc with
  | zero => simp [stream,FieldPowers.digits]
  | succ d ih =>
    change (List.ofFn (fun j : Fin (d+1) => List.ofFn (fun i => c i j))).flatten.foldl _ _ = _
    rw [List.ofFn_succ,List.flatten_cons,List.foldl_append,fold_line]
    let tail (i : Index F) (j : Fin d) := c i j.succ
    change (stream F tail).foldl _ _ = _
    rw [ih]
    have ex (i : Index F) : values i ^ FieldPowers.digits (List.ofFn (c i)) =
        (if c i 0 then values i else 1) * (values i^2) ^ FieldPowers.digits (List.ofFn (tail i)) := by
      rw [List.ofFn_succ,FieldPowers.digits,pow_add,pow_mul]
      cases c i 0 <;> simp [tail]
    have sq (i) : (values i^2)^(2^d) = values i^(2^(d+1)) := by
      rw [←pow_mul,pow_succ (2:ℕ) d,Nat.mul_comm 2 (2^d)]
    simp only [ex,Finset.prod_mul_distrib,mul_assoc,sq]

private def view (left : List (Option Bool)) (xs : List Bool) : Fin 1 → SymbolTape (Option Bool) :=
  fun _ => ⟨left,(xs.map some).head?.getD none,(xs.map some).tail⟩

private theorem raw_read (bits pad choices : List Bool) (left : List (Option Bool)) (slack : ℕ)
    (r : Registers (Fintype.card F)) :
    let out := bits.foldl (advance F) r
    FieldSelect.nativeReturn (table F) none (result F) (2*bits.length+1+slack) (.tag r)
      (view left (CompactFrame.frameBits bits ++ pad)) choices =
      if out.position.val=0 ∧ choices.isEmpty then some (element F out.product) else none := by
  intro out
  induction bits generalizing r left with
  | nil =>
    rw [show 2*List.length ([] : List Bool)+1+slack = slack+1 by simp;omega]
    simp [out,FieldSelect.nativeReturn,CompactFrame.frameBits,CellMacro.FieldDecoder.frame,view,table,result]
  | cons b bs ih =>
    rw [show 2*(b::bs).length+1+slack = (2*bs.length+1+slack)+1+1 by simp;omega]
    simp only [FieldSelect.nativeReturn,CompactFrame.frameBits,CellMacro.FieldDecoder.frame,List.cons_append,
      view,List.map_cons,List.head?_cons,Option.getD_some,table,move]
    exact ih (some b::some true::left) (advance F r b)

/-- The native team routine reads the existing ISA writer's exact contiguous
word burst. On its only choice string it returns the field product of the claims. -/
theorem event_value {w d : ℕ} (hw : 0<w) (c : Index F → Fin d → Bool) (e : TeamRAM.Event w) (fuel : ℕ)
    (words : e.old = CompactFrame.pack w (stream F c)) (budget : 2*d*Fintype.card F < fuel) :
    FieldProcessor.returned (routine F) (result F) fuel e =
      if e.choices.isEmpty then some (∏ i, (Fintype.equivFin F).symm i ^ FieldPowers.digits (List.ofFn (c i))) else none := by
  let bs := stream F c
  have he : 2*bs.length+1 + (fuel-(2*bs.length+1)) = fuel := by
    dsimp only [bs]; rw [stream_length,←Nat.mul_assoc];omega
  have hx := CompactFrame.inputBits_pack hw bs
  let raw := CompactFrame.frameBits bs ++ List.replicate (CompactFrame.padding w bs) false
  have head : input none some (0 : Fin 1) raw = view [] raw := by funext i; simp [input,view,Subsingleton.elim i 0]
  unfold FieldProcessor.returned
  rw [words,hx,←he]
  change FieldSelect.nativeReturn (table F) none (result F) _ (.tag (regs F (zero F) (element F) 1)) (input none some 0 raw) e.choices = _
  rw [head,raw_read,fold_stream]
  simp [zero,regs,number,element]

private theorem bounded_view (fuel : ℕ) (q : Phase (Fintype.card F))
    (left : List (Option Bool)) (xs : List Bool) (fits : xs.length < fuel) :
    TapeStops (table F) none fuel q (view left xs) := by
  induction fuel generalizing q left xs with
  | zero => omega
  | succ f ih =>
    cases xs with
    | nil => cases q <;> simp [TapeStops,table,view]
    | cons x xs =>
      have bound : xs.length < f := by simpa using fits
      cases q with
      | tag r =>
        cases x with
        | false => simp [TapeStops,table,view]
        | true => exact ih (.data r) (some true::left) xs bound
      | data r => exact ih (.tag (advance F r x)) (some x::left) xs bound

/-- The private boundedness guard holds on every possible word burst as soon as
there is one native tick beyond its bit length. Malformed tables and incomplete
final rounds therefore cannot overrun the clock. -/
theorem bounded {w : ℕ} (vs : List (VPVNP.BurstRAM.Word w)) (fuel : ℕ) (fits : vs.length*w < fuel) :
    (routine F).bounded fuel vs := by
  let xs := TeamPrivateCall.inputBits vs
  have he : input none some (0 : Fin 1) xs = view [] xs := by funext i; simp [input,view,Subsingleton.elim i 0]
  change TapeStops (table F) none fuel (.tag _) (input none some 0 xs)
  rw [he]
  exact bounded_view F fuel _ [] xs (by simpa only [xs,TeamPrivateCall.inputBits_length] using fits)

end FiniteScalarRounds

end BorderVNP
end Computability
end OAI
