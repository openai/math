import OAI.Computability.BorderVNP.FinitePrivateReturnTape
import OAI.Computability.BorderVNP.FiniteCellPower
import OAI.Computability.BorderVNP.TeamSitePrivate

/-! # Native field output from binary multiplicity reports

A single symbol tape scans little-endian exponents for the fixed list of field
elements. Each exponent digit is preceded by a one bit and each exponent ends
with a zero bit. The finite control squares its current base and accumulates
the product. Thus a single deterministic team private call can return the
field value even outside its prime subfield.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldScalar

open TeamPrivateTape TeamPrivateValue
open scoped BigOperators

/-- Control label for dispatching a fixed field position or scanning its exponent. -/
inductive State (k : ℕ) where
  | visit (remaining : Fin (k+1)) (acc : Fin k)
  | tag (idx base acc : Fin k)
  | bit (idx base acc : Fin k)
  deriving DecidableEq, Fintype

variable (F : Type*) [Field F] [Fintype F]
/-- An ordinal in the fixed enumeration of the coefficient field. -/
abbrev Index (F : Type*) [Fintype F] := Fin (Fintype.card F)
private noncomputable abbrev index (v : F) : Index F := Fintype.equivFin F v
private noncomputable abbrev val (i : Index F) : F := (Fintype.equivFin F).symm i

private def step (next : State (Fintype.card F)) (sym : Fin 1 → Option Bool) (right : Bool) :
    TapeChoice (State (Fintype.card F)) (Option Bool) 1 :=
  .one ⟨next,sym,fun _ => if right then some true else none⟩

/-- The finite native symbol table, with no private guesses. -/
noncomputable def table : TapeTable (State (Fintype.card F)) (Option Bool) 1
  | .visit j a, sym => if h : j.val = 0 then .halt true false else
      let i : Index F := ⟨j.val-1,by have := j.isLt; omega⟩
      step F (.tag i i a) sym false
  | .tag i b a, sym => match sym 0 with
    | none => .halt false false
    | some false => step F (.visit i.castSucc a) sym true
    | some true => step F (.bit i b a) sym true
  | .bit i b a, sym => match sym 0 with
    | none => .halt false false
    | some use => step F (.tag i (index F ((val F b)^2))
        (if use then index F (val F a * val F b) else a)) sym true

/-- Only a successful end of the field-position loop returns its accumulated scalar. -/
noncomputable def output : FieldSelect.Return (State (Fintype.card F)) (Option Bool) F 1
  | .visit _ a, _, _ => val F a
  | _, _, _ => 0

/-- The common fixed team private routine, with one input tape and three symbol tracks. -/
noncomputable def routine : TeamSite.Macro (State (Fintype.card F)) (Option Bool) 1 (Fintype.card (Option Bool)) :=
  ⟨Alphabet.ofFintype none,some,0,table F,.visit (Fin.last _) (index F 1)⟩

/-- Delimit all the digits of a single exponent; the resulting bits can be
concatenated and padded to whole addressed RAM words. -/
def encode : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: encode bs

/-- Exactly two payload bits per digit and one end marker. -/
theorem encode_length (bs : List Bool) : (encode bs).length = 2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [encode,ih]; omega

/-- Tape contents at the current input head. All already-scanned cells stay behind it. -/
private def view (left : List (Option Bool)) (xs : List Bool) : Fin 1 → SymbolTape (Option Bool) :=
  fun _ => ⟨left,(xs.map some).head?.getD none,(xs.map some).tail⟩

omit [Field F] in
private theorem stay_view (q : State (Fintype.card F)) (left : List (Option Bool)) (xs : List Bool) :
    (⟨q,fun i => (view left xs i).head,fun _ => none⟩ : TapeCommand _ _ _).apply none (view left xs) =
      view left xs := rfl

private theorem read_value (i : Index F) (bs extra : List Bool) (left : List (Option Bool))
    (a b : F) (fuel : ℕ) (choices : List Bool) :
    FieldSelect.nativeReturn (table F) none (output F) (2*bs.length+1+fuel) (.tag i (index F b) (index F a))
      (view left (encode bs ++ extra)) choices =
    FieldSelect.nativeReturn (table F) none (output F) fuel (.visit i.castSucc (index F (a*b^FieldPowers.digits bs)))
      (view ((encode bs).reverse.map some ++ left) extra) choices := by
  induction bs generalizing a b left with
  | nil =>
    rw [show 2*List.length ([] : List Bool)+1+fuel = fuel+1 by simp; omega]
    simp only [encode,List.cons_append,List.nil_append,FieldSelect.nativeReturn,table,view,step,List.map_cons,
      List.head?_cons,Option.getD_some,ite_true,FieldPowers.digits,pow_zero,mul_one,List.reverse_cons,
      List.reverse_nil,List.map_nil,List.nil_append]
    rfl
  | cons use bs ih =>
    rw [show 2*(use::bs).length+1+fuel = (2*bs.length+1+fuel)+1+1 by simp; omega]
    simp only [encode,List.cons_append,FieldSelect.nativeReturn,table,step,view,List.map_cons,List.head?_cons,
      Option.getD_some,ite_true,Equiv.symm_apply_apply]
    change FieldSelect.nativeReturn (table F) none (output F) (2*bs.length+1+fuel) (.tag i (index F (b^2)) (if use then index F (a*b) else index F a))
      (view (some use::some true::left) (encode bs++extra)) choices = _
    have power : (if use then a*b else a)*(b^2)^FieldPowers.digits bs = a*b^FieldPowers.digits (use::bs) := by
      cases use <;> simp [FieldPowers.digits,pow_add,pow_mul,mul_assoc]
    have lab : (if use then index F (a*b) else index F a) = index F (if use then a*b else a) := by cases use <;> rfl
    rw [lab,ih,power]
    simp only [List.reverse_cons,List.map_append,List.append_assoc]
    rfl

/-- Data and exact native time for a finite prefix of the field-position loop,
enumerated from the highest numbered position down. -/
def packet (counts : Index F → List Bool) : (j : ℕ) → j ≤ Fintype.card F → List Bool
  | 0, _ => []
  | j+1, h => encode (counts ⟨j,by omega⟩) ++ packet counts j (by omega)

private theorem visit_value (counts : Index F → List Bool) (j : ℕ) (hj : j ≤ Fintype.card F)
    (left : List (Option Bool)) (pad : List Bool) (a : F) (slack : ℕ) (choices : List Bool) :
    FieldSelect.nativeReturn (table F) none (output F) ((packet F counts j hj).length+j+1+slack)
      (.visit ⟨j,by omega⟩ (index F a)) (view left (packet F counts j hj ++ pad)) choices =
      if choices.isEmpty then some (a * ∏ i : Fin j, val F (i.castLE hj)^FieldPowers.digits (counts (i.castLE hj))) else none := by
  induction j generalizing a left with
  | zero =>
    simp only [packet,List.length_nil,zero_add,List.nil_append]
    rw [show 1+slack=slack+1 by omega]
    simp [FieldSelect.nativeReturn,table,output,index,val]
  | succ j ih =>
    let i : Index F := ⟨j,by omega⟩
    let prev : j ≤ Fintype.card F := by omega
    let bs := counts i
    let rest := packet F counts j prev
    let fuel := rest.length+j+1+slack
    change FieldSelect.nativeReturn (table F) none (output F) ((encode bs ++ rest).length+(j+1)+1+slack)
      (.visit i.succ (index F a)) (view left ((encode bs ++ rest)++pad)) choices = _
    rw [show (encode bs++rest).length+(j+1)+1+slack = (2*bs.length+1+fuel)+1 by rw [List.length_append,encode_length]; dsimp [fuel]; omega]
    simp only [FieldSelect.nativeReturn,table,Fin.val_succ,Nat.succ_ne_zero,dite_false,Nat.add_sub_cancel,
      step,Bool.false_eq_true,ite_false,stay_view,List.append_assoc,Fin.eta]
    rw [show i = index F (val F i) from ((Fintype.equivFin F).apply_symm_apply i).symm] at ⊢
    rw [read_value]
    simp only [index,val,Equiv.apply_symm_apply]
    change FieldSelect.nativeReturn (table F) none (output F) ((packet F counts j prev).length+j+1+slack)
      (.visit ⟨j,by omega⟩ (index F (a*val F i^FieldPowers.digits bs))) (view _ (packet F counts j prev++pad)) choices = _
    rw [ih,Fin.prod_univ_castSucc]
    by_cases hh : choices.isEmpty
    · simp only [hh,ite_true,Option.some.injEq]
      let z := ∏ k : Fin j, val F (k.castLE prev)^FieldPowers.digits (counts (k.castLE prev))
      change a * val F i ^ FieldPowers.digits bs * z = a * (z * val F i ^ FieldPowers.digits bs)
      rw [mul_assoc,mul_comm (val F i^FieldPowers.digits bs) z]
    · simp [hh]

/-- On its literal, whole-word-padded private input the field routine has one
choice string and returns the true product, in time linear in the payload. -/
theorem native_value (counts : Index F → List Bool) (pad : List Bool) (slack : ℕ) (choices : List Bool) :
    let raw := packet F counts (Fintype.card F) le_rfl
    FieldSelect.nativeReturn (routine F).table (routine F).alphabet.blank (output F)
      (raw.length+Fintype.card F+1+slack) (routine F).start (input none some 0 (raw++pad)) choices =
      if choices.isEmpty then some (∏ i, val F i ^ FieldPowers.digits (counts i)) else none := by
  intro raw
  have he : input none some (0 : Fin 1) (raw++pad) = view [] (raw++pad) := by
    funext i
    have hi : i=0 := Subsingleton.elim ..
    simp [input,view,hi]
  rw [he]
  have h := visit_value F counts (Fintype.card F) le_rfl [] pad 1 slack choices
  have idx : (⟨Fintype.card F,by omega⟩ : Fin (Fintype.card F+1)) = Fin.last _ := Fin.ext rfl
  rw [idx] at h
  simpa only [routine,Alphabet.ofFintype,raw,one_mul,Fin.castLE_refl] using h

/-- Number of class dispatch steps still possible. Each non-dispatch step
consumes one input bit or stops immediately at the blank. -/
def remaining {k : ℕ} : State k → ℕ
  | .visit j _ => j.val
  | .tag i _ _ | .bit i _ _ => i.val

private theorem bounded_view (fuel : ℕ) (q : State (Fintype.card F))
    (left : List (Option Bool)) (xs : List Bool) (budget : xs.length + remaining q < fuel) :
    TapeStops (table F) none fuel q (view left xs) := by
  induction fuel generalizing q left xs with
  | zero => omega
  | succ fuel ih =>
    cases q with
    | visit j a =>
      by_cases h : j.val = 0
      · simp [TapeStops,table,h]
      · simp only [TapeStops,table,h,dite_false,step,Bool.false_eq_true,ite_false,stay_view]
        apply ih
        simp only [remaining] at budget ⊢
        omega
    | tag i b a =>
      cases xs with
      | nil => simp [TapeStops,table,view]
      | cons x xs =>
        cases x <;> simp only [TapeStops,table,view,List.map_cons,List.head?_cons,Option.getD_some,
          step,ite_true] <;> apply ih _ (some _::left) xs <;> simp only [List.length_cons,remaining,Fin.val_castSucc] at budget ⊢ <;> omega
    | bit i b a =>
      cases xs with
      | nil => simp [TapeStops,table,view]
      | cons x xs =>
        simp only [TapeStops,table,view,List.map_cons,List.head?_cons,Option.getD_some,step,ite_true]
        apply ih _ (some x::left) xs
        simp only [List.length_cons,remaining] at budget ⊢
        omega

/-- Every raw input burst, including a malformed exponent record, halts within
one transition per input bit plus a fixed number of class dispatches. -/
theorem bounded {w : ℕ} (vs : List (VPVNP.BurstRAM.Word w)) (fuel : ℕ)
    (fits : (TeamPrivateCall.inputBits vs).length + Fintype.card F < fuel) :
    (routine F).bounded fuel vs := by
  let xs := TeamPrivateCall.inputBits vs
  have he : input none some (0 : Fin 1) xs = view [] xs := by
    funext i
    have hi : i=0 := Subsingleton.elim ..
    simp [input,view,hi]
  change TapeStops (table F) none fuel (.visit (Fin.last _) (index F 1)) (input none some 0 xs)
  rw [he]
  exact bounded_view F fuel _ [] xs fits

omit [Field F] in
/-- If every reported scalar count has the same bit width, the entire encoded
argument length is linear in that width at fixed field, even with zero scalars. -/
theorem packet_length (counts : Index F → List Bool) (w : ℕ) (h : ∀ i, (counts i).length = w) :
    ∀ j (hj : j ≤ Fintype.card F), (packet F counts j hj).length = j*(2*w+1) := by
  intro j
  induction j with
  | zero => intro _; simp [packet]
  | succ j ih => intro hj; rw [packet,List.length_append,encode_length,h,ih]; ring

end FieldScalar

end BorderVNP
end Computability
end OAI
