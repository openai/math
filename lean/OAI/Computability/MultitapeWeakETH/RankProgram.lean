import OAI.Computability.MultitapeWeakETH.FormulaRanks
import OAI.Computability.IntegerMultiplication.Code.Pace
import OAI.Computability.IntegerMultiplication.Code.Iter

/-! # Polynomial-time rank computation for bounded-length syntax keys -/

namespace OAI.Computability.MultitapeWeakETH.FormulaRanks

open IntegerMultiplication.Code

abbrev Key := List Tally

/-- Zero is the end marker, so each syntax integer is stored one larger. -/
def encodeKey (k : List ℕ) : Key := k.map (fun a => tally (a+1))

private def first (x : Key) : Tally := List.casesOn x [] fun a _ => a
private def rest (x : Key) : Key := List.casesOn x [] fun _ l => l

private def cmp : ℕ → Key × Key → Bool
  | 0, _ => false
  | d+1, (x,y) =>
    bif Iter.small (first x,first y) then true else
      bif Iter.small (first y,first x) then false else cmp d (rest x,rest y)

private theorem cmp_poly (d : ℕ) : Poly (cmp d) := by
  have headP : Easy first := Easy.listCase [] Easy.fst
  have tailP : Easy rest := Easy.listCase [] Easy.snd
  induction d with
  | zero => exact IntegerMultiplication.Code.Poly.const false
  | succ d ih =>
    have l := ((Easy.fst (Y:=Key)).compose headP).poly
    have r := ((Easy.snd (X:=Key)).compose headP).poly
    exact Poly.choose ((l.pair r).compose Iter.small_easy.poly) (IntegerMultiplication.Code.Poly.const true)
      (Poly.choose ((r.pair l).compose Iter.small_easy.poly) (IntegerMultiplication.Code.Poly.const false)
        (((Easy.fst.compose tailP).pair (Easy.snd.compose tailP)).poly.compose ih))

private theorem cmp_encode (d : ℕ) (x y : List ℕ) (hx : x.length ≤ d) (hy : y.length ≤ d) :
    cmp d (encodeKey x,encodeKey y) = decide (x < y) := by
  induction d generalizing x y with
  | zero =>
    have h := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hx)
    have h' := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hy)
    simp [h,h',cmp]
  | succ d ih =>
    cases x with
    | nil =>
      cases y with
      | nil => simpa [cmp,encodeKey,first,rest,Iter.small] using ih [] [] (by simp) (by simp)
      | cons b y => simp [cmp,encodeKey,first,Iter.small]
    | cons a x =>
      cases y with
      | nil => simp [cmp,encodeKey,first,Iter.small]
      | cons b y =>
        have tail := ih x y (by simpa using hx) (by simpa using hy)
        by_cases lt : a < b
        · simp [cmp,encodeKey,first,Iter.small,List.cons_lt_cons_iff,lt]
        by_cases gt : b < a
        · simp [cmp,encodeKey,first,Iter.small,List.cons_lt_cons_iff,lt,gt,ne_of_gt gt]
        obtain rfl : a=b := by omega
        simpa [cmp,encodeKey,first,rest,Iter.small] using tail

def sameKey (d : ℕ) (q : Key × Key) := !(cmp d q || cmp d q.swap)

theorem sameKey_poly (d : ℕ) : Poly (sameKey d) :=
  (((cmp_poly d).pair (Easy.exchange.poly.compose (cmp_poly d))).compose Iter.conn_easy.poly).compose Iter.negate.poly

theorem sameKey_encode (d : ℕ) (x y : List ℕ) (hx : x.length ≤ d) (hy : y.length ≤ d) :
    sameKey d (encodeKey x, encodeKey y) = decide (x = y) := by
  simp only [sameKey,Prod.swap,cmp_encode d x y hx hy,cmp_encode d y x hy hx]
  rcases lt_trichotomy x y with lt | rfl | gt
  · simp [lt,ne_of_lt lt]
  · simp
  · simp [gt,ne_of_gt gt]

def countKeys (d : ℕ) (q : Key × List Key) : Tally :=
  (q.2.map fun x => bif cmp d (x,q.1) then [()] else []).flatten

theorem countKeys_poly (d : ℕ) : Poly (countKeys d) := by
  have one := Poly.choose (Easy.exchange.poly.compose (cmp_poly d))
    (IntegerMultiplication.Code.Poly.const [()]) (IntegerMultiplication.Code.Poly.const ([] : Tally))
  exact (Poly.push [] [] one).compose Easy.flatten.poly

theorem countKeys_length (d : ℕ) (xs : List (List ℕ)) (a : List ℕ) (ha : a.length ≤ d)
    (lengths : ∀ x ∈ xs, x.length ≤ d) :
    (countKeys d (encodeKey a,xs.map encodeKey)).length = (xs.filter fun x => decide (x<a)).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have prev :=  ih fun y hy => lengths y (List.mem_cons_of_mem _ hy)
    have test := cmp_encode d x a (lengths _ List.mem_cons_self) ha
    by_cases lt : x < a <;> simpa [countKeys,test,lt,Nat.add_comm] using prev

theorem ordinal_program {α : Type} [Fintype α] (key : α ↪ List ℕ) (xs : List α)
    (unique : xs.Nodup) (all : ∀ x, x ∈ xs) (d : ℕ) (bounded : ∀ x, (key x).length ≤ d) (a : α) :
    (countKeys d (encodeKey (key a),(xs.map key).map encodeKey)).length = (ordinal key a).val := by
  rw [countKeys_length d _ _ (bounded a) (by simpa using fun x _ => bounded x),
    ordinal_val key xs unique all a]
  simp only [List.filter_map,Function.comp_def,List.length_map]

end OAI.Computability.MultitapeWeakETH.FormulaRanks
