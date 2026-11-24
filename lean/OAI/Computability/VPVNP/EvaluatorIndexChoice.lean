import OAI.Computability.VPVNP.StructuredStackTotal
import OAI.Computability.VPVNP.RAMTapeWord
import Mathlib.Tactic.DeriveFintype

/-!
# A binary machine choice below an input bound

The evaluator guesses a basis index after each linear step. It also makes a
final choice below the prime-field residue. This finite-control routine consumes
the little-endian bits of the bound and guesses one bit for each. Comparing
successive, more significant bits requires only one bit of state. A successful
choice writes the guessed bits in big-endian order onto the output stack.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.IndexChoice

open RAMTape

/-- Finite control for a bounded binary guess. It retains the comparison with the bound as it
reads and writes successive bits. -/
inductive Phase where
  | read (less : Bool)
  | guess (less boundBit : Bool)
  | write (less guessBit : Bool)
  | finish (less : Bool)
  deriving DecidableEq, Fintype

private def nextLess (less guessBit boundBit : Bool) : Bool :=
  if guessBit = boundBit then less else boundBit

/-- Each bit takes a pop, a two-way choice and a push. A final pop and
comparison either return to the continuation or halt in rejection. -/
def guessBelow {K : Type*} (bound dest : K) : Routine K Phase where
  entry := .read false
  code
    | .read less => .pop bound fun b ↦ some (b.elim (.finish less) (.guess less))
    | .guess less b => .choose (some (.write (nextLess less false b) false))
        (some (.write (nextLess less true b) true))
    | .write less b => .push dest b (some (.read less))
    | .finish true => .goto none
    | .finish false => .halt false

private def below (less : Bool) (guess bound : List Bool) : Prop :=
  TapeWord.value guess < TapeWord.value bound ∨
    (TapeWord.value guess = TapeWord.value bound ∧ less = true)

private instance (less : Bool) (guess bound : List Bool) : Decidable (below less guess bound) :=
  inferInstanceAs (Decidable (_ ∨ _))

private theorem below_cons (less a b : Bool) (x y : List Bool) :
    below less (a :: x) (b :: y) ↔ below (nextLess less a b) x y := by
  cases less <;> cases a <;> cases b <;> simp [below, nextLess, TapeWord.value] <;> omega

variable {K : Type*} [DecidableEq K] (bound dest : K) (hne : bound ≠ dest)

/-- Replace the exhausted bound by the empty stack and prepend the guessed
bits, high bit first, to the destination. -/
def written (s : Stacks K) (bits : List Bool) : Stacks K :=
  Function.update (Function.update s bound []) dest (bits.reverse ++ s dest)

include hne in
private theorem written_step (s : Stacks K) (tail bits : List Bool) (b : Bool) :
    written bound dest (Function.update (Function.update s bound tail) dest (b :: s dest)) bits =
      written bound dest s (b :: bits) := by
  funext k
  by_cases hd : k = dest
  · subst k
    simp [written, List.append_assoc]
  · by_cases hb : k = bound
    · subst k
      simp [written, Function.update_of_ne hne]
    · simp [written, Function.update_of_ne, hd, hb]

include hne in
private theorem count_read (fuel : ℕ) (c : ℕ → Stacks K → ℕ) (less : Bool)
    (bs : List Bool) (s : Stacks K) (hs : s bound = bs) :
    (guessBelow bound dest).countFrom c (fuel + (3 * bs.length + 2)) (some (.read less)) s =
      ∑ f : Fin bs.length → Bool,
        if below less (List.ofFn f) bs then c fuel (written bound dest s (List.ofFn f)) else 0 := by
  induction bs generalizing less s with
  | nil =>
    have hup : Function.update s bound [] = s := by rw [← hs, Function.update_eq_self]
    cases less <;> simp [Routine.countFrom, guessBelow, hs, below, written, TapeWord.value, hup]
  | cons b bs ih =>
    let s' := Function.update s bound bs
    let out (a : Bool) := Function.update s' dest (a :: s dest)
    have hsrc (a) : out a bound = bs := by simp [out, s', Function.update_of_ne hne]
    have step (r : ℕ) :
        (guessBelow bound dest).countFrom c (r+3) (some (.read less)) s =
          (guessBelow bound dest).countFrom c r (some (.read (nextLess less false b))) (out false) +
          (guessBelow bound dest).countFrom c r (some (.read (nextLess less true b))) (out true) := by
      simp only [Routine.countFrom, guessBelow, hs, List.head?_cons, List.tail_cons, Option.elim_some]
      simp only [out, s', Function.update_of_ne hne.symm]
    rw [show fuel + (3 * (b :: bs).length + 2) = (fuel + (3 * bs.length + 2)) + 3 by
      simp only [List.length_cons]; omega, step, ih _ (out false) (hsrc false),
      ih _ (out true) (hsrc true)]
    let test (f : Fin (bs.length + 1) → Bool) :=
      if below less (List.ofFn f) (b :: bs) then c fuel (written bound dest s (List.ofFn f)) else 0
    change _ = ∑ f, test f
    rw [← (Fin.consEquiv (fun _ : Fin (bs.length + 1) ↦ Bool)).sum_comp test,
      Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
    simp only [Fin.consEquiv_apply, test, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, below_cons,
      out, s', written_step bound dest hne]

include hne in
/-- The continuation runs once per legal binary representation, at exactly
the same remaining fuel on all successful branches. -/
theorem count_guessBelow (c : ℕ → Stacks K → ℕ) (fuel : ℕ) (s : Stacks K) :
    (guessBelow bound dest).count c (fuel + (3 * (s bound).length + 2)) s =
      ∑ f : Fin (s bound).length → Bool,
        if TapeWord.value (List.ofFn f) < TapeWord.value (s bound) then
          c fuel (written bound dest s (List.ofFn f)) else 0 := by
  simpa only [Routine.count, guessBelow, below, Bool.false_eq_true, and_false, or_false] using
    count_read bound dest hne fuel c false (s bound) s rfl

include hne in
/-- With a bound encoded as one word, the integer count is the sum over the
legal index type. There are no duplicate representations or modulo aliases. -/
theorem count_guessBelow_fin {w : ℕ} (n : BurstRAM.Word w) (s : Stacks K)
    (hs : s bound = BurstRAM.wordBits n) (c : ℕ → Stacks K → ℕ) (fuel : ℕ) :
    (guessBelow bound dest).count c (fuel + (3*w + 2)) s =
      ∑ i : Fin n.val, c fuel (written bound dest s
        (BurstRAM.wordBits (Fin.castLE n.isLt.le i : BurstRAM.Word w))) := by
  classical
  let g (bs : List Bool) := if TapeWord.value bs < TapeWord.value (s bound) then
    c fuel (written bound dest s bs) else 0
  have hl : (s bound).length = w := hs ▸ BurstRAM.length_wordBits n
  have hr : ∀ m l : ℕ, m = l → (∑ x : Fin m → Bool, g (List.ofFn x)) =
      ∑ x : Fin l → Bool, g (List.ofFn x) := fun m _ h ↦ h ▸ rfl
  conv_lhs => rw [← hl, count_guessBelow bound dest hne]
  change (∑ x : Fin (s bound).length → Bool, g (List.ofFn x)) = _
  rw [hr _ _ hl, ← (RAMSerialization.wordBits w).sum_comp (fun x ↦ g (List.ofFn x))]
  dsimp only [g]
  rw [hs, TapeWord.value_wordBits]
  change (∑ i : BurstRAM.Word w, if TapeWord.value (BurstRAM.wordBits i) < n.val then
    c fuel (written bound dest s (BurstRAM.wordBits i)) else 0) = _
  rw [show (∑ i : BurstRAM.Word w, if TapeWord.value (BurstRAM.wordBits i) < n.val then
      c fuel (written bound dest s (BurstRAM.wordBits i)) else 0) =
    ∑ i : {i : BurstRAM.Word w // i.val < n.val}, c fuel (written bound dest s (BurstRAM.wordBits i.val)) by
      simp only [TapeWord.value_wordBits, ← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _]
  let e : Fin n.val ≃ {i : BurstRAM.Word w // i.val < n.val} :=
    { toFun := fun i ↦ ⟨Fin.castLE n.isLt.le i, i.isLt⟩
      invFun := fun i ↦ ⟨i.val.val, i.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact (e.sum_comp (fun i ↦ c fuel (written bound dest s (BurstRAM.wordBits i.val)))).symm

include hne in
/-- Returning with one successful leaf per legal final guess realizes the
representative of the prime-field residue as an integer path count. -/
theorem count_final_residue {w : ℕ} (n : BurstRAM.Word w) (s : Stacks K)
    (hs : s bound = BurstRAM.wordBits n) (fuel : ℕ) :
    (guessBelow bound dest).count (fun _ _ ↦ 1) (fuel + (3*w + 2)) s = n.val := by
  rw [count_guessBelow_fin bound dest hne n s hs]
  simp

include hne in
private theorem allStops_read (c : ℕ → Stacks K → Prop) (fuel : ℕ) (less : Bool)
    (bs : List Bool) (s : Stacks K) (hs : s bound = bs)
    (hc : ∀ xs : List Bool, xs.length = bs.length → below less xs bs →
      c fuel (written bound dest s xs)) :
    (guessBelow bound dest).AllStopsFrom c (fuel+(3*bs.length+2)) (some (.read less)) s := by
  induction bs generalizing less s with
  | nil =>
    have hup : Function.update s bound [] = s := by rw [← hs, Function.update_eq_self]
    cases less with
    | false => simp [Routine.AllStopsFrom, guessBelow, hs]
    | true =>
      have hv := hc [] rfl (by simp [below])
      simpa [Routine.AllStopsFrom, guessBelow, hs, written, hup] using hv
  | cons b bs ih =>
    let rest := Function.update s bound bs
    let out (a : Bool) := Function.update rest dest (a :: s dest)
    have hsrc (a) : out a bound = bs := by simp [out, rest, Function.update_of_ne hne]
    have recur (a : Bool) := ih (nextLess less a b) (out a) (hsrc a) (by
      intro xs hx hv
      simpa only [out, rest, written_step bound dest hne] using
        hc (a :: xs) (by simp [hx]) ((below_cons ..).mpr hv))
    rw [show fuel+(3*(b::bs).length+2) = (fuel+(3*bs.length+2))+3 by simp; omega]
    have step (r : ℕ) :
        (guessBelow bound dest).AllStopsFrom c (r+3) (some (.read less)) s ↔
        (guessBelow bound dest).AllStopsFrom c r (some (.read (nextLess less false b))) (out false) ∧
        (guessBelow bound dest).AllStopsFrom c r (some (.read (nextLess less true b))) (out true) := by
      simp only [Routine.AllStopsFrom, guessBelow, hs, List.head?_cons, List.tail_cons, Option.elim_some,
        out, rest, Function.update_of_ne hne.symm]
    exact (step _).mpr ⟨recur false, recur true⟩

include hne in
/-- Every nonrejecting branch returns a legal ordinal with the same residual
clock, while every illegal choice has already halted. -/
theorem allStops_guessBelow {w : ℕ} (n : BurstRAM.Word w) (s : Stacks K)
    (hs : s bound = BurstRAM.wordBits n) (c : ℕ → Stacks K → Prop) (fuel : ℕ)
    (hc : ∀ i : Fin n.val, c fuel (written bound dest s
      (BurstRAM.wordBits (Fin.castLE n.isLt.le i : BurstRAM.Word w)))) :
    (guessBelow bound dest).AllStops c (fuel+(3*w+2)) s := by
  have h := allStops_read bound dest hne c fuel false (BurstRAM.wordBits n) s hs (by
    intro xs hx hv
    rw [BurstRAM.length_wordBits] at hx
    have hh : TapeWord.value xs < n.val := by simpa [below, TapeWord.value_wordBits] using hv
    let i : Fin n.val := ⟨TapeWord.value xs, hh⟩
    have same : BurstRAM.wordBits (Fin.castLE n.isLt.le i : BurstRAM.Word w) = xs :=
      TapeWord.eq_of_length_value (by simp [hx]) (by simp [i, TapeWord.value_wordBits])
    simpa only [same] using hc i)
  simpa only [Routine.AllStops, guessBelow, BurstRAM.length_wordBits] using h

include hne in
private theorem stops_read (b : Bool) (bs : List Bool) (s : Stacks K)
    (hs : s bound = bs) (less : Bool) :
    StopsWithin ((guessBelow bound dest).close b) (3*bs.length+3) (some (.read less)) s := by
  induction bs generalizing s less with
  | nil => cases less <;> simp [StopsWithin, guessBelow, Routine.close, hs]
  | cons d ds ih =>
    let rest := Function.update s bound ds
    let out (a : Bool) := Function.update rest dest (a :: rest dest)
    have hsrc (a) : out a bound = ds := by simp [out, rest, Function.update_of_ne hne]
    have step (t : ℕ) : StopsWithin ((guessBelow bound dest).close b) (t+3) (some (.read less)) s ↔
        StopsWithin ((guessBelow bound dest).close b) t (some (.read (nextLess less false d))) (out false) ∧
        StopsWithin ((guessBelow bound dest).close b) t (some (.read (nextLess less true d))) (out true) := by
      simp only [StopsWithin, Routine.close, guessBelow, hs, List.head?_cons, List.tail_cons,
        Option.elim_some, out, rest]
    rw [show 3*(d::ds).length+3 = (3*ds.length+3)+3 by simp; omega, step]
    exact ⟨ih _ (hsrc false) _, ih _ (hsrc true) _⟩

include hne in
/-- Even illegal index guesses halt within the same linear instruction clock. -/
theorem guessBelow_stops (b : Bool) (s : Stacks K) :
    StopsWithin ((guessBelow bound dest).close b) (3*(s bound).length+3)
      (some (guessBelow bound dest).entry) s :=
  stops_read bound dest hne b (s bound) s rfl false

include hne in
/-- Close the returning routine as an accepting machine: its actual binary
branch tree has exactly the specified number of accepting leaves. -/
theorem final_residue_paths {w : ℕ} (n : BurstRAM.Word w) (s : Stacks K)
    (hs : s bound = BurstRAM.wordBits n) :
    stackPaths ((guessBelow bound dest).close true) (3*w+3)
      (some (guessBelow bound dest).entry) s = n.val := by
  rw [Routine.stackPaths_close]
  change (guessBelow bound dest).count _ _ s = _
  rw [show 3*w+3 = 1+(3*w+2) by omega,
    count_guessBelow_fin bound dest hne n s hs]
  simp

end Evaluator.IndexChoice

end VPVNP
end Computability
end OAI
