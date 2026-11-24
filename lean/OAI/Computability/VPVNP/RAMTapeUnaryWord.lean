import OAI.Computability.VPVNP.RAMTapeUnaryWordValue
import OAI.Computability.VPVNP.RAMTapeStacks
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Preparing the length and the unit as padded binary words

The input is a unary tally of the physical input length. A fixed control
allocates two words, adding a group of `p+1` zero bits to each word for every
mark and one further group. It sets the unit word's low bit and increments
the length word once for each saved mark. All data-dependent loops operate
on individual stack cells.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.UnaryWord

/-- Stacks for a unary source tally, pending increments, padded binary length and unit words,
and arithmetic scratch. -/
inductive Port where
  | src | pending | number | unit | tmp
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Control states for allocating both padded words, setting the unit bit, and counting the
saved unary marks into the length word. -/
inductive Phase (p : ℕ) where
  | alloc (remaining : Fin (p+2))
  | allocUnit (remaining : Fin (p+2))
  | next | save
  | unitHead | unitOne | count
  | add (carry : Bool) | emit (sum carry : Bool)
  | restore | put (b : Bool) | done
  deriving DecidableEq, Fintype

/-- Allocate padded zero words in groups of the parameter plus one bits, set the unit to one,
and increment the length word for each unary mark. -/
def code (p : ℕ) : StackCode Port (Phase p)
  | .alloc i => if h : i.val = 0 then .goto .next
    else .push .number false (.allocUnit ⟨i.val-1, by have := i.isLt; omega⟩)
  | .allocUnit i => .push .unit false (.alloc i)
  | .next => .pop .src fun b ↦ b.elim .unitHead (fun _ ↦ .save)
  | .save => .push .pending true (.alloc (Fin.last (p+1)))
  | .unitHead => .pop .unit (fun _ ↦ .unitOne)
  | .unitOne => .push .unit true .count
  | .count => .pop .pending fun b ↦ b.elim .done (fun _ ↦ .add true)
  | .add c => .pop .number fun b ↦ b.elim .restore (fun d ↦ .emit (d ^^ c) (d && c))
  | .emit b c => .push .tmp b (.add c)
  | .restore => .pop .tmp fun b ↦ b.elim .count .put
  | .put b => .push .number b .restore
  | .done => .halt true

/-- Assign the supplied bit lists to the source, pending, length, unit, and temporary stacks. -/
def store (src pending number unit tmp : List Bool) : Stacks Port
  | .src => src
  | .pending => pending
  | .number => number
  | .unit => unit
  | .tmp => tmp

private theorem update_store (s a x u t v : List Bool) (k : Port) :
    Function.update (store s a x u t) k v = match k with
      | .src => store v a x u t
      | .pending => store s v x u t
      | .number => store s a v u t
      | .unit => store s a x v t
      | .tmp => store s a x u v := by
  funext i
  cases k <;> cases i <;> simp [store]

local macro "unary_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [store, update_store, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none])

private abbrev ones (n : ℕ) := List.replicate n true
private abbrev zeros (n : ℕ) := List.replicate n false

private theorem alloc_run (p k : ℕ) (hk : k ≤ p+1) (s a x u : List Bool) :
    StackRuns (code p) (2*k+1) (.alloc ⟨k, by omega⟩) (store s a x u []) .next
      (store s a (zeros k ++ x) (zeros k ++ u) []) := by
  induction k generalizing x u with
  | zero => exact .cons (.goto (by simp [code])) (.nil ..)
  | succ k ih =>
    have hc : code p (.alloc ⟨k+1, by omega⟩) = .push .number false (.allocUnit ⟨k, by omega⟩) := by
      simp [code]
    simp only [Nat.mul_succ]
    refine .cons (.push hc) ?_
    simp only [store, update_store]
    unary_step
    simpa only [zeros, List.replicate_succ', List.append_assoc, List.singleton_append] using
      ih (by omega) (false :: x) (false :: u)

/-- Stack steps from the initial allocation to the instruction that sets the unit bit. -/
private def allocWork (p n : ℕ) := (n+1)*(2*(p+1)+1) + 2*n + 1

private theorem prepare_run (p n : ℕ) (a x u : List Bool) :
    StackRuns (code p) (allocWork p n) (.alloc (Fin.last (p+1))) (store (ones n) a x u [])
      .unitHead (store [] (ones n ++ a) (zeros ((p+1)*(n+1)) ++ x) (zeros ((p+1)*(n+1)) ++ u) []) := by
  induction n generalizing a x u with
  | zero =>
    have h := alloc_run p (p+1) le_rfl [] a x u
    have hnext : StackRuns (code p) 1 .next (store [] a (zeros (p+1) ++ x) (zeros (p+1) ++ u) [])
        .unitHead (store [] a (zeros (p+1) ++ x) (zeros (p+1) ++ u) []) := by
      unary_step
      exact .nil ..
    simpa [allocWork, ones, Fin.last] using h.trans hnext
  | succ n ih =>
    let x' := zeros (p+1) ++ x
    let u' := zeros (p+1) ++ u
    have h := alloc_run p (p+1) le_rfl (ones (n+1)) a x u
    have hsave : StackRuns (code p) 2 .next (store (true :: ones n) a x' u' [])
        (.alloc (Fin.last (p+1))) (store (ones n) (true :: a) x' u' []) := by
      unary_step
      unary_step
      exact .nil ..
    have htotal := (h.trans hsave).trans (ih (true :: a) x' u')
    have hc : (2*(p+1)+1 + 2) + allocWork p n = allocWork p (n+1) := by
      unfold allocWork
      ring
    rw [hc] at htotal
    simpa only [zeros, Nat.mul_succ (p+1) (n+1), List.replicate_add, List.append_assoc,
      ones, List.replicate_succ', List.singleton_append, x', u', Fin.last] using htotal

private theorem add_run (p : ℕ) (carry : Bool) (src pending x unit tmp : List Bool) :
    StackRuns (code p) (2*x.length+1) (.add carry) (store src pending x unit tmp) .restore
      (store src pending [] unit ((incScan carry x).1.reverse ++ tmp)) := by
  induction x generalizing carry tmp with
  | nil => unary_step; exact .nil ..
  | cons b x ih =>
    simp only [List.length_cons, Nat.mul_succ, incScan, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    unary_step
    unary_step
    exact ih (b && carry) ((b ^^ carry) :: tmp)

private theorem restore_run (p : ℕ) (src pending x unit tmp : List Bool) :
    StackRuns (code p) (2*tmp.length+1) .restore (store src pending x unit tmp)
      .count (store src pending (tmp.reverse ++ x) unit []) := by
  induction tmp generalizing x with
  | nil => unary_step; exact .nil ..
  | cons b tmp ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    unary_step
    unary_step
    exact ih (b :: x)

theorem count_run (p k : ℕ) (src x u : List Bool) (hfit : TapeWord.value x + k < 2^x.length) :
    ∃ result, result.length = x.length ∧ TapeWord.value result = TapeWord.value x + k ∧
      StackRuns (code p) (k*(4*x.length+3)+1) .count (store src (ones k) x u [])
        .done (store src [] result u []) := by
  induction k generalizing x with
  | zero =>
    refine ⟨x, rfl, (Nat.add_zero _).symm, ?_⟩
    simp only [Nat.zero_mul]
    unary_step
    exact .nil ..
  | succ k ih =>
    let y := (incScan true x).1
    have hlen : y.length = x.length := incScan_length ..
    have hval : TapeWord.value y = TapeWord.value x + 1 := incScan_value_of_lt _ _ (by
      simp only [Bool.toNat_true]
      omega)
    have hfit' : TapeWord.value y + k < 2^y.length := by rw [hlen, hval]; omega
    obtain ⟨r, hr, hv, htail⟩ := ih y hfit'
    refine ⟨r, hr.trans hlen, by omega, ?_⟩
    have ha := add_run p true src (ones k) x u []
    have hb := restore_run p src (ones k) [] u y.reverse
    simp only [List.append_nil] at ha
    simp only [List.length_reverse, List.reverse_reverse, List.append_nil, hlen] at hb
    rw [hlen] at htail
    rw [show (k+1)*(4*x.length+3)+1 = ((2*x.length+1)+(2*x.length+1)+(k*(4*x.length+3)+1))+1 by
      ring]
    change StackRuns _ _ _ (store src (true :: ones k) x u []) _ _
    unary_step
    exact (ha.trans hb).trans htail

/-- Enter the counting loop with an already allocated zero word. Each saved
mark increments that word. The source and unit stacks pass through intact. -/
theorem count_fixed (p w k : ℕ) (src unit : List Bool) (hk : k < 2^w) :
    StackRuns (code p) (k*(4*w+3)+1) .count
      (store src (List.replicate k true) (List.replicate w false) unit []) .done
      (store src [] (BurstRAM.wordBits (Fin.ofNat (2^w) k)) unit []) := by
  obtain ⟨z,hl,hv,h⟩ := count_run p k src (zeros w) unit (by simpa [zeros] using hk)
  simp only [zeros, List.length_replicate, zeros_value, Nat.zero_add] at hl hv h
  have hz : z = BurstRAM.wordBits (Fin.ofNat (2^w) k) :=
    TapeWord.eq_of_length_value (by simpa using hl)
      (by simpa [TapeWord.value_wordBits, Fin.val_ofNat, Nat.mod_eq_of_lt hk] using hv)
  simpa only [hz] using h

/-- Allocate the two words, set the unit's low bit, and scan both directions
through the length word once per input mark. -/
def work (p n : ℕ) : ℕ := allocWork p n + 2 + (n*(4*width p n+3)+1)

/-- The degree of the instruction bound is independent of the fixed
program parameter `p`. -/
theorem work_le (p n : ℕ) : work p n ≤ 12*(p+1)*(n+1)^2 := by
  simp only [work, allocWork, width]
  nlinarith only [Nat.zero_le (p*n), Nat.zero_le (p*n*n), Nat.zero_le (n*n), Nat.zero_le p, Nat.zero_le n]

/-- Starting with only the unary tally, prepare the two fixed-width words.
Their width, including all padding cells, is `(p+1)*(n+1)`. -/
theorem runs (p n : ℕ) :
    StackRuns (code p) (work p n) (.alloc (Fin.last (p+1))) (store (List.replicate n true) [] [] [] [])
      .done (store [] [] (BurstRAM.wordBits (inputWord p n)) (BurstRAM.wordBits (unitWord p n)) []) := by
  let W := width p n
  let u := BurstRAM.wordBits (unitWord p n)
  have hw : 0 < W := width_pos p n
  have hz : zeros W = false :: zeros (W-1) := by
    calc
      zeros W = zeros ((W-1)+1) := congrArg zeros (by omega)
      _ = _ := List.replicate_succ
  have hset : StackRuns (code p) 2 .unitHead (store [] (ones n) (zeros W) (zeros W) [])
      .count (store [] (ones n) (zeros W) u []) := by
    rw [show u = true :: zeros (W-1) from (unit_wordBits p n).symm]
    have h : StackRuns (code p) 2 .unitHead (store [] (ones n) (zeros W) (false :: zeros (W-1)) [])
        .count (store [] (ones n) (zeros W) (true :: zeros (W-1)) []) := by
      unary_step
      unary_step
      exact .nil ..
    simpa only [← hz] using h
  have hprep := prepare_run p n [] [] []
  simp only [List.append_nil] at hprep
  have hfit : TapeWord.value (zeros W) + n < 2 ^ (zeros W).length := by
    simpa [zeros, W] using (inputWord p n).isLt
  obtain ⟨r, hr, hv, hcount⟩ := count_run p n [] (zeros W) u hfit
  simp only [zeros, List.length_replicate, zeros_value, Nat.zero_add] at hr hv hcount
  have he : r = BurstRAM.wordBits (inputWord p n) :=
    TapeWord.eq_of_length_value (by simpa using hr) (by simpa [TapeWord.value_wordBits] using hv)
  rw [he] at hcount
  exact (hprep.trans hset).trans hcount

end RAMTape.UnaryWord

end VPVNP
end Computability
end OAI
