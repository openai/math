import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Code
import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Computability
import OAI.LinearAlgebra.MatrixExponent.Coloring.Matching
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Sort
import Batteries.Tactic.OpenPrivate
import OAI.LinearAlgebra.MatrixExponent.Coloring.Edges

universe u v

section
/-!
# Evaluation with materialized array results

Return an array view inside a pair so construction of its vector
precedes the closure for indexed reads, even after eta expansion.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Algorithm
variable {w : ℕ} {A D : Type}

private def run : {A D : Type} → Code w A D → A → D × Unit
  | _, _, .comp f g, x => run g (run f x).1
  | _, _, .pair f g, x => (((run f x).1, (run g x).1), ())
  | _, _, .tab _ f, x =>
    let a := Vector.ofFn (fun i => (run (f i) x).1)
    ((fun i => a[i.val]), ())
  | _, _, c, x => (c.eval x, ())

def evaluate (p : Code w A D) (x : A) : D := (run p x).1

theorem evaluate_eq (p : Code w A D) : evaluate p = p.eval := by
  induction p with
  | comp p q ip iq =>
    funext x
    change evaluate q (evaluate p x) = q.eval (p.eval x)
    rw [ip, iq]
  | pair p q ip iq =>
    funext x
    change (evaluate p x, evaluate q x) = (p.eval x, q.eval x)
    rw [ip, iq]
  | tab hh f ih =>
    funext x i
    change (Vector.ofFn (fun j => evaluate (f j) x))[i.val] =
      (Vector.ofFn (fun j => (f j).eval x))[i.val]
    simp only [ih]
  | _ => rfl

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-!
# Metered construction of immutable tables

A step count is instrumentation. A tabulation evaluates its row
procedure once per index and stores each returned value. A block
of 64 operations covers allocating a header, constructing a row,
adjusting loop indices, and writing the result and its address.
The subprocedure costs are added using the same materialized rows.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring

structure Work (A : Type u) where
  value : A
  steps : ℕ

def allowance (w : ℕ) := (100 + w) ^ 5

namespace Work
variable {A : Type u} {D : Type v} {h : ℕ}

@[noinline] def tab (f : B h → Work A) : Work (B h → A) :=
  let t := Vector.ofFn f
  ⟨fun i => t[i.val].value, 64 + ∑ i : B h, (64 + t[i.val].steps)⟩

theorem tab_value (f : B h → Work A) : (tab f).value = fun i => (f i).value := by
  funext i
  simp only [tab, Vector.getElem_ofFn]

theorem tab_steps (f : B h → Work A) : (tab f).steps = 64 + ∑ i, (64 + (f i).steps) := by
  simp only [tab, Vector.getElem_ofFn]

theorem tab_le (f : B h → Work A) (n : ℕ) (hh : ∀ i, (f i).steps ≤ n) :
    (tab f).steps ≤ 64 + 2 ^ h * (64 + n) := by
  rw [tab_steps]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _ : B h, (64 + n) := Finset.sum_le_sum fun i _ => Nat.add_le_add_left (hh i) 64
    _ = _ := by simp

end Work
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-! # Materialized tables with index-dependent entries -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Work
open Coloring

variable {h : ℕ} {A : B h → Type u}

private def row (f : ∀ i, Work (A i)) (i : B h) : Work (Sigma A) :=
  let r := f i
  ⟨⟨i, r.value⟩, r.steps⟩

private def unpack (s : Sigma A) (i : B h) (he : s.1 = i) : A i :=
  he ▸ s.2

private theorem unpack_eq (s : Sigma A) (i : B h) (x : A i) (he : s.1 = i)
    (hs : s = ⟨i, x⟩) : unpack s i he = x := by
  subst s
  rfl

/-- Each row stores its index beside the payload. Fetching erases the
index equality proof and uses the payload already in the table. -/
def dtab (f : ∀ i, Work (A i)) : Work (∀ i, A i) :=
  let t := tab (row f)
  have he (i : B h) : (t.value i).1 = i :=
    congrArg Sigma.fst (congrFun (tab_value (row f)) i)
  ⟨fun i => unpack (t.value i) i (he i), t.steps⟩

theorem dtab_value (f : ∀ i, Work (A i)) : (dtab f).value = fun i => (f i).value := by
  funext i
  exact unpack_eq _ _ _ _ (congrFun (tab_value (row f)) i)

theorem dtab_steps (f : ∀ i, Work (A i)) : (dtab f).steps = 64 + ∑ i, (64 + (f i).steps) :=
  tab_steps (row f)

theorem dtab_le (f : ∀ i, Work (A i)) (n : ℕ) (hh : ∀ i, (f i).steps ≤ n) :
    (dtab f).steps ≤ 64 + 2 ^ h * (64 + n) :=
  tab_le (row f) n hh

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Work
end

section
/-!
# Building word programs with separate construction and execution bounds

Each constructor charges 64 elementary word operations for its fixed
local work, including the opcode, field accesses and allocation.
Tabulation builds and meters each child once. Its setup charge includes
the opcode and its slot charge includes the child reference. Reusing a
child twice charges its construction twice. Weakening a bound changes
only a proof and leaves the built program and counter unchanged.

Ordinary literals and gate truth tables are supplied data.
`atCost` and `litCost` also charge for computing a static address.
The specification function and all proofs are erased.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring Algorithm

structure Builder (w : ℕ) {A D : Type} (f : A → D) (n : ℕ) where
  made : Work (Code w A D)
  runs : made.value.eval = f
  bound : made.value.time + 16 ≤ 32 * n
  built : made.steps + allowance w ≤ 128 * allowance w * n

namespace Builder
variable {w : ℕ}

abbrev code {A D : Type} {f : A → D} {n : ℕ} (p : Builder w f n) := p.made.value

private theorem reserve (w : ℕ) : 64 ≤ allowance w :=
  le_trans (by decide : 64 ≤ 100 ^ 5) (Nat.pow_le_pow_left (by omega) 5)

private theorem leaf {k : ℕ} (hk : k ≤ allowance w) :
    64 + k + allowance w ≤ 128 * allowance w * 1 := by
  have := reserve w
  omega

private theorem fixed (w : ℕ) : 64 + allowance w ≤ 128 * allowance w * 1 :=
  leaf (Nat.zero_le (allowance w))

def id {A} : Builder w (_root_.id : A → A) 1 :=
  ⟨⟨.id, 64⟩, rfl, le_rfl, fixed w⟩

def fst {A D} : Builder w (Prod.fst : A × D → A) 1 :=
  ⟨⟨.fst, 64⟩, rfl, le_rfl, fixed w⟩

def snd {A D} : Builder w (Prod.snd : A × D → D) 1 :=
  ⟨⟨.snd, 64⟩, rfl, le_rfl, fixed w⟩

def select {A} : Builder w (fun x : Bool × A × A => if x.1 then x.2.1 else x.2.2) 1 :=
  ⟨⟨.select, 64⟩, rfl, le_rfl, fixed w⟩

def «at» {A} {h : ℕ} (hh : h ≤ w) (i : B h) : Builder w (fun x : B h → A => x i) 1 :=
  ⟨⟨.at hh i, 64⟩, rfl, le_rfl, fixed w⟩

def read {A} {h : ℕ} (hh : h ≤ w) : Builder w (fun x : (B h → A) × B h => x.1 x.2) 1 :=
  ⟨⟨.read hh, 64⟩, rfl, le_rfl, fixed w⟩

def bit {A} (b : Bool) : Builder w (fun _ : A => b) 1 :=
  ⟨⟨.bit b, 64⟩, rfl, le_rfl, fixed w⟩

def lit {A} {h : ℕ} (hh : h ≤ w) (i : B h) : Builder w (fun _ : A => i) 1 :=
  ⟨⟨.lit hh i, 64⟩, rfl, le_rfl, fixed w⟩

def lt {h : ℕ} (hh : h ≤ w) : Builder w (fun x : B h × B h => decide (x.1 < x.2)) 1 :=
  ⟨⟨.lt hh, 64⟩, rfl, le_rfl, fixed w⟩

def eq {h : ℕ} (hh : h ≤ w) : Builder w (fun x : B h × B h => decide (x.1 = x.2)) 1 :=
  ⟨⟨.eq hh, 64⟩, rfl, le_rfl, fixed w⟩

def add {h : ℕ} (hh : h ≤ w) : Builder w (fun x : B h × B h => x.1 + x.2) 1 :=
  ⟨⟨.add hh, 64⟩, rfl, le_rfl, fixed w⟩

def resize {h k : ℕ} (hh : h ≤ w) (hk : k ≤ w) : Builder w (fun x : B h => Fin.ofNat (2 ^ k) x.val) 1 :=
  ⟨⟨.resize hh hk, 64⟩, rfl, le_rfl, fixed w⟩

def odd {h : ℕ} (hh : h ≤ w) : Builder w (fun x : B h => decide (x.val % 2 = 1)) 1 :=
  ⟨⟨.odd hh, 64⟩, rfl, le_rfl, fixed w⟩

def halve {h : ℕ} (hh : h ≤ w) : Builder w (fun x : B h =>
      (⟨x.val / 2, (Nat.div_le_self ..).trans_lt x.isLt⟩ : B h)) 1 :=
  ⟨⟨.halve hh, 64⟩, rfl, le_rfl, fixed w⟩

def atCost {A} {h : ℕ} (hh : h ≤ w) (i : Work (B h)) (hi : i.steps ≤ allowance w) :
    Builder w (fun x : B h → A => x i.value) 1 :=
  ⟨⟨.at hh i.value, 64 + i.steps⟩, rfl, le_rfl, leaf hi⟩

def litCost {A} {h : ℕ} (hh : h ≤ w) (i : Work (B h)) (hi : i.steps ≤ allowance w) :
    Builder w (fun _ : A => i.value) 1 :=
  ⟨⟨.lit hh i.value, 64 + i.steps⟩, rfl, le_rfl, leaf hi⟩

def gate (f : Bool × Bool → Bool) : Builder w f 1 where
  made := ⟨.gate (f (false, false)) (f (false, true)) (f (true, false)) (f (true, true)), 64⟩
  runs := by funext ⟨a, b⟩; cases a <;> cases b <;> rfl
  bound := le_rfl
  built := fixed w

variable {A D E : Type} {h k m n : ℕ} {f : A → D}

def mono (p : Builder w f m) (hm : m ≤ n) : Builder w f n :=
  ⟨p.made, p.runs, p.bound.trans (Nat.mul_le_mul_left 32 hm),
    p.built.trans (Nat.mul_le_mul_left _ hm)⟩

private theorem joinCost {x y : ℕ}
    (hx : x + allowance w ≤ 128 * allowance w * m)
    (hy : y + allowance w ≤ 128 * allowance w * n) :
    64 + x + y + allowance w ≤ 128 * allowance w * (m + n) := by
  have := reserve w
  rw [mul_add]
  omega

def comp {g : D → E} (p : Builder w f m) (q : Builder w g n) :
    Builder w (g ∘ f) (m + n) where
  made := ⟨p.code.comp q.code, 64 + p.made.steps + q.made.steps⟩
  runs := by change q.made.value.eval ∘ p.made.value.eval = _; rw [p.runs, q.runs]
  bound := by
    change 16 + p.made.value.time + q.made.value.time + 16 ≤ _
    have := p.bound
    have := q.bound
    omega
  built := joinCost p.built q.built

def pair {g : A → E} (p : Builder w f m) (q : Builder w g n) :
    Builder w (fun x => (f x, g x)) (m + n + 1) where
  made := ⟨p.code.pair q.code, 64 + p.made.steps + q.made.steps⟩
  runs := by change (fun x => (p.made.value.eval x, q.made.value.eval x)) = _; rw [p.runs, q.runs]
  bound := by
    change 16 + p.made.value.time + q.made.value.time + 16 ≤ _
    have := p.bound
    have := q.bound
    omega
  built := (joinCost p.built q.built).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))

def tab (hh : h ≤ w) (f : B h → A → D) (p : ∀ i, Builder w (f i) m) :
    Builder w (fun x i => f i x) (2 ^ h * (m + 1)) := by
  let a := Work.tab (fun i => (p i).made)
  have ha : a.value = fun i => (p i).made.value := Work.tab_value _
  refine ⟨⟨.tab hh a.value, a.steps⟩, ?_, ?_, ?_⟩
  · change (Code.tab hh a.value).eval = _
    rw [ha]
    funext x i
    change (Vector.ofFn (fun j => (p j).made.value.eval x))[i.val] = _
    rw [Vector.getElem_ofFn, (p i).runs]
  · change (Code.tab hh a.value).time + 16 ≤ _
    rw [ha]
    change 16 + (∑ i, (4 + (p i).made.value.time)) + 16 ≤ _
    have es : (∑ i, (4 + (p i).made.value.time)) ≤ 2 ^ h * (32 * m) := calc
      _ ≤ ∑ _i : B h, 32 * m := Finset.sum_le_sum (fun i _ => by have := (p i).bound; omega)
      _ = _ := by simp
    nlinarith only [es, Nat.two_pow_pos h]
  · change (Work.tab (fun i => (p i).made)).steps + allowance w ≤ _
    rw [Work.tab_steps]
    have := reserve w
    have es : (∑ i, (64 + (p i).made.steps)) ≤ 2 ^ h * (128 * allowance w * m) := calc
      _ ≤ ∑ _i : B h, 128 * allowance w * m :=
        Finset.sum_le_sum (fun i _ => by have := (p i).built; omega)
      _ = _ := by simp
    have hp := Nat.le_mul_of_pos_left (128 * allowance w) (Nat.two_pow_pos h)
    rw [show 128 * allowance w * (2 ^ h * (m + 1)) =
      2 ^ h * (128 * allowance w * m) + 2 ^ h * (128 * allowance w) by ring]
    omega

def keep {f : A → D} (h : Builder w f n) : Builder w (fun x => (x, f x)) (1 + n + 1) := Builder.id.pair h

def gather (hh : h ≤ w) (hk : k ≤ w) :
    Builder w (fun x : (B h → A) × (B k → B h) => x.1 ∘ x.2) (2 ^ k * 6) :=
  .tab hk _ (fun i => (Builder.fst.pair (Builder.snd.comp (.at hk i))).comp (.read hh))

end Builder
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-!
# Counting active dummy edges by a balanced tree

Each internal node adds two words modulo `2^(h+1)`. At the root the
unreduced sum is at most `2^h`, so comparing the two words compares the
exact counts. The generator halves the index domain at each step.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Builder
open Coloring Algorithm

variable {h w : ℕ}

private abbrev Masks (h : ℕ) := (B h → Bool) × (B h → Bool)

private def total {n : ℕ} (δ : B h → Bool) (b : Bool) (q : B n → B h)
    (x : Masks h) : B (h + 1) :=
  Fin.ofNat _ (∑ j, if δ (q j) = true ∧ x.1 (q j) = true ∧ x.2 (q j) = b then 1 else 0)

private theorem total_val (δ : B h → Bool) (b : Bool) (x : Masks h) :
    (total δ b _root_.id x).val =
      (Finset.univ.filter (fun i => δ i = true ∧ x.1 i = true ∧ x.2 i = b)).card := by
  unfold total
  simp only [id_eq, ← Finset.card_filter]
  apply Nat.mod_eq_of_lt
  refine (Finset.card_le_univ _).trans_lt ?_
  simp only [Fintype.card_fin, pow_succ]
  have := Nat.two_pow_pos h
  omega

/-- Numeration of one contiguous subarray. The recursion passes the
starting offset itself, so an individual load never walks a chain of
index maps. -/
private def span (h n off : ℕ) (i : B n) : B h := Fin.ofNat _ (i.val + off)

private theorem span_id : span h h 0 = _root_.id := by
  funext i
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

private def counter (hh : h + 1 ≤ w) (δ : B h → Bool) (b : Bool)
    (n off : ℕ) : Builder w (total δ b (span h n off)) (2 ^ n * 16 - 2) := by
  induction n generalizing off with
  | zero =>
    let i := span h 0 off 0
    have hr : h ≤ w := by omega
    let g : Builder w (fun x : Masks h => decide (δ i = true ∧ x.1 i = true ∧ x.2 i = b)) 6 :=
      ((fst.comp (.at hr i)).pair (snd.comp (.at hr i))).comp
        (.gate (fun y => decide (δ i = true ∧ y.1 = true ∧ y.2 = b)))
    let inc := (g.pair ((lit hh 1).pair (lit hh 0))).comp select
    have e : total δ b (span h 0 off) = fun x : Masks h =>
        if decide (δ i = true ∧ x.1 i = true ∧ x.2 i = b) then 1 else 0 := by
      funext x
      unfold total
      have single (f : B 0 → ℕ) : ∑ i, f i = f 0 := Fin.sum_univ_one f
      rw [single]
      simp only [i, decide_eq_true_eq]
      split <;> rfl
    rw [e]
    exact inc.mono (by decide)
  | succ n ih =>
    have left (j : B n) : span h (n + 1) off (halves n (.inl j)) = span h n off j := rfl
    have right (j : B n) : span h (n + 1) off (halves n (.inr j)) = span h n (2 ^ n + off) j := by
      unfold span
      congr 1
      change (2 ^ n + j.val) + off = _
      omega
    have e : total δ b (span h (n + 1) off) = fun x =>
        total δ b (span h n off) x + total δ b (span h n (2 ^ n + off)) x := by
      funext x
      unfold total
      rw [← (halves n).sum_comp, Fintype.sum_sum_type]
      simp only [left, right]
      exact Fin.ext (Nat.add_mod _ _ _)
    rw [e]
    refine (((ih off).pair (ih (2 ^ n + off))).comp (.add hh)).mono ?_
    have := Nat.two_pow_pos n
    rw [pow_succ]
    omega

def minority (hh : h + 1 ≤ w) (δ : B h → Bool) :
    Builder w (fun x : (B h → Bool) × (B h → Bool) => Coloring.minority δ x.1 x.2)
      (2 ^ h * (100 + w) ^ 10) := by
  let C := ((counter hh δ false h 0).pair (counter hh δ true h 0)).comp (.lt hh)
  let neg : Builder w (fun b : Bool => !b) 4 :=
    (Builder.id.pair Builder.id).comp (.gate (fun x => !x.1))
  have e : (fun x : Masks h => Coloring.minority δ x.1 x.2) =
      fun x => !(decide (total δ false (span h h 0) x < total δ true (span h h 0) x)) := by
    funext x
    rw [Bool.eq_iff_iff]
    simp [Coloring.minority, Fin.lt_def, span_id, total_val]
  rw [e]
  apply (C.comp neg).mono
  have M := (budget_step h w 0).trans (budget_mono h w (by decide : 1 ≤ 10))
  simp only [pow_zero, mul_one] at M
  have := Nat.two_pow_pos h
  omega

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Builder
end

section
/-!
# Uniform code for Batcher's comparator network

The pair-tree layouts agree with the RAM proof. Each recursive step
constructs its comparator or routing code along with its specification.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Builder

open Coloring

open private T build peek read_build decode read_decode from OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Sort

variable {α : Type} {a : Wire}
variable {w m r h k : ℕ}

/-- Carry one starting offset. A right turn adds one shifted unit,
and each leaf emits a single static load. -/
private def enter (hh : h ≤ w) (n off : ℕ) :
    Builder w (fun x : B h → α => build n (fun i => x (Fin.ofNat _ (i + off))))
      (2 ^ n * (1 + n)) := by
  induction n generalizing off with
  | zero => exact .at hh (Fin.ofNat _ (0 + off))
  | succ n ih =>
    have H := (ih off).pair (ih (2 ^ n + off))
    convert H.mono (n := 2 ^ (n + 1) * (1 + (n + 1))) ?_ using 1
    · funext x
      have e (i : ℕ) : (2 ^ n + i) + off = i + (2 ^ n + off) := by omega
      simp only [build, e]
    · have : 0 < 2 ^ n := by positivity
      ring_nf
      omega

private def exitEntry (n i : ℕ) : Builder w (fun x : T α n => peek n x i) (1 + n) := by
  induction n generalizing i with
  | zero => exact .id
  | succ n ih =>
    by_cases h : i < 2 ^ n
    · simp only [peek, ite_eq_left h]
      exact (fst.comp (ih i)).mono (by omega)
    · simp only [peek, ite_eq_right h]
      exact (snd.comp (ih (i - 2 ^ n))).mono (by omega)

private def both {β γ δ : Type} {f : α → β} {g : γ → δ} (hf : Builder w f m)
    (hg : Builder w g r) : Builder w (Prod.map f g) (m + r + 3) :=
  ((fst.comp hf).pair (snd.comp hg)).mono (by omega)

private def middle :
    Builder w (fun x : (α × α) × (α × α) => ((x.1.1, x.2.1), (x.1.2, x.2.2))) 11 :=
  ((fst.comp fst).pair (snd.comp fst)).pair ((fst.comp snd).pair (snd.comp snd))

private structure Models (e : Val a ≃ α) (n : ℕ) (f : Val (tree n a) → Val (tree n a))
    (w cost : ℕ) where
  run : T α n → T α n
  prog : Builder w run cost
  sound : ∀ x, run (decode e n x) = decode e n (f x)

private def revModels (e : Val a ≃ α) (n : ℕ) :
    Models e n (reverseTree n) w (2 ^ n * (4 * (1 + n))) := by
  induction n with
  | zero => exact ⟨_, Builder.id.mono (by decide), fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨f, hf, ef⟩ := ih
    refine ⟨_, ((snd.comp hf).pair (fst.comp hf)).mono ?_, fun x => ?_⟩
    · have : 0 < 2 ^ n := by positivity
      ring_nf
      omega
    · exact congrArg₂ Prod.mk (ef x.2) (ef x.1)

section
variable [LinearOrder (Val a)]

private def splitModels {e : Val a ≃ α} (he : Models e 1 (splitTree 0) w m) (n : ℕ) :
    Models e (n + 1) (splitTree n) w (2 ^ n * (m + 100 * n)) := by
  induction n with
  | zero => simpa using he
  | succ n ih =>
    obtain ⟨f, hf, ef⟩ := ih
    have hp := middle (α := T α n) (w := w)
    refine ⟨_, ((hp.comp (both hf hf)).comp hp).mono ?_, fun x => ?_⟩
    · have : 0 < 2 ^ n := by positivity
      ring_nf
      omega
    · let y : Val (tree (n + 1) a) := (x.1.1, x.2.1)
      let z : Val (tree (n + 1) a) := (x.1.2, x.2.2)
      exact congrArg₂ (fun (p q : T α (n + 1)) => ((p.1, q.1), (p.2, q.2))) (ef y) (ef z)

private def mergeModels {e : Val a ≃ α} (he : Models e 1 (splitTree 0) w m) (n : ℕ) :
    Models e n (mergeTree n) w (2 ^ n * (1 + n) ^ 2 * (m + 100)) := by
  induction n with
  | zero => exact ⟨_, Builder.id.mono (by simp), fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨f, hf, ef⟩ := ih
    obtain ⟨g, hg, eg⟩ := splitModels he n
    refine ⟨_, (hg.comp (both hf hf)).mono ?_, fun x => ?_⟩
    · have : 0 < 2 ^ n := by positivity
      ring_nf
      omega
    · rw [Function.comp_apply, eg]
      exact congrArg₂ Prod.mk (ef (splitTree n x).1) (ef (splitTree n x).2)

private def sortModels {e : Val a ≃ α} (he : Models e 1 (splitTree 0) w m) (n : ℕ) :
    Models e n (sortTree n) w (2 ^ n * (1 + n) ^ 3 * (m + 200)) := by
  induction n with
  | zero => exact ⟨_, Builder.id.mono (by simp), fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨f, hf, ef⟩ := ih
    obtain ⟨g, hg, eg⟩ := mergeModels he (n + 1)
    obtain ⟨v, hv, ev⟩ := revModels (w := w) e n
    refine ⟨_, ((both hf (hf.comp hv)).comp hg).mono ?_, fun x => ?_⟩
    · have : 0 < 2 ^ n := by positivity
      ring_nf
      omega
    · change g (f (decode e n x.1), v (f (decode e n x.2))) = _
      rw [ef, ef, ev]
      exact eg (sortTree n x.1, reverseTree n (sortTree n x.2))

end

section
variable [LinearOrder α]

private def exchange (cmp : Builder w (fun x : α × α => decide (x.1 < x.2)) m) :
    Builder w (fun x : α × α => (min x.1 x.2, max x.1 x.2)) (m + 7) := by
  have sw : Builder w (fun x : α × α => (x.2, x.1)) 3 := snd.pair fst
  have p := (cmp.pair (Builder.id.pair sw)).comp select
  convert p.mono (n := m + 7) (by omega) using 1
  funext ⟨x, y⟩
  by_cases h : x < y
  · simp [h, min_eq_left h.le, max_eq_right h.le]
  · simp [h, min_eq_right (le_of_not_gt h), max_eq_left (le_of_not_gt h)]

/-- The code equivalence transfers correctness on single records. No encoding or
decoding takes place in the program, which compares and moves whole records. -/
def sort (e : Val a ≃ α) (cmp : Builder w (fun x : α × α => decide (x.1 < x.2)) m)
    (hh : h ≤ w) :
    Builder w (fun x : B h → α => x ∘ Tuple.sort x) (2 ^ h * (100 + h) ^ 6 * (m + 1)) := by
  let ord := LinearOrder.lift' e e.injective
  have he : Models e 1 (splitTree 0) w (m + 7) := by
    refine ⟨_, exchange cmp, fun x => ?_⟩
    change (min (e x.1) (e x.2), max (e x.1) (e x.2)) =
      (e (min x.1 x.2), e (max x.1 x.2))
    rcases le_total x.1 x.2 with j | j
    · have j' : e x.1 ≤ e x.2 := j
      rw [min_eq_left j', max_eq_right j', min_eq_left j, max_eq_right j]
    · have j' : e x.2 ≤ e x.1 := j
      rw [min_eq_right j', max_eq_left j', min_eq_right j, max_eq_left j]
  obtain ⟨g, hg, eg⟩ := sortModels he h
  let idx := Fin.ofNat (2 ^ h)
  let fetch (v : T α h) (i : B h) := peek h v i
  have hout : Builder w fetch (2 ^ h * ((1 + h) + 1)) := .tab hh _ (fun i => exitEntry h i.val)
  have p := ((enter hh h 0).comp hg).comp hout
  have ok (x : B h → α) : fetch (g (build h (x ∘ idx))) = x ∘ Tuple.sort x := by
    obtain ⟨z, hz⟩ := (decode e h).surjective (build h (x ∘ idx))
    have src : fetch (decode e h z) = x := by
      funext i
      unfold fetch
      rw [hz, read_build _ _ _ i.isLt]
      simp [idx]
    rw [← hz, eg]
    apply List.ofFn_injective
    have ep (v : Val (tree h a)) : List.ofFn (fetch (decode e h v)) =
        (flatten h v).map e := read_decode e h v
    rw [ep]
    refine List.Perm.eq_of_pairwise' ?_ (Tuple.monotone_sort _).sortedLE_ofFn.pairwise ?_
    · exact List.pairwise_map.mpr (sortTree_sorted h z)
    · rw [← src]
      exact ((sortTree_perm h z).map e).trans
        ((ep z).symm ▸ (Equiv.Perm.ofFn_comp_perm ..).symm)
  change Builder w (fun x => fetch (g (build h (x ∘ idx)))) _ at p
  simp only [ok] at p
  exact p.mono (by ring_nf; omega)

end

private def lexLt {β : Type} [LinearOrder α] [LinearOrder β] {t : ℕ}
    (p : Builder w (fun x : α × α => decide (x.1 < x.2)) m)
    (q : Builder w (fun x : α × α => decide (x.1 = x.2)) r)
    (s : Builder w (fun x : β × β => decide (x.1 < x.2)) t) :
    Builder w (fun x : (α ×ₗ β) × (α ×ₗ β) => decide (x.1 < x.2)) (m + r + t + 19) := by
  let L := α ×ₗ β
  have a : Builder w (fun x : L × L => ((ofLex x.1).1, (ofLex x.2).1)) 5 :=
    (fst.comp fst).pair (snd.comp fst)
  have b : Builder w (fun x : L × L => ((ofLex x.1).2, (ofLex x.2).2)) 5 :=
    (fst.comp snd).pair (snd.comp snd)
  have u := ((a.comp q).pair (b.comp s)).comp (gate (fun x => x.1 && x.2))
  have v := ((a.comp p).pair u).comp (gate (fun x => x.1 || x.2))
  convert v.mono (n := m + r + t + 19) (by omega) using 1
  funext ⟨x, y⟩
  let i := ofLex x
  let j := ofLex y
  change decide (toLex i < toLex j) =
    (decide (i.1 < j.1) || decide (i.1 = j.1) && decide (i.2 < j.2))
  apply Bool.eq_iff_iff.mpr
  simp [Prod.Lex.toLex_lt_toLex]

/-- Record indices break ties in the key and recover the forward permutation. -/
def permutation (hh : h ≤ w) (hk : k ≤ w) :
    Builder w (fun x : (B h → B k) × (B h → Bool) => ⇑(Coloring.permutation x.1 x.2))
      (2 ^ h * (100 + w) ^ 20) := by
  let A := Bool ×ₗ (B k ×ₗ B h)
  let e : Val (.pair .bit (.pair (word k) (word h))) ≃ A :=
    (Equiv.refl Bool).prodCongr ((MatrixExponent.Control.index k).prodCongr (MatrixExponent.Control.index h))
  have cmp : Builder w (fun x : A × A => decide (x.1 < x.2)) 43 :=
    lexLt (.gate _) (.gate _) (lexLt (.lt hk) (.eq hk) (.lt hh))
  have key : Builder w (fun (x : (B h → B k) × (B h → Bool)) i =>
      toLex (!x.2 i, toLex (x.1 i, i))) (2 ^ h * 12) := by
    refine .tab (m := 11) hh _ (fun i => ?_)
    have neg : Builder w (fun x : Bool => !x) 4 := (Builder.id.pair Builder.id).comp (gate (fun p => !p.1))
    -- The first index pays for the two word layouts in the record
    -- equivalence, even if an implementation erases those layouts.
    let v : Work (B h) := ⟨i, if i.val = 0 then 64 * (k + h) else 0⟩
    have hv : v.steps ≤ allowance w := by
      have hv' : 64 * (k + h) ≤ (100 + w) ^ 2 := by nlinarith
      have := hv'.trans (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 5))
      unfold v allowance
      dsimp only
      split <;> omega
    exact ((snd.comp (.at hh i)).comp neg).pair ((fst.comp (.at hh i)).pair (litCost hh v hv))
  have out : Builder w (fun (x : B h → A) i => (ofLex (ofLex (x i)).2).2) (2 ^ h * 4) :=
    .tab hh _ (fun i => ((Builder.at hh i).comp snd).comp snd)
  refine ((key.comp (sort e cmp hh)).comp out).mono ?_
  calc
    _ ≤ 2 ^ h * (12 + (100 + w) ^ 6 * 44 + 4) := by
      rw [show 43 + 1 = 44 by decide, mul_add, mul_add, ← mul_assoc]
      gcongr
    _ ≤ 2 ^ h * (100 + w) ^ 7 := by
      apply Nat.mul_le_mul_left
      ring_nf
      omega
    _ ≤ _ := by gcongr; omega

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Builder
end

section
/-!
# Matching with an explicit enumeration of supported vertices

Only the first `size` dummy labels carry weight. Their order can be
chosen independently of the graph. The finite support is used in the
proof, and the program reads the size and labels directly.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring (B Regular degree join halve halves stock dummy perfect)
open private stock_join stock_uniform few_dummies from OAI.LinearAlgebra.MatrixExponent.Coloring.Matching

variable {h k : ℕ}

structure Reservation (k : ℕ) where
  size : ℕ
  assign : ℕ → B k
  unique : Set.InjOn assign (Set.Iio size)

def Reservation.support (S : Reservation k) := (Finset.range S.size).image S.assign

theorem Reservation.card_support (S : Reservation k) : S.support.card = S.size := by
  unfold support
  rw [Finset.card_image_of_injOn, Finset.card_range]
  simpa using S.unique

def dummyLabel (S : Reservation k) (i : B h) : B k := S.assign i.val

def weights (S : Reservation k) (d : ℕ) (x : B h → Bool) :=
  join (fun i => if x i then 2 ^ (h + 1) / d else 0)
    (fun i => if i.val < S.size then 2 ^ (h + 1) % d else 0)

def matching (S : Reservation k) (d : ℕ) (L R : B h → B k)
    (x : B h → Bool) (i : B h) : Bool :=
  let y := (halve (join L (dummyLabel S)) (join R (dummyLabel S)) (dummy h))^[h + 1]
    (weights S d x)
  decide (y (halves h (.inl i)) = 1)

private theorem dummy_degree (S : Reservation k) (hs : S.size ≤ 2 ^ h) (j : B k) :
    degree (dummyLabel (h := h) S) (fun i => decide (i.val < S.size)) j =
      if j ∈ S.support then 1 else 0 := by
  let P := Finset.univ.filter (fun i : B h => i.val < S.size ∧ S.assign i.val = j)
  suffices P.card = if j ∈ S.support then 1 else 0 by simpa [P, degree, dummyLabel] using this
  by_cases hj : j ∈ S.support
  · obtain ⟨u, hu, eu⟩ := Finset.mem_image.mp hj
    have ht := Finset.mem_range.mp hu
    let i : B h := ⟨u, ht.trans_le hs⟩
    have hp : P = {i} := by
      ext t
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hq, eq⟩
        exact Fin.ext (S.unique hq ht (eq.trans eu.symm))
      · rintro rfl
        exact ⟨ht, eu⟩
    simp [hp, hj]
  · have hp : P = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨ht, he⟩ := (Finset.mem_filter.mp hi).2
      exact hj (Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr ht, he⟩)
    simp [hp, hj]

variable {S : Reservation k} {d : ℕ} {L R : B h → B k} {x : B h → Bool}

private theorem regular_stock (hs : S.size ≤ 2 ^ h)
    (he : ∀ j, degree L x j = if j ∈ S.support then d else 0) (j : B k) :
    stock (join L (dummyLabel S)) (weights S d x) j = if j ∈ S.support then 2 ^ (h + 1) else 0 := by
  rw [stock_join]
  simp only [weights, join, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  have hg := stock_uniform (dummyLabel (h := h) S) (fun i => decide (i.val < S.size))
    (2 ^ (h + 1) % d) j
  simp only [decide_eq_true_eq, dummy_degree S hs] at hg
  rw [stock_uniform, he, hg]
  by_cases hj : j ∈ S.support
  · simp only [hj, ite_true, one_mul, Nat.div_add_mod]
  · simp [hj]

private theorem fewReserved (hd : 1 ≤ d) (hs : S.size * d ≤ 2 ^ h) :
    Coloring.dummyStock (dummy h) (weights S d x) < 2 ^ (h + 1) := by
  have hp := few_dummies (S := S.support) (x := x) hd (by rwa [S.card_support])
  simpa only [Coloring.weights, weights, S.card_support] using hp

theorem matching_spec (he : Regular S.support d L R x) (hd : 1 ≤ d) (hs : S.size * d ≤ 2 ^ h) :
    Regular S.support 1 L R (matching S d L R x) ∧ ∀ i, matching S d L R x i = true → x i = true := by
  have sz := (Nat.le_mul_of_pos_right _ hd).trans hs
  let y := (halve (join L (dummyLabel S)) (join R (dummyLabel S)) (dummy h))^[h + 1] (weights S d x)
  obtain ⟨hl, hr, hm, hz⟩ := perfect S.support (regular_stock sz he.1) (regular_stock sz he.2) (fewReserved hd hs)
  have hz' (i : B h) : y (halves h (.inr i)) = 0 := hz _ (by simp [dummy, join])
  let Y := matching S d L R x
  have hy (i) : Y i = true ↔ y (halves h (.inl i)) = 1 := decide_eq_true_iff
  have aux (p : B h → B k)
      (hp : ∀ j, stock (join p (dummyLabel S)) y j = if j ∈ S.support then 1 else 0) (j : B k) :
      degree p Y j = if j ∈ S.support then 1 else 0 := by
    let m (i) := y (halves h (.inl i))
    have hv (k) : stock p m k = if k ∈ S.support then 1 else 0 := by
      rw [← hp, stock_join]
      simp [stock, hz', m]
    have hunit : m = (fun i => if Y i then 1 else 0) := by
      funext i
      have hh : m i ≤ stock p m (p i) := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
      rw [hv] at hh
      simp only [hy]
      change m i = if m i = 1 then 1 else 0
      split_ifs at * <;> omega
    simpa [hunit, stock_uniform] using hv j
  refine ⟨⟨aux L hl, aux R hr⟩, fun i hi => ?_⟩
  have hc : y (halves h (.inl i)) ≤ weights S d x (halves h (.inl i)) := hm _
  rw [(hy i).mp hi] at hc
  by_contra e
  simp [weights, join, e] at hc

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-!
# Edge colouring with enumerated supports

Appending the split bit doubles the enumeration. Vertex number
`2*j+b` on the next level has label `2*assign j+b`.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring (B Regular double split nextEnd rest combine)
open private double_eq double_surj mem_enlarge Proper Regular.degree_pos
  remaining bisect merge_proper from OAI.LinearAlgebra.MatrixExponent.Coloring.Edges

variable {h k : ℕ}

def Reservation.enlarge (S : Reservation k) : Reservation (k + 1) where
  size := S.size * 2
  assign i := double (S.assign (i / 2)) (decide (i % 2 = 1))
  unique := by
    intro i hi j hj e
    obtain ⟨hu, hb⟩ := double_eq.mp e
    change i < S.size * 2 at hi
    change j < S.size * 2 at hj
    have hp : i / 2 = j / 2 := S.unique (show i / 2 < S.size by omega) (show j / 2 < S.size by omega) hu
    have : i % 2 = 1 ↔ j % 2 = 1 := by simpa using congrArg (· = true) hb
    omega

theorem Reservation.support_enlarge (S : Reservation k) :
    S.enlarge.support = Coloring.enlarge S.support := by
  ext t
  obtain ⟨u, b, rfl⟩ := double_surj t
  rw [mem_enlarge]
  simp only [support, Finset.mem_image, Finset.mem_range, enlarge, double_eq]
  constructor
  · rintro ⟨i, hi, he, _⟩
    exact ⟨i / 2, by omega, he⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨2 * j + b.toNat, ?_, ?_, ?_⟩
    · cases b <;> simp <;> omega
    · congr 1
      cases b <;> simp
      omega
    · cases b <;> simp

def retired (S : Reservation k) (d : ℕ) (L R : B h → B k) (x : B h → Bool) : B h → Bool :=
  if d % 2 = 0 then fun _ => false else matching S d L R x

def recurse {k : ℕ} (fuel : ℕ) (S : Reservation k) (d : ℕ) (L R : B h → B k)
    (x : B h → Bool) : B h → B h :=
  match fuel with
  | 0 => fun _ => 0
  | n + 1 =>
    let y := retired S d L R x
    let a := rest x y
    let b := split L R a
    let c := recurse n S.enlarge (d / 2) (nextEnd L b) (nextEnd R b) a
    fun i => combine d (y i) (b i) (c i)

def colours (S : Reservation k) (d : ℕ) (L R : B h → B k) (x : B h → Bool) : B h → B h :=
  recurse (h + 1) S d L R x

variable {S : Reservation k} {d : ℕ} {L R : B h → B k} {x : B h → Bool}

private theorem outgoing (he : Regular S.support d L R x) (hs : S.size * d ≤ 2 ^ h) :
    Regular S.support (d % 2) L R (retired S d L R x) ∧
      ∀ i, retired S d L R x i = true → x i = true := by
  by_cases hd : d % 2 = 0
  · simp [retired, hd, Regular, Coloring.degree]
  · rw [retired, ite_eq_right hd, show d % 2 = 1 by omega]
    exact matching_spec he (by omega) hs

private theorem proper (fuel : ℕ) (hd : d ≤ 2 ^ h) (hf : d < 2 ^ fuel)
    (hs : S.size * d ≤ 2 ^ h) (he : Regular S.support d L R x) :
    Proper d L R x (recurse fuel S d L R x) := by
  induction fuel generalizing k d x with
  | zero =>
    intro i hi
    have := Regular.degree_pos he hi
    simp only [pow_zero] at hf
    omega
  | succ fuel ih =>
    obtain ⟨hy, hsub⟩ := outgoing he hs
    have hr := bisect (remaining he hy hsub)
    rw [← S.support_enlarge] at hr
    have sz : S.enlarge.size * (d / 2) ≤ 2 ^ h := by
      change S.size * 2 * (d / 2) ≤ _
      rw [mul_assoc]
      exact (Nat.mul_le_mul_left _ (by omega : 2 * (d / 2) ≤ d)).trans hs
    rw [pow_succ] at hf
    have hp := ih (d := d / 2) (by omega) (by omega) sz hr
    rw [recurse]
    exact merge_proper hd hy hp

theorem edge_coloring {h k : ℕ} (S : Reservation k) (d : ℕ) (hd : d ≤ 2 ^ h)
    (hs : S.size * d ≤ 2 ^ h) (L R : B h → B k) (x : B h → Bool)
    (he : Regular S.support d L R x) :
    ∀ i, x i = true → (colours S d L R x i).val < d ∧
      ∀ j, x j = true → colours S d L R x i = colours S d L R x j →
        (L i = L j ∨ R i = R j) → i = j :=
  proper (h + 1) hd (by rw [pow_succ]; have := Nat.two_pow_pos h; omega) hs he

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end
