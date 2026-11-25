import OAI.Computability.NearSquareRoot.KernelComputableAddress
import Mathlib.Data.List.GetD
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! # Primitive-recursive natural-number representatives of modular matrices -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Raw

open Matrix KernelComputableAddress

abbrev Mat := ℕ → ℕ → ℕ

def read (cols : ℕ) (t : List ℕ) : Mat := fun r c => t.getD (r*cols+c) 0

def write (rows cols : ℕ) (f : Mat) : List ℕ :=
  (List.range (rows*cols)).map fun k => f (k/cols) (k%cols)

@[simp] theorem read_write {rows cols r c : ℕ} (f : Mat) (hr : r < rows) (hc : c < cols) :
    read cols (write rows cols f) r c = f r c := by
  have hn : r*cols+c < rows*cols := calc
    _ < (r+1)*cols := by simpa only [Nat.succ_mul] using Nat.add_lt_add_left hc (r*cols)
    _ ≤ _ := Nat.mul_le_mul_right cols hr
  rw [read, List.getD_eq_getElem _ _ (by simpa [write] using hn)]
  simp [write, Nat.mod_eq_of_lt hc]
  rw [Nat.mul_comm r cols, Nat.mul_add_div (by omega : 0 < cols), Nat.div_eq_of_lt hc, Nat.add_zero]

def add (f g : Mat) : Mat := fun i j => f i j + g i j
def neg (p : ℕ) (f : Mat) : Mat := fun i j => p+1 - f i j % (p+1)
def sub (p : ℕ) (f g : Mat) : Mat := add f (neg p g)
def scale (a : ℕ) (f : Mat) : Mat := fun i j => a * f i j
def ident : Mat := fun i j => if i = j then 1 else 0
def mult (n : ℕ) (f g : Mat) : Mat := fun i j => ∑ k ∈ Finset.range n, f i k * g k j
def powers (n : ℕ) (f : Mat) : ℕ → List ℕ
  | 0 => write n n ident
  | k+1 => write n n (mult n f (read n (powers n f k)))
def power (n : ℕ) (f : Mat) (o : ℕ) : Mat := read n (powers n f o)

/-- Interpretation of the in-range entries. -/
def interpret (p : ℕ) (a b : ℕ) (f : Mat) : Matrix (Fin a) (Fin b) (ZMod (p+1)) :=
  fun i j => (f i j : ZMod (p+1))

@[simp] theorem interpret_add (p a b : ℕ) (f g : Mat) :
    interpret p a b (add f g) = interpret p a b f + interpret p a b g := by
  ext i j; simp [interpret, add]

@[simp] theorem interpret_neg (p a b : ℕ) (f : Mat) :
    interpret p a b (neg p f) = -interpret p a b f := by
  ext i j
  have h := (Nat.mod_lt (f i j) (Nat.succ_pos p)).le
  simp [interpret, neg, Nat.cast_sub h, ZMod.natCast_mod]

@[simp] theorem interpret_sub (p a b : ℕ) (f g : Mat) :
    interpret p a b (sub p f g) = interpret p a b f - interpret p a b g := by
  rw [sub, interpret_add, interpret_neg, sub_eq_add_neg]

@[simp] theorem interpret_scale (p a b s : ℕ) (f : Mat) :
    interpret p a b (scale s f) = (s : ZMod (p+1)) • interpret p a b f := by
  ext i j; simp [interpret, scale]

@[simp] theorem interpret_ident (p n : ℕ) : interpret p n n ident = 1 := by
  ext i j; by_cases h : i = j <;> simp [interpret, ident, Matrix.one_apply, h, Fin.val_eq_val]

@[simp] theorem interpret_mult (p a b n : ℕ) (f g : Mat) :
    interpret p a b (mult n f g) = interpret p a n f * interpret p n b g := by
  ext i j
  simp only [interpret, mult, Nat.cast_sum, Nat.cast_mul, Matrix.mul_apply]
  exact (Fin.sum_univ_eq_sum_range (fun k => (f i k : ZMod (p+1)) * (g k j : ZMod (p+1))) n).symm

@[simp] theorem interpret_power (p n : ℕ) (f : Mat) (o : ℕ) :
    interpret p n n (power n f o) = (interpret p n n f) ^ o := by
  induction o with
  | zero =>
    rw [pow_zero, ← interpret_ident p n]
    ext i j; simp [interpret, power, powers, i.isLt, j.isLt]
  | succ o ih =>
    rw [pow_succ', ← ih, ← interpret_mult]
    ext i j; simp [interpret, power, powers, i.isLt, j.isLt]

variable {X Y : Type*} [Primcodable X] [Primcodable Y]

/-- Joint primitive recursiveness in the parameters and both coordinates. -/
def EntryPR (f : X → Mat) : Prop := Primrec fun a : X × ℕ × ℕ => f a.1 a.2.1 a.2.2

theorem EntryPR.eval {f : X → Mat} (h : EntryPR f) {x : Y → X} {i j : Y → ℕ}
    (hx : Primrec x) (hi : Primrec i) (hj : Primrec j) : Primrec fun y => f (x y) (i y) (j y) :=
  Primrec.comp h (hx.pair (hi.pair hj))

theorem EntryPR.pull {f : X → Mat} (h : EntryPR f) {u : Y → X} (hu : Primrec u) :
    EntryPR fun y => f (u y) :=
  h.eval (hu.comp .fst) (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)

theorem primrec_read {n : X → ℕ} {v : X → List ℕ} (hn : Primrec n) (hv : Primrec v) :
    EntryPR fun x => read (n x) (v x) :=
  (Primrec.list_getD 0).comp (hv.comp .fst) (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.fst.comp .snd) (hn.comp .fst)) (Primrec.snd.comp .snd))

theorem primrec_write {r c : X → ℕ} {f : X → Mat} (hr : Primrec r) (hc : Primrec c) (hf : EntryPR f) :
    Primrec fun x => write (r x) (c x) (f x) :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp hr hc))
    (hf.eval .fst (Primrec.nat_div.comp .snd (hc.comp .fst)) (Primrec.nat_mod.comp .snd (hc.comp .fst))).to₂

theorem EntryPR.add {f g : X → Mat} (hf : EntryPR f) (hg : EntryPR g) : EntryPR fun x => add (f x) (g x) :=
  Primrec.nat_add.comp hf hg

theorem EntryPR.neg {p : X → ℕ} {f : X → Mat} (hp : Primrec p) (hf : EntryPR f) :
    EntryPR fun x => neg (p x) (f x) :=
  let q := Primrec.succ.comp (hp.comp (Primrec.fst (α := X) (β := ℕ × ℕ)))
  Primrec.nat_sub.comp q (Primrec.nat_mod.comp hf q)

theorem EntryPR.sub {p : X → ℕ} {f g : X → Mat} (hp : Primrec p) (hf : EntryPR f) (hg : EntryPR g) :
    EntryPR fun x => sub (p x) (f x) (g x) := hf.add (EntryPR.neg hp hg)

theorem EntryPR.scale {a : X → ℕ} {f : X → Mat} (ha : Primrec a) (hf : EntryPR f) :
    EntryPR fun x => scale (a x) (f x) := Primrec.nat_mul.comp (ha.comp .fst) hf

theorem primrec_ident : EntryPR (fun _ : X => ident) :=
  Primrec.ite (Primrec.eq.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)) (.const 1) (.const 0)

theorem EntryPR.mult {n : X → ℕ} {f g : X → Mat} (hn : Primrec n) (hf : EntryPR f) (hg : EntryPR g) :
    EntryPR fun x => mult (n x) (f x) (g x) :=
  primrec_rangeSum (hn.comp .fst) (Primrec.nat_mul.comp
    (hf.eval (Primrec.fst.comp .fst) (Primrec.fst.comp (Primrec.snd.comp .fst)) .snd)
    (hg.eval (Primrec.fst.comp .fst) .snd (Primrec.snd.comp (Primrec.snd.comp .fst)))).to₂

theorem EntryPR.power {n o : X → ℕ} {f : X → Mat} (hn : Primrec n) (hf : EntryPR f) (ho : Primrec o) :
    EntryPR fun x => power (n x) (f x) (o x) := by
  apply primrec_read hn
  let step (x : X) (v : ℕ × List ℕ) := write (n x) (n x) (Raw.mult (n x) (f x) (read (n x) v.2))
  have hs : Primrec₂ step := (primrec_write (hn.comp .fst) (hn.comp .fst)
    (EntryPR.mult (hn.comp .fst) (hf.pull .fst) (primrec_read (hn.comp .fst) (Primrec.snd.comp .snd)))).to₂
  refine (Primrec.nat_rec' ho (primrec_write hn hn primrec_ident) hs).of_eq fun x => ?_
  generalize o x = k
  induction k with
  | zero => rfl
  | succ k ih => simp [step, ih, powers]

/-- Primitive recursive bounded universal quantification over a numerical range. -/
theorem bounded {n : X → ℕ} {P : X → ℕ → Prop} (hn : Primrec n)
    (hp : PrimrecPred (fun t : X × ℕ => P t.1 t.2)) : PrimrecPred (fun x => ∀ k < n x, P x k) := by
  have rel : PrimrecRel (fun k x => P x k) := (hp.comp (Primrec.snd.pair Primrec.fst)).primrecRel
  exact (rel.forall_mem_list.comp (Primrec.list_range.comp hn) Primrec.id).of_eq (by simp)

def equalMod (p rows cols : ℕ) (A B : Mat) : Prop :=
  ∀ i < rows, ∀ j < cols, A i j % (p+1) = B i j % (p+1)

instance (p rows cols : ℕ) (A B : Mat) : Decidable (equalMod p rows cols A B) :=
  inferInstanceAs (Decidable (∀ i < rows, ∀ j < cols, A i j % (p+1) = B i j % (p+1)))

theorem matches_iff (p rows cols : ℕ) (A B : Mat) :
    equalMod p rows cols A B ↔ interpret p rows cols A = interpret p rows cols B := by
  constructor
  · intro h
    ext i j
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (h i i.isLt j j.isLt)
  · intro h i hi j hj
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp
      (congrFun (congrFun h (⟨i, hi⟩ : Fin rows)) (⟨j, hj⟩ : Fin cols))

theorem primrec_matches {p rows cols : X → ℕ} {A B : X → Mat} (hp : Primrec p) (hr : Primrec rows)
    (hc : Primrec cols) (hA : EntryPR A) (hB : EntryPR B) :
    PrimrecPred fun x => equalMod (p x) (rows x) (cols x) (A x) (B x) := by
  apply bounded hr
  apply bounded (hc.comp .fst)
  let hs := Primrec.succ.comp (hp.comp (Primrec.fst.comp (Primrec.fst (α := X × ℕ) (β := ℕ))))
  exact Primrec.eq.comp (Primrec.nat_mod.comp (hA.eval (Primrec.fst.comp .fst) (Primrec.snd.comp .fst) .snd) hs)
    (Primrec.nat_mod.comp (hB.eval (Primrec.fst.comp .fst) (Primrec.snd.comp .fst) .snd) hs)

end InterchangeROMRepair.Raw

end NearSquareRoot
end Computability
end OAI
