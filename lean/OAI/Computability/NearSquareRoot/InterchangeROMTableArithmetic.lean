import OAI.Computability.NearSquareRoot.InterchangeROMTable
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul

/-! # Generating linear bank tables over a variable finite residue ring

The generator takes a modulus, an input arity and a matrix of natural numbers.
The resulting list of pairs is primitive recursive in all three arguments.
Physical letters are P192 tally trees; their entire truth table is generated from
the numerical matrix. Rectangular matrices and arity zero are included.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMTable

open IntegerMultiplication IntegerMultiplication.Code

variable {X : Type*} [Primcodable X]

theorem primrec_words {A : Type*} [Primcodable A] : Primrec₂ (@words A) := by
  let step (a : List A) (v : ℕ × List (List A)) :=
    a.flatMap fun k => v.2.map (k :: ·)
  have hs : Primrec₂ step := by
    change Primrec fun v : List A × (ℕ × List (List A)) => step v.1 v.2
    apply Primrec.list_flatMap Primrec.fst
    change Primrec fun v : (List A × (ℕ × List (List A))) × A => v.1.2.2.map (v.2 :: ·)
    apply Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  refine (Primrec.nat_rec (Primrec.const ([[]] : List (List A))) hs).of_eq ?_
  intro a n
  induction n with
  | zero => rfl
  | succ n ih =>
    exact congrArg (fun v => step a (n,v)) ih

/-- Sum of the first `n` coefficient products, padding short rows with zero. -/
def dot (c w : List ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => dot c w n + c.getD n 0 * w.getD n 0

theorem primrec_dot {c w : X → List ℕ} {n : X → ℕ}
    (hc : Primrec c) (hw : Primrec w) (hn : Primrec n) :
    Primrec fun x => dot (c x) (w x) (n x) := by
  let step (x : X) (v : ℕ × ℕ) := v.2 + (c x).getD v.1 0 * (w x).getD v.1 0
  have hs : Primrec₂ step := by
    change Primrec fun v : X × (ℕ × ℕ) => step v.1 v.2
    exact Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) <| Primrec.nat_mul.comp
      ((Primrec.list_getD 0).comp (hc.comp .fst) (Primrec.fst.comp Primrec.snd))
      ((Primrec.list_getD 0).comp (hw.comp .fst) (Primrec.fst.comp Primrec.snd))
  have he (x : X) (i : ℕ) : i.rec 0 (fun i s => step x (i,s)) = dot (c x) (w x) i := by
    induction i with
    | zero => rfl
    | succ i ih => exact congrArg (fun s => step x (i,s)) ih
  exact ((Primrec.nat_rec (Primrec.const 0) hs).comp Primrec.id hn).of_eq fun x => he x (n x)

/-- Both sides of a table row are ordinary lists of numeral residues. -/
def matrixRows (p n : ℕ) (matrix : List (List ℕ)) : List (List ℕ × List ℕ) :=
  (words (List.range p) n).map fun w => (w,matrix.map fun c => dot c w n % p)

theorem primrec_matrixRows {p n : X → ℕ} {matrix : X → List (List ℕ)}
    (hp : Primrec p) (hn : Primrec n) (hm : Primrec matrix) :
    Primrec (fun x => matrixRows (p x) (n x) (matrix x)) := by
  apply Primrec.list_map (primrec_words.comp (Primrec.list_range.comp hp) hn)
  change Primrec fun v : X × List ℕ => (v.2,(matrix v.1).map fun c => dot c v.2 (n v.1) % p v.1)
  apply Primrec.snd.pair
  apply Primrec.list_map (hm.comp Primrec.fst)
  change Primrec fun v : (X × List ℕ) × List ℕ => dot v.2 v.1.2 (n v.1.1) % p v.1.1
  exact Primrec.nat_mod.comp (primrec_dot Primrec.snd (Primrec.snd.comp Primrec.fst)
    (hn.comp (Primrec.fst.comp Primrec.fst))) (hp.comp (Primrec.fst.comp Primrec.fst))

def numeral (a : ℕ) : Tree := send (tally a)
def numeralWord := Task.forest numeral

def matrixTable (p n : ℕ) (matrix : List (List ℕ)) : List (Tree × Tree) :=
  (matrixRows p n matrix).map fun uv => (numeralWord uv.1, numeralWord uv.2)

theorem numeral_injective : Function.Injective numeral := by
  intro i j h
  have e := congrArg Tree.count h
  change size (tally i) = size (tally j) at e
  simpa [size_tally,tally] using e

private theorem dot_sum (c w : List ℕ) (n : ℕ) :
    dot c w n = ∑ i ∈ Finset.range n, c.getD i 0 * w.getD i 0 := by
  induction n with
  | zero => simp [dot]
  | succ n ih => simp [dot, ih, Finset.sum_range_succ]

/-- Natural entries of a row vector in increasing coordinate order. -/
def residues {p n : ℕ} (v : Fin n → ZMod p) : List ℕ := List.ofFn fun i => (v i).val

private theorem get_residues {p n : ℕ} (v : Fin n → ZMod p) (i : Fin n) :
    (residues v).getD i.val 0 = (v i).val := by
  simp [List.getD, residues]

theorem dot_mod {p n : ℕ} [NeZero p] (c w : Fin n → ZMod p) :
    dot (residues c) (residues w) n % p = (∑ i, c i * w i).val := by
  have hc : (dot (residues c) (residues w) n : ZMod p) = ∑ i, c i * w i := by
    rw [dot_sum, ← Fin.sum_univ_eq_sum_range]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [get_residues, get_residues, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  simpa only [ZMod.val_natCast] using congrArg ZMod.val hc

/-- The literal table used on tape realizes multiplication by the requested
matrix over the actual residue ring. -/
theorem matrixTable_correct {p m n : ℕ} [NeZero p]
    (M : Matrix (Fin m) (Fin n) (ZMod p)) (x : Fin n → ZMod p) :
    let t := matrixTable p n (List.ofFn fun i => residues (M i))
    let u := numeralWord (residues x)
    let v := numeralWord (residues (M.mulVec x))
    RegisterLookup.read t u = v ∧ (u,v) ∈ t := by
  have hw (a : ℕ) (h : a ∈ residues x) : a ∈ List.range p := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    exact List.mem_range.mpr (ZMod.val_lt _)
  have h := literal_correct (List.range p) n numeral numeral_injective
    (fun w => numeralWord ((List.ofFn fun i => residues (M i)).map fun c => dot c w n % p))
    (residues x) (by simp [residues]) hw
  simp only [List.map_ofFn,Function.comp_def,dot_mod] at h
  simpa only [matrixTable,matrixRows,List.map_map,literal,Function.comp_def,
    List.map_ofFn,residues,Matrix.mulVec,dotProduct,numeralWord] using h

end InterchangeROMTable

end NearSquareRoot
end Computability
end OAI
