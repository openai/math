import OAI.Computability.NearSquareRoot.InterchangeROMTableMask
import OAI.Computability.NearSquareRoot.InterchangeROMTableTagged

/-! # The three-way finite table for a spectral sweep

The head of a table key is the address comparison. The remaining two
entries are the ordinary residue and its value at the interchanged address.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.SweepTable

open IntegerMultiplication IntegerMultiplication.Code InterchangeROMTable GeneratorSyntax
open private comparisonMark_inj from OAI.Computability.NearSquareRoot.InterchangeROMTableMask

/-- The un-reduced natural numerator for the selected output. -/
def numerator (p half : ℕ) (inverse : Bool) (c : Fin 3) (x y : ℕ) : ℕ :=
  if c = 1 then x else
    (if inverse then half else 1) * ((if c = 2 then p+1 - x%(p+1) else x) + y)

theorem residue_eq (p half : ℕ) (inverse : Bool) (tag : Ordering) (x y : ZMod (p+1)) :
    numerator p half inverse (comparisonCode tag) x.val y.val % (p+1) =
      (InterchangeSpectralStep.value inverse (half : ZMod (p+1)) tag x y).val := by
  have leq : x.val ≤ p+1 := (ZMod.val_lt _).le
  have modulus : ((p+1 : ℕ) : ZMod (p+1)) = 0 := ZMod.natCast_self _
  have negx : ((p+1 - x.val%(p+1) : ℕ) : ZMod (p+1)) = -x := by
    rw [Nat.mod_eq_of_lt (ZMod.val_lt _),Nat.cast_sub leq,modulus,ZMod.natCast_zmod_val,zero_sub]
  rw [← ZMod.val_natCast]
  apply congrArg ZMod.val
  cases tag <;> cases inverse <;>
    simp [numerator,comparisonCode,InterchangeSpectralStep.value,negx] <;> ring

/-- The signed word table for one spectral pass. -/
def table (p half : ℕ) (inverse : Bool) : List (Tree × Tree) :=
  tagged ([0,1,2] : List (Fin 3)) comparisonMark fun c =>
    literal (List.range (p+1)) 2 numeral fun w =>
      numeralWord [numerator p half inverse c (w.getD 0 0) (w.getD 1 0) % (p+1)]

theorem correct (p half : ℕ) (inverse : Bool) (tag : Ordering) (x y : ZMod (p+1)) :
    let u := Tree.fork (comparisonMark (comparisonCode tag)) (numeralWord [x.val,y.val])
    let v := numeralWord [(InterchangeSpectralStep.value inverse (half : ZMod (p+1)) tag x y).val]
    RegisterLookup.read (table p half inverse) u = v ∧ (u,v) ∈ table p half inverse := by
  apply tagged_correct _ _ comparisonMark_inj _ (comparisonCode tag)
  · cases tag <;> decide
  · let f (w : List ℕ) := numeralWord
      [numerator p half inverse (comparisonCode tag) (w.getD 0 0) (w.getD 1 0) % (p+1)]
    have member (a : ℕ) (ha : a ∈ [x.val,y.val]) : a ∈ List.range (p+1) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl <;> exact List.mem_range.mpr (ZMod.val_lt _)
    have h := literal_correct (List.range (p+1)) 2 numeral numeral_injective f [x.val,y.val] rfl member
    have e : f [x.val,y.val] = numeralWord [(InterchangeSpectralStep.value inverse
      (half : ZMod (p+1)) tag x y).val] := congrArg (fun z => numeralWord [z]) (residue_eq _ _ _ _ _ _)
    exact e ▸ h

variable {X : Type} [Primcodable X]

private theorem computable_numerator {p half x y : X → ℕ} {inv : X → Bool} {tag : X → Fin 3}
    (hp : Computable p) (hh : Computable half) (hi : Computable inv)
    (ht : Computable tag) (hx : Computable x) (hy : Computable y) :
    Computable fun u => numerator (p u) (half u) (inv u) (tag u) (x u) (y u) := by
  have n := Computable.succ.comp hp
  have neg := Primrec.nat_sub.to_comp.comp n (Primrec.nat_mod.to_comp.comp hx n)
  let dir (v : Fin 3) (b : Fin 3) := decide (v = b)
  have c (b : Fin 3) : Computable fun u => dir (tag u) b :=
    (Primrec.dom_finite (fun v : Fin 3 => dir v b)).to_comp.comp ht
  have src := Computable.cond (c 2) neg hx
  have coeff := Computable.cond hi hh (Computable.const 1)
  have v := Computable.cond (c 1) hx (Primrec.nat_mul.to_comp.comp coeff
    (Primrec.nat_add.to_comp.comp src hy))
  apply v.of_eq
  intro u
  simp [numerator,dir,Bool.cond_eq_ite]

theorem computable_spelled_table {p half : X → ℕ} {inv : X → Bool}
    (hp : Computable p) (hh : Computable half) (hi : Computable inv) :
    Computable fun x => spelledTable (table (p x) (half x) (inv x)) := by
  apply computable_spelled_tagged (enc := fun _ => comparisonMark) (Computable.const _)
    ((Primrec.dom_finite (fun v : Fin 3 => spelling (comparisonMark v))).to_comp.comp Computable.snd).to₂
  let Y := X × Fin 3
  change Computable (fun u : Y => spelledTable (literal (List.range (p u.1 + 1)) 2 numeral fun w =>
    numeralWord [numerator (p u.1) (half u.1) (inv u.1) u.2 (w.getD 0 0) (w.getD 1 0) % (p u.1 + 1)]))
  have hp' : Computable (fun v : Y => p v.1) := hp.comp Computable.fst
  apply computable_spelled_literal (letter := fun _ : Y => numeral)
    (Primrec.list_range.to_comp.comp (Computable.succ.comp hp')) (Computable.const 2)
    (primrec_spelling_numeral.to_comp.comp Computable.snd).to₂
  let A := Y × List ℕ
  have src : Computable (fun u : A => u.1.1) := Computable.fst.comp Computable.fst
  have dig (j : ℕ) : Computable (fun u : A => u.2.getD j 0) :=
    (Primrec.list_getD 0).to_comp.comp Computable.snd (Computable.const j)
  have out := computable_numerator (hp.comp src) (hh.comp src) (hi.comp src)
    (Computable.snd.comp (Computable.fst (α := Y) (β := List ℕ))) (dig 0) (dig 1)
  exact (primrec_spelling_numeralWord.to_comp.comp
    (Computable.list_cons.comp (Primrec.nat_mod.to_comp.comp out (Computable.succ.comp (hp.comp src)))
      (Computable.const []))).to₂

end InterchangeROMRepair.SweepTable

end NearSquareRoot
end Computability
end OAI
