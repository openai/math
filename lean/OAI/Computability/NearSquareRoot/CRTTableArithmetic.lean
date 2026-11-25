import OAI.Computability.IntegerMultiplication.Staff.Nat
import Mathlib.Data.Int.GCD

/-! Unary arithmetic for the small moduli of the CRT routing tables.
Each `Poly` theorem gives a stack program with a polynomial time bound in the
encoded input size. In particular the inverse search only enumerates residues
of its supplied axis modulus. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication IntegerMultiplication.Code

/-- Unary remainder; for modulus zero this returns the dividend. -/
def rem (i : Tally × Tally) : Tally := (Staff.quot i).2

@[fun_prop] theorem rem_poly : Poly rem := Staff.stable_q.sndCompose

@[simp] theorem rem_length (x a : Tally) : (rem (x,a)).length = x.length % a.length := by
  conv_lhs => rw [← recover_tally x, ← recover_tally a]
  simp [rem, Staff.quot_r]

private def mul (p : Tally × Tally) : Tally :=
  (p.1.map (fun _ => p.2)).flatten

private theorem mul_poly : Poly mul :=
  (Packed.chamber (X := Tally)).compose Easy.flatten.poly

private theorem mul_length (x y : Tally) : (mul (x,y)).length = x.length * y.length := by
  simp [mul, List.map_const', List.length_flatten]

def mulMod (i : Tally × Tally × Tally) : Tally :=
  rem (mul (i.1, i.2.1), i.2.2)

@[fun_prop] theorem mulMod_poly : Poly mulMod := by
  have h := (show Poly (fun i : Tally × Tally × Tally => (i.1,i.2.1)) by fun_prop).compose mul_poly
  exact (h.pair (by fun_prop)).compose rem_poly

@[simp] theorem mulMod_length (x y a : Tally) :
    (mulMod (x,y,a)).length = x.length * y.length % a.length := by
  simp [mulMod, mul_length]

def addMod (i : Tally × Tally × Tally) : Tally := rem (i.1 ++ i.2.1, i.2.2)

@[fun_prop] theorem addMod_poly : Poly addMod := by
  exact (show Poly (fun i : Tally × Tally × Tally => (i.1 ++ i.2.1,i.2.2)) by fun_prop).compose rem_poly

@[simp] theorem addMod_length (x y a : Tally) :
    (addMod (x,y,a)).length = (x.length + y.length) % a.length := by
  simp [addMod]

/-- A modular elimination step reduces the accumulator before adding the
modulus and subtracting the already-reduced product. -/
def subtractMul (i : Tally × Tally × Tally × Tally) : Tally :=
  let a := i.2.2.2
  rem ((cutLists (mulMod i.2, rem (i.1,a) ++ a)).2, a)

@[fun_prop] theorem subtractMul_poly : Poly subtractMul := by
  let A := Tally × Tally × Tally × Tally
  have ha : Poly (fun i : A => i.2.2.2) := by fun_prop
  have hv := (Easy.fst.poly.pair ha).compose rem_poly
  have hp := (Easy.snd (X := Tally) (Y := Tally × Tally × Tally)).poly.compose mulMod_poly
  have cut := (hp.pair (Poly.app hv ha)).compose (easy_cut (X := Unit) Easy.identity).sndCompose.poly
  exact (cut.pair ha).compose rem_poly

@[simp] theorem subtractMul_length (v c t a : Tally) :
    (subtractMul (v,c,t,a)).length =
      (v.length % a.length + a.length - (c.length * t.length % a.length)) % a.length := by
  simp [subtractMul, cutLists]

theorem subtractMul_lt (v c t a : Tally) (ha : 0 < a.length) :
    (subtractMul (v,c,t,a)).length < a.length := by
  rw [subtractMul_length]
  exact Nat.mod_lt _ ha

private def inverseTest (p : (Tally × Tally) × Tally) : Bool :=
  decide ((mulMod (p.1.1,p.2,p.1.2)).length = (rem (tally 1,p.1.2)).length)

private theorem inverseTest_poly : Poly inverseTest := by
  let A := (Tally × Tally) × Tally
  have h := (show Poly (fun p : A => (p.1.1,p.2,p.1.2)) by fun_prop).compose mulMod_poly
  have t := (show Poly (fun p : A => (tally 1,p.1.2)) by fun_prop).compose rem_poly
  exact (h.pair t).compose (Iter.linked (X:=Unit) (Y:=Unit)).poly

private def accept (p : (Tally × Tally) × Tally) : List Tally :=
  bif inverseTest p then [p.2] else []

private theorem accept_poly : Poly accept := by
  unfold accept
  apply Code.Poly.choose inverseTest_poly
  · fun_prop
  · exact (Easy.const ([] : List Tally)).poly

private def candidates (p : Tally × Tally) : List Tally :=
  (polyPush accept (p, Iter.lineup p.2)).flatten

private theorem candidates_poly : Poly candidates := by
  have h := (Poly.identity.pair (Easy.snd.poly.compose Iter.poly_line)).compose
    (Poly.push ([],[]) [] accept_poly)
  exact h.compose Easy.flatten.poly

/-- First multiplicative inverse in increasing residue order, or zero if none
exists. Modulus one gives zero, the sole valid residue. -/
def inverse (p : Tally × Tally) : Tally := (candidates p).headD []

@[fun_prop] theorem inverse_poly : Poly inverse :=
  candidates_poly.compose (Iter.leader []).poly

private theorem mem_candidates (x a u : Tally) : u ∈ candidates (x,a) ↔
    u.length < a.length ∧ x.length * u.length % a.length = 1 % a.length := by
  have lineup (v : Tally) : v ∈ Iter.lineup a ↔ v.length < a.length := by
    simp only [Iter.lineup, List.mem_ofFn]
    constructor
    · rintro ⟨j,rfl⟩
      simp
    · intro h
      exact ⟨⟨v.length,h⟩,recover_tally v⟩
  simp only [candidates, polyPush, ← List.flatMap_def, List.mem_flatMap]
  constructor
  · rintro ⟨v,hv,h⟩
    by_cases test : inverseTest ((x,a),v) = true
    · simp only [accept,test,Bool.cond_true,List.mem_singleton] at h
      subst v
      exact ⟨(lineup u).mp hv, by simpa [inverseTest] using test⟩
    · simp [accept, Bool.eq_false_iff.mpr test] at h
  · rintro ⟨hu,h⟩
    refine ⟨u,(lineup u).mpr hu,?_⟩
    have test : inverseTest ((x,a),u) = true := by simpa [inverseTest] using h
    simp [accept, test]

theorem inverse_lt (x a : Tally) (ha : 0 < a.length) :
    (inverse (x,a)).length < a.length := by
  cases h : candidates (x,a) with
  | nil => simpa [inverse,h] using ha
  | cons z zs =>
    have hm : z ∈ candidates (x,a) := by simp [h]
    simpa [inverse,h] using ((mem_candidates x a z).mp hm).1

@[simp] theorem inverse_zero (x : Tally) : inverse (x,[]) = [] := by
  simp [inverse,candidates,Iter.lineup,polyPush]

theorem inverse_spec (x a : Tally) (ha : 0 < a.length) (h : x.length.Coprime a.length) :
    (inverse (x,a)).length < a.length ∧
      x.length * (inverse (x,a)).length % a.length = 1 % a.length := by
  obtain ⟨u,hu,he⟩ := Nat.exists_mul_mod_eq_of_coprime 1 h ha.ne'
  have hm : tally u ∈ candidates (x,a) := (mem_candidates x a _).mpr (by simpa using And.intro hu he)
  cases hl : candidates (x,a) with
  | nil => simp [hl] at hm
  | cons v vs =>
    have hv : v ∈ candidates (x,a) := by simp [hl]
    simpa [inverse,hl] using (mem_candidates x a v).mp hv

end CRTTable

end NearSquareRoot
end Computability
end OAI
