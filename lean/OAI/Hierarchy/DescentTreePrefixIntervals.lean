import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
/-! # Common-depth leaf intervals for all nodes of an adaptively chosen contact tree -/

namespace Hierarchy.DescentTreePrefixIntervals

abbrev Bits (d : ℕ) := Fin d→Bool

/-- Lexicographic leaf number, with the oldest spatial decision in the high bit. -/
def lex : (d : ℕ)→Bits d→ℕ
  | 0,_=>0
  | d+1,x=>2*lex d (fun i=>x i.castSucc)+(x (Fin.last d)).toNat

theorem lex_lt (d : ℕ) (x : Bits d) : lex d x<2^d := by
  induction d with
  | zero=>decide +revert
  | succ d ih=>
    have small:=ih (fun i=>x i.castSucc)
    simp only [lex,pow_succ]
    cases x (Fin.last d) <;> simp <;> omega

theorem lex_injective (d : ℕ) : Function.Injective (lex d) := by
  induction d with
  | zero=>exact fun _ _ _=>Subsingleton.elim _ _
  | succ d ih=>
    intro x y equal
    simp only [lex] at equal
    have bits : x (Fin.last d)=y (Fin.last d) := by
      cases lx : x (Fin.last d) <;> cases ly : y (Fin.last d) <;> simp_all [Bool.toNat] <;> omega
    have base : (fun i : Fin d=>x i.castSucc)=(fun i : Fin d=>y i.castSucc) := ih (by rw [bits] at equal;omega)
    funext i
    exact Fin.lastCases bits (fun j=>congrFun base j) i

def cut {d h : ℕ} (le : d≤h) (x : Bits h) : Bits d := fun i=>x (Fin.castLE le i)

def start {d : ℕ} (H : ℕ) (u : Bits d) := lex d u*2^(H-d)

def stop {d : ℕ} (H : ℕ) (u : Bits d) := (lex d u+1)*2^(H-d)

/-- The first and the excluded last leaf addresses are independent of the actual book. -/
theorem inside {d h : ℕ} (le : d≤h) (x : Bits h) :
    start h (cut le x)≤lex h x ∧ lex h x<stop h (cut le x) := by
  induction h with
  | zero=>
    obtain rfl : d=0:=by omega
    simp [start,stop,lex]
  | succ h ih=>
    by_cases top : d=h+1
    · subst d
      have eqn : cut le x=x:=rfl
      simp [eqn,start,stop]
    · have below : d≤h:=by omega
      let prior : Bits h:=fun i=>x i.castSucc
      obtain ⟨lo,hi⟩:=ih below prior
      have same : cut below prior=cut le x:=rfl
      have pow : 2^(h+1-d)=2^(h-d)*2 := by rw [show h+1-d=(h-d)+1 by omega,pow_succ]
      simp only [start,stop] at *
      rw [←same,pow,←Nat.mul_assoc,←Nat.mul_assoc]
      change _≤2*lex h prior+(x (Fin.last h)).toNat ∧ 2*lex h prior+_ < _
      cases x (Fin.last h) <;> simp <;> omega

/-- A short real leaf key is zero-padded on its right, in the one common maximum-height address space. -/
theorem member {d h H : ℕ} (depth : d≤h) (wide : h≤H) (x : Bits h) (v : Bits d) :
    (start H v≤start H x ∧ start H x<stop H v) ↔ cut depth x=v := by
  have pos : 0<2^(H-h):=Nat.two_pow_pos _
  have pow : 2^(H-d)=2^(h-d)*2^(H-h) := by rw [←pow_add];congr 1;omega
  have test : (start H v≤start H x ∧ start H x<stop H v) ↔
      (start h v≤lex h x ∧ lex h x<stop h v) := by
    simp only [start,stop,pow,←Nat.mul_assoc,Nat.mul_le_mul_right_iff pos,Nat.mul_lt_mul_right pos]
  rw [test]
  refine ⟨?_,fun eqn=>eqn ▸ inside depth x⟩
  intro ⟨lo,hi⟩
  apply lex_injective d
  have own:=inside depth x
  by_contra neq
  rcases lt_or_gt_of_ne neq with a|a
  · have gap:=Nat.mul_le_mul_right (2^(h-d)) (Nat.succ_le_of_lt a)
    change (_+1)*(2^(h-d))≤_*_ at gap
    simp only [start,stop] at own lo hi
    omega
  · have gap:=Nat.mul_le_mul_right (2^(h-d)) (Nat.succ_le_of_lt a)
    change (_+1)*(2^(h-d))≤_*_ at gap
    simp only [start,stop] at own lo hi
    omega

theorem stop_le {d H : ℕ} (le : d≤H) (v : Bits d) : stop H v≤2^H := by
  have cap:=Nat.mul_le_mul_right (2^(H-d)) (show lex d v+1≤2^d from lex_lt d v)
  simpa [stop,←pow_add,Nat.add_sub_of_le le] using cap

end Hierarchy.DescentTreePrefixIntervals

end OAI
