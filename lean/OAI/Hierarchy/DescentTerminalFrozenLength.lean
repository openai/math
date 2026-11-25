import OAI.Hierarchy.DescentTerminalFrozenRoster
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Decoding the true number of attached original cohorts from the sparse host word -/
namespace Hierarchy.DescentTerminalFrozenRoster
open Computability.BorderVNP.FragmentBucket
open scoped Classical BigOperators
noncomputable section

def length (f code : ℕ) := if code=0 then 0 else Nat.log (2^(f+1)) code+1

theorem length_read {n H f : ℕ} (home : Fin n→Fin H) (frozen : Fin n→Fin (2^f)) (s : Fin H) :
    length f (book home frozen s).val=count home s := by
  let B:=2^(f+1)
  let z:=book home frozen s
  have overflow : z.val<B^(count home s):=z.isLt
  by_cases empty : count home s = 0
  · have upper : z.val < 1 := calc
      z.val < B^(count home s) := overflow
      _ = 1 := by rw [empty, pow_zero]
    calc
      length f z.val = 0 := ite_eq_left (Nat.lt_one_iff.mp upper)
      _ = count home s := empty.symm
  · let m := count home s - 1
    have size : count home s = m+1 := by dsimp only [m]; omega
    let last : Fin (count home s):=⟨m,by omega⟩
    let char (i : Fin (count home s)) := digit frozen (atRank home s i).val
    have expr : z.val=∑i,(char i).val*B^i.val:=by
      change (finFunctionFinEquiv char).val=_
      rw [finFunctionFinEquiv_apply]
    have summand : (char last).val*B^last.val≤z.val:=by
      rw [expr]
      exact Finset.single_le_sum (f := fun i : Fin (count home s) => (char i).val * B^i.val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ last)
    have positive : 0<(char last).val:=Nat.zero_lt_succ _
    have floor : B^m≤z.val:=(Nat.le_mul_of_pos_left _ positive).trans summand
    have nonzero : z.val≠0:=Nat.ne_of_gt ((pow_pos (Nat.two_pow_pos _) _).trans_le floor)
    have upper : z.val < B^(m+1) :=
      overflow.trans_le (congrArg (fun k : ℕ => B^k) size).le
    calc
      length f z.val = Nat.log B z.val+1 := ite_eq_right nonzero
      _ = m+1 := congrArg (fun k : ℕ => k+1) (Nat.log_eq_of_pow_le_of_lt_pow floor upper)
      _ = count home s := size.symm

def dense (f code frozenId : ℕ) := lookup f (length f code) code frozenId

theorem dense_read {n H f : ℕ} (home : Fin n→Fin H) (frozen : Fin n→Fin (2^f)) (s : Fin H)
    (distinct : ∀i j : Fin n,home i=s→home j=s→frozen i=frozen j→i=j) (u : Fin n) (belongs : home u=s) :
    dense f (book home frozen s).val (frozen u).val=prior home u.val s := by
  rw [dense,length_read]
  exact lookup_read home frozen s distinct u belongs

end
end Hierarchy.DescentTerminalFrozenRoster

end OAI
