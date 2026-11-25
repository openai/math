import OAI.Computability.VPVNP.RAMExecution
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Append-only addresses for a finite run of original RAM dates -/
namespace Hierarchy.DescentDatedAddressBook
open Computability.VPVNP.BurstRAM

/-- The first unused address before date `t`, after a fixed initial header. -/
def floor (origin : ℕ) (span : ℕ→ℕ) : ℕ→ℕ
  | 0 => origin
  | t+1 => floor origin span t+span t

@[simp] theorem floor_zero (origin : ℕ) (span : ℕ→ℕ) : floor origin span 0=origin := rfl
@[simp] theorem floor_succ (origin : ℕ) (span : ℕ→ℕ) (t : ℕ) :
    floor origin span (t+1)=floor origin span t+span t := rfl

theorem floor_mono (origin : ℕ) (span : ℕ→ℕ) : Monotone (floor origin span) :=
  monotone_nat_of_le_succ (fun _=>Nat.le_add_right ..)

/-- Every individual word of an earlier interval lies below the floor
passed to the machines of strictly later dates. Empty dates are allowed. -/
theorem separated {origin i j off : ℕ} {span : ℕ→ℕ} (dated : i<j) (slot : off<span i) :
    floor origin span i+off<floor origin span j :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left slot _) (floor_mono origin span dated)

theorem retained {w origin start stop addr : ℕ} (span : ℕ→ℕ) (states : ℕ→Memory w)
    (earlier : addr<floor origin span start) (dates : start≤stop)
    (kept : ∀t,start≤t→t<stop→∀x<floor origin span t,states (t+1) x=states t x) :
    states stop addr=states start addr := by
  induction stop,dates using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    exact (kept j hj (Nat.lt_succ_self _) addr (earlier.trans_le (floor_mono origin span hj))).trans
      (ih (fun t ht lt=>kept t ht (lt.trans (Nat.lt_succ_self _))))

theorem floor_le {origin n slice : ℕ} (span : ℕ→ℕ) (sizes : ∀i<n,span i≤slice) :
    floor origin span n≤origin+n*slice := by
  induction n with
  | zero => simp
  | succ t ih =>
    simpa only [floor_succ,Nat.succ_mul,Nat.add_assoc] using
      Nat.add_le_add (ih (fun i hi=>sizes i (Nat.lt_succ_of_lt hi))) (sizes t (Nat.lt_succ_self _))

/-- The number of dated sections and their true individual lengths may have different
exponents. One linear word width covers the initial header and every section. -/
theorem within_word {h A B n origin : ℕ} (positive : 0<h) (span : ℕ→ℕ)
    (header : origin≤2^(B*h)) (dates : n≤2^(A*h)) (sizes : ∀i<n,span i≤2^(B*h)) :
    floor origin span n<2^((A+B+2)*h) := by
  have counts:=Nat.mul_le_mul_right (2^(B*h)) dates
  rw [←Nat.pow_add,←Nat.add_mul] at counts
  have pre : 2^(B*h)≤2^((A+B)*h):=Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_right h (Nat.le_add_left ..))
  have former:=floor_le (origin:=origin) span sizes
  have extra : (A+B)*h+2≤(A+B+2)*h := by rw [Nat.add_mul (A+B) 2];omega
  have window:=Nat.pow_le_pow_right (by decide : 0<2) extra
  rw [Nat.pow_add] at window
  have pos:=Nat.two_pow_pos ((A+B)*h)
  omega

end Hierarchy.DescentDatedAddressBook

end OAI
