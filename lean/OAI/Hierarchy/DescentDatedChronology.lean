import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Closing the address bound on the actual date-dependent sequence of floors -/
namespace Hierarchy.DescentDatedAddressBook
open Computability.VPVNP.BurstRAM Filter

/-- A machine may locate its next public stop by computing absolute addresses at the
exact old floor. This recursion also works for non-strictly-increasing floors. -/
def cursor (start : ℕ) (next : ℕ→ℕ→ℕ) : ℕ→ℕ
  | 0=>start
  | t+1=>next t (cursor start next t)

theorem cursor_eq (start : ℕ) (next : ℕ→ℕ→ℕ) (grows : ∀t a,a≤next t a) (n : ℕ) :
    cursor start next n = floor start (fun t=>next t (cursor start next t)-cursor start next t) n := by
  induction n with
  | zero=>rfl
  | succ t ih=>
    rw [floor_succ,←ih,Nat.add_sub_of_le (grows t _)]; rfl

/-- Bounds on actual increments only apply along the realized history. Each date
receives the preceding date's computed end, and earlier memory can stay in place. -/
theorem cursor_room {h start n A B w : ℕ} (next : ℕ→ℕ→ℕ) (grows : ∀t a,a≤next t a)
    (positive : 0<h) (header : start≤2^(B*h)) (dates : n≤2^(A*h)) (hardware : (A+B+2)*h≤w)
    (cost : ∀t<n,next t (cursor start next t)-cursor start next t≤2^(B*h)) :
    cursor start next n<2^w := by
  rw [cursor_eq start next grows]
  exact (within_word positive _ header dates cost).trans_le (Nat.pow_le_pow_right (by decide) hardware)

theorem cursor_retains {w start s t x : ℕ} (next : ℕ→ℕ→ℕ) (grows : ∀j a,a≤next j a)
    (states : ℕ→Memory w) (old : x<cursor start next s) (order : s≤t)
    (frame : ∀v,s≤v→v<t→∀u<cursor start next v,states (v+1) u=states v u) :
    states t x=states s x := by
  let widths (v : ℕ):=next v (cursor start next v)-cursor start next v
  have relocated (v : ℕ) : cursor start next v=floor start widths v := cursor_eq start next grows v
  apply retained widths states (old.trans_eq (relocated s)) order
  intro v lo hi u earlier
  exact frame v lo hi u (earlier.trans_eq (relocated v).symm)

/-- Uniform rates are combined once, even when different stage types provide their own
host, table, or halo exponents. The last terminal section is a genuine additional date. -/
theorem eventual_calendar_room {start dates : ℕ→ℕ} (next : ℕ→ℕ→ℕ→ℕ)
    (grows : ∀h t a,a≤next h t a)
    (prefixRoom : Bounded (ι:=fun _=>Unit) (fun h _=>start h))
    (length : Bounded (ι:=fun _=>Unit) (fun h _=>dates h))
    (dated : Bounded (ι:=fun h=>Fin (dates h))
      (fun h t=>next h t (cursor (start h) (next h) t)-cursor (start h) (next h) t)) :
    ∃K : ℕ,∀ᶠ h:ℕ in atTop,cursor (start h) (next h) (dates h)<2^(K*h) := by
  obtain ⟨C,hc⟩:=prefixRoom
  obtain ⟨A,ha⟩:=length
  obtain ⟨B,hb⟩:=dated
  refine ⟨A+max C B+2,?_⟩
  filter_upwards [hc,ha,hb,eventually_ge_atTop 1] with h pref count each positive
  have le (u v : ℕ) (hu : u≤v) : 2^(u*h)≤2^(v*h):=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hu)
  exact cursor_room (B:=max C B) (next h) (grows h) positive ((pref ()).trans (le _ _ (le_max_left ..)))
    (count ()) le_rfl (fun t ht=>(each ⟨t,ht⟩).trans (le _ _ (le_max_right ..)))

end Hierarchy.DescentDatedAddressBook

end OAI
