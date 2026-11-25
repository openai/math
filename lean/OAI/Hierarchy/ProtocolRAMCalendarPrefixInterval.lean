import OAI.Hierarchy.ProtocolRAMCalendarStockBound
import OAI.Hierarchy.ProtocolRAMCalendarSegments
import OAI.Hierarchy.ProtocolRAMCalendarPrevious

namespace OAI
/-! # Current-state and persistence laws from the mounted chronological prefix -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.PrefixInterval
open Computability.VPVNP.BurstRAM PrivateRAM StockBound
variable {w q d : ℕ} (C : Chart w q d) (initial : Memory w)
local notation "es" => events C.mesh
local notation "atDate" j:arg => (es)[(j).val]'((j).isLt)

theorem split_position (c : Mesh) (e : Event) (prior tail : List Event)
    (split : events c=prior++e::tail) : position c e=prior.length := by
  have small : prior.length<(events c).length := by rw [split,List.length_append,List.length_cons]; omega
  have val:=congrArg (fun ns : List ℕ=>ns[prior.length]?) (positions c)
  change ((events c).map (position c))[prior.length]?=(List.range (events c).length)[prior.length]? at val
  rw [List.getElem?_range small,split,List.map_append,List.map_cons,List.getElem?_append_right (by simp)] at val
  simpa only [List.length_map,Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] using val

theorem mounted_prefix {s t : ℕ} (le : s≤t) (live : mounted C ((es).take t) initial) :
    mounted C ((es).take s) initial := by
  let xs:=(es).take t
  have split : mounted C (xs.take s ++ xs.drop s) initial := by
    rw [List.take_append_drop]
    exact live
  have left := ((mounted_append C (xs.take s) (xs.drop s) initial).mp split).1
  simpa [xs,List.take_take,Nat.min_eq_left le,Nat.min_eq_right le] using left

theorem ready_at {t : ℕ} (i : Fin (es).length) (early : i.val<t)
    (live : mounted C ((es).take t) initial) : ready C (atDate i) (state C initial i.val) := by
  have small := mounted_prefix C initial (show i.val+1≤t from early) live
  rw [List.take_succ_eq_append_getElem i.isLt] at small
  have last := ((mounted_append C _ _ initial).mp small).2
  exact last.1

/-- A predicate can describe either the two-sided address footprint or the protected
low prefix. The induction uses readiness only at events strictly before the upper cut. -/
private theorem unchanged (P : Event → Prop) (x : ℕ)
    (preserve : ∀e m,ready C e m→P e→after C e m x=m x) (s t : ℕ)
    (le : s≤t) (valid : t≤(es).length) (live : mounted C ((es).take t) initial)
    (keep : ∀ j : Fin (es).length,s≤j.val→j.val<t→P (atDate j)) :
    state C initial t x=state C initial s x := by
  induction t with
  | zero =>
    obtain rfl : s=0 := Nat.eq_zero_of_le_zero le
    rfl
  | succ t ih =>
    by_cases equal : s=t+1
    · rw [equal]
    · have prev : s≤t := by omega
      let j : Fin (es).length := ⟨t,by omega⟩
      have last := ready_at C initial j (show j.val<t+1 from Nat.lt_succ_self _) live
      rw [state_succ C initial t j.isLt]
      exact (preserve _ _ last (keep j prev (Nat.lt_succ_self _))).trans
        (ih prev (by omega) (mounted_prefix C initial (Nat.le_succ t) live)
          (fun k lb ub => keep k lb (Nat.lt_trans ub (Nat.lt_succ_self _))))

theorem after_at (i : Fin (es).length) (t x : ℕ) (early : i.val<t) (valid : t≤(es).length)
    (live : mounted C ((es).take t) initial)
    (keep : ∀j : Fin (es).length,i.val<j.val→j.val<t→protected C x (atDate j)) :
    state C initial t x = after C (atDate i) (state C initial i.val) x := by
  rw [←state_succ C initial i.val i.isLt]
  exact unchanged C initial (protected C x) x (fun e m=>after_frame C e m x)
    (i.val+1) t early valid live keep

theorem after_outside_at (i : Fin (es).length) (t x : ℕ) (early : i.val<t) (valid : t≤(es).length)
    (live : mounted C ((es).take t) initial)
    (keep : ∀j : Fin (es).length,i.val<j.val→j.val<t→ outside C x (atDate j)) :
    state C initial t x = after C (atDate i) (state C initial i.val) x := by
  rw [←state_succ C initial i.val i.isLt]
  exact unchanged C initial (outside C x) x (fun e m=>after_outside C e m x)
    (i.val+1) t early valid live keep

theorem before_at (t x : ℕ) (valid : t≤(es).length) (live : mounted C ((es).take t) initial)
    (keep : ∀j : Fin (es).length,j.val<t→protected C x (atDate j)) : state C initial t x=initial x :=
  unchanged C initial (protected C x) x (fun e m=>after_frame C e m x) 0 t
    (Nat.zero_le _) valid live (fun j _=>keep j)

theorem before_outside_at (t x : ℕ) (valid : t≤(es).length) (live : mounted C ((es).take t) initial)
    (keep : ∀j : Fin (es).length,j.val<t→ outside C x (atDate j)) : state C initial t x=initial x :=
  unchanged C initial (outside C x) x (fun e m=>after_outside C e m x) 0 t
    (Nat.zero_le _) valid live (fun j _=>keep j)

theorem after_arena (A : Arena) (i : Fin (es).length) (t x : ℕ)
    (early : i.val<t) (valid : t≤(es).length) (live : mounted C ((es).take t) initial)
    (paid : x<A.base C.mesh (atDate i)+A.stride)
    (low : ∀j : Fin (es).length,i.val<j.val→j.val<t→ x<A.base C.mesh (atDate j)→protected C x (atDate j)) :
    state C initial t x = after C (atDate i) (state C initial i.val) x := by
  apply after_at C initial i t x early valid live
  intro j lo hi
  apply low j lo hi
  have ordered : position C.mesh (atDate i)<position C.mesh (atDate j) := by
    simpa only [position_at C.mesh i.isLt,position_at C.mesh j.isLt] using lo
  exact paid.trans_le (A.apart C.mesh ordered)

end Hierarchy.ProtocolRAM.Calendar.PrefixInterval
end

end OAI
