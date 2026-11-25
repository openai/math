import OAI.Hierarchy.DescentCapacityCalendar
import OAI.Hierarchy.DescentCalendarNumbers
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace OAI
/-! # Capacity of the actual prefix of the public register calendar -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentHostDegree
open scoped BigOperators
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem cap_entry (t g J : ℕ) : ∀x∈capCalendar G.b t g J,x≤2^capRate G t g:=by
  let B:=2^capRate G t g
  have ord (start n:ℕ)(end_:start+n≤t):∀x∈ordinaryCapFactors G.b start n,x≤B:=by
    induction n generalizing start with
    | zero=>simp [ordinaryCapFactors]
    | succ n ih=>
      intro x member
      change x∈(2^gainExponent 20 (atRound start)*G.b)::ordinaryCapFactors G.b (start+1) n at member
      rcases List.mem_cons.mp member with rfl|later
      · let j:Fin t:=⟨start,by omega⟩
        have item:=Finset.single_le_sum (f:=fun z:Fin t=>2^gainExponent 20 (atRound z.val)*G.b)
          (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
        change 2^gainExponent 20 (atRound start)*G.b≤_ at item
        exact item.trans ((Nat.le_add_left ..).trans (Nat.lt_two_pow_self (n:=capRate G t g)).le)
      · exact ih (start+1) (by omega) _ later
  have p:∀x∈capPeriod G.b t g,x≤B:=by
    intro x mem
    rcases List.mem_append.mp mem with l|r
    · exact ord 0 t (by omega) x l
    · rw [List.mem_singleton.mp r]
      apply Nat.pow_le_pow_right (by decide)
      unfold capRate;omega
  have full (z:ℕ):∀x∈capCalendar G.b t g z,x≤B:=by
    induction z with
    | zero=>simp [capCalendar]
    | succ z ih=>
      intro x mem
      rcases List.mem_append.mp mem with earlier|later
      · exact p x earlier
      · exact ih x later
  exact full J

theorem cap_at_age (t g J i : ℕ) :
    ((capCalendar G.b t g J).take i).prod*256≤2^(8+capRate G t g*i):=by
  let xs:=(capCalendar G.b t g J).take i
  let B:=2^capRate G t g
  have prod:xs.prod≤B^xs.length:=List.prod_le_pow_length xs B
    (fun x hit=>cap_entry G t g J x (List.mem_of_mem_take hit))
  have count:xs.length≤ i:=by rw [List.length_take];exact Nat.min_le_left ..
  calc
    _ ≤ B^i*256:=Nat.mul_le_mul_right _ (prod.trans (Nat.pow_le_pow_right (Nat.two_pow_pos _) count))
    _ = _:=by change ((2^_)^_)*(2^8)=_;rw [←pow_mul,←pow_add,Nat.add_comm]

end Hierarchy.DescentSixParty.NativePitch

end OAI
