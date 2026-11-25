import OAI.Hierarchy.DescentCapAtAge

namespace OAI
/-! # Products of the actual scheduled ordinary and reset capacity factors -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentHostDegree
open scoped BigOperators
variable {F:Type} [Field F] (G:PoweredGadget F)

private theorem prefix_length (b start t:ℕ):(ordinaryCapFactors b start t).length=t:=by
  induction t generalizing start with
  | zero=>rfl
  | succ t ih=>simp [ordinaryCapFactors,ih]

private theorem calendar_length (b t gain n:ℕ):(capCalendar b t gain n).length=(t+1)*n:=by
  induction n with
  | zero=>simp [capCalendar]
  | succ n ih=>simp [capCalendar,capPeriod,prefix_length,ih,Nat.mul_succ,Nat.add_comm,Nat.add_assoc]

theorem terminal_factor (b t gain height age:ℕ) (last:age+1=(t+1)*height):
    2^gain*((capCalendar b t gain height).take age).prod=(capCalendar b t gain height).prod:=by
  have cut (n:ℕ):∃xs,capCalendar b t gain (n+1)=xs++[2^gain]:=by
    induction n with
    | zero=>exact ⟨ordinaryCapFactors b 0 t,by simp [capCalendar,capPeriod]⟩
    | succ n ih=>obtain ⟨xs,hx⟩:=ih;exact ⟨capPeriod b t gain++xs,by rw [capCalendar,hx,List.append_assoc]⟩
  obtain ⟨n,hh⟩:=Nat.exists_eq_succ_of_ne_zero (show height≠0 by intro h0;simp [h0] at last)
  obtain ⟨xs,hx⟩:=cut n
  have size:=calendar_length b t gain height
  rw [hh,hx] at size
  have nlen:xs.length=age:=by simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add] at size;rw [hh] at last;omega
  rw [hh,hx,←nlen]
  simp [Nat.mul_comm]

theorem all_caps (t g J i:ℕ):
    ((capCalendar G.b t g J).take i).prod*256≤2^(8+capRate G t g*((t+1)*J)):=by
  have len:=calendar_length G.b t g J
  by_cases inside:i≤(t+1)*J
  · exact (cap_at_age G t g J i).trans (Nat.pow_le_pow_right (by decide)
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ inside) 8))
  · have later:(capCalendar G.b t g J).length≤ i:=len.le.trans (Nat.le_of_not_ge inside)
    rw [List.take_of_length_le later]
    simpa only [List.take_of_length_le len.le] using cap_at_age G t g J ((t+1)*J)

end Hierarchy.DescentSixParty.NativePitch

end OAI
