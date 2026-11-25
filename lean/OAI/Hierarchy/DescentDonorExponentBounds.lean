import OAI.Hierarchy.DescentDonorScale
import OAI.Hierarchy.DescentCompilerSlack
import OAI.Hierarchy.DescentCalendarNumbers

namespace OAI
/-! # The actual radix and the per-age capacity of donor inputs are uniformly short -/
namespace Hierarchy.DescentCompiler.TerminalScale.AgeBound
variable {ι : Type*} {age i cap : ι→ℕ}

theorem radix (t host gain cut : ℕ) :
    AgeBound age (fun x=>2^groupBits t (age x) host gain cut) :=
  ⟨1+(host+gain)*(t+1)+8+cut,fun x=>Nat.pow_le_pow_right (by decide) (groupBits_linear ..)⟩

theorem dated_cap {t gain : ℕ} (stop : ∀x,i x≤(t+1)*age x)
    (charged : ∀x,cap x≤2^(8+gain*i x)) : AgeBound age cap := by
  refine ⟨8+gain*(t+1),fun x=>(charged x).trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) ?_)⟩
  have bound :=Nat.mul_le_mul_left gain (stop x)
  calc
    _ ≤ 8+gain*((t+1)*age x) :=Nat.add_le_add_left bound _
    _ ≤ (8+gain*(t+1))*(age x+1) := by
      rw [Nat.mul_succ,Nat.add_mul]
      nlinarith only [Nat.zero_le (gain*(t+1))]

theorem lookup_name_index (k D : ℕ) :
    Nat.clog 2 (2^(k+1)*(2^(DescentHostDegree.packExponent 20 D)+2))≤
      k+1+(DescentHostDegree.packExponent 20 D+2) := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add (2:ℕ) (k+1) (DescentHostDegree.packExponent 20 D+2)]
  apply Nat.mul_le_mul_left
  rw [pow_add]
  have pos : 0<(2:ℕ)^(DescentHostDegree.packExponent 20 D) := Nat.two_pow_pos _
  omega

theorem ranked_labels {k D : ι→ℕ} (bits : AgeBound age k) (degree : AgeBound age D) :
    AgeBound age (fun x=>Nat.clog 2 (2^(k x+1)*(2^(DescentHostDegree.packExponent 20 (D x))+2))) := by
  have log := AgeBound.clog ((AgeBound.const age 2).mul degree)
  have packed:= (AgeBound.const age 20).add ((AgeBound.const age 34).mul log)
  exact (((bits.add (AgeBound.const age 1)).add (packed.add (AgeBound.const age 2)))).mono
    (fun x=>lookup_name_index ..)

/-- With the same age used by the time calculation, two copies of the field actually
fit in one coefficient-independent word. -/
theorem payload_room (a B : ℕ) (slack : a<B) : ∀ᶠ h : ℕ in Filter.atTop,
    let J:=Nat.log 2 h/(2*B)
    2*scale J a≤h := by
  filter_upwards [Filter.eventually_ge_atTop (2^(2*B):ℕ)] with h lower
  have positive : h≠0 := ((Nat.two_pow_pos _).trans_le lower).ne'
  let J:=Nat.log 2 h/(2*B)
  have budget : J*(2*B)≤Nat.log 2 h := Nat.div_mul_le_self _ _
  have both : 2*B≤Nat.log 2 h := (Nat.le_log_iff_pow_le (by decide) positive).2 lower
  have age : 1≤J := (Nat.le_div_iff_mul_le (by omega : 0<2*B)).2 (by simpa using both)
  have room : a*(J+1)+1≤Nat.log 2 h := by
    have paid := Nat.mul_le_mul_left (2*J) (show a+1≤B by omega)
    have enough := Nat.mul_le_mul_left a age
    nlinarith [budget]
  calc
    2*scale J a=2^(a*(J+1)+1) := by change 2*2^(a*(J+1))=_;rw [pow_succ,Nat.mul_comm]
    _ ≤ h := (Nat.le_log_iff_pow_le (by decide) positive).1 room

end Hierarchy.DescentCompiler.TerminalScale.AgeBound

end OAI
