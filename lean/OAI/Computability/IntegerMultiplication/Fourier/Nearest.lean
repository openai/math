import OAI.Computability.IntegerMultiplication.Fourier.Index
import OAI.Computability.IntegerMultiplication.Fourier.Window
import OAI.Computability.IntegerMultiplication.Fourier.CosTail
import Mathlib.Tactic

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier
variable (s t : ℕ) [NeZero s] [NeZero t]

def pickRaw (y : Spot s) : ℕ := (2*t*y.val+s)/(2*s)

private theorem pick_lt {s t : ℕ} [NeZero s] (h : s≤t) (y : Spot s) :
    pickRaw s t y < t := by
  rw [pickRaw, Nat.div_lt_iff_lt_mul]
  have e : 2*t*y.val+2*t≤2*t*s := by
    have ht : y.val+1≤s := y.isLt
    nlinarith only [Nat.mul_le_mul_left (2*t) ht]
  nlinarith [show s>0 from Nat.pos_of_ne_zero (NeZero.ne s)]
  have := Nat.pos_of_ne_zero (NeZero.ne s); omega

def pick (h : s≤t) (y : Spot s) : Spot t := ⟨pickRaw s t y,pick_lt h y⟩

def delta (y : Spot s) : ℤ := (s:ℤ)*pickRaw s t y - t*rep y

omit [NeZero t] in
theorem delta_small (y : Spot s) : 2*|delta s t y| ≤ (s:ℤ) := by
  unfold delta pickRaw rep
  zify
  have hs : s>0 := Nat.pos_of_ne_zero (NeZero.ne s)
  have hn : 2*s>0 := by omega
  let m := 2*t*y.val+s
  have hh : m/(2*s)*(2*s) ≤ m := Nat.div_mul_le_self _ _
  have hm : m < (m/(2*s)+1)*(2*s) := by
    have e := Nat.mod_add_div m (2*s)
    have u := Nat.mod_lt m hn
    rw [Nat.add_mul,Nat.mul_comm (m/(2*s))] -- inspect
    omega
  zify at hh hm
  dsimp only [m] at *
  -- cast quotient left in goal not push
  have eq (z : ℤ) : 2*|z| = |2*z| := by rw [abs_mul]; rfl
  rw [eq]
  push_cast at hh hm
  apply abs_le.mpr
  constructor <;> nlinarith

/-- For expansion we take the floor location (ties are immaterial). -/
def floorSample (k : Spot t) : ℕ := s*k.val/t

theorem floor_lt (k : Spot t) : floorSample s t k < s :=
  (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne t))).mpr
    (Nat.mul_lt_mul_of_pos_left k.isLt (Nat.pos_of_ne_zero (NeZero.ne s)))

omit [NeZero s] in
theorem floor_spec (k : Spot t) :
    ∃ δ : ℤ, (s:ℤ)*rep k = t*(floorSample s t k)+δ ∧ |δ|≤(t:ℤ) := by
  refine ⟨((s*k.val%t:ℕ):ℤ),?_,?_⟩
  · unfold floorSample rep
    exact_mod_cast ((by have := Nat.mod_add_div (s*k.val) t; omega) :
      s*k.val=t*(s*k.val/t)+(s*k.val%t))
  · rw [abs_of_nonneg (by exact_mod_cast Nat.zero_le _)]
    exact_mod_cast (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne t))).le

theorem inj_near (y : ℤ) {L : ℕ} (h : 2*L<s) :
    Set.InjOn (fun i : ℤ => wrap s (y+i)) (IntegerMultiplication.Fourier.rad L : Set ℤ) := by
  intro a ha b hb e
  have hz := Int.modEq_iff_dvd.mp ((wrap_eq s _ _).mp e)
  rcases lt_trichotomy a b with hq|hq|hq
  · exfalso
    have he := Int.le_of_dvd (show 0 < _ from by omega) hz
    rw [Finset.mem_coe,mem_rad] at ha hb
    omega
  · exact hq
  · exfalso
    have he' := Int.modEq_iff_dvd.mp ((wrap_eq s _ _).mp e.symm)
    have he := Int.le_of_dvd (show 0 < _ from by omega) he'
    rw [Finset.mem_coe,mem_rad] at ha hb
    omega

end Fourier

end IntegerMultiplication
end Computability
end OAI
