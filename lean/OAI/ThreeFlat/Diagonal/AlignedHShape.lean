import OAI.ThreeFlat.RAM.PhysicalPinsNumeric
import OAI.ThreeFlat.Diagonal.DefectBudget
import OAI.ThreeFlat.Diagonal.AlignedChunkVisit
import OAI.ThreeFlat.Diagonal.TickClockAllocation

namespace OAI
/-! # The native two-half matrix and its block clock at the chosen dyadic age -/

namespace ThreeFlat.Diagonal.AlignedHShape
open RAM.PhysicalPinsExpr
variable {u b A e ℓ : ℕ}

/-- One period is the number of whole L-tick intervals in a half. -/
def shape (u b A ℓ params parameterBase templateBase : ℕ) : Shape where
  advice := 2^(u^3)
  teamBits := u^3
  timeBits := u^6
  parameterBits := params
  bits := 2^(u^10-u^4)
  inside := 2^ℓ-1
  teams := 2^(u^3)
  period := 2^(u^3+u^4-b*(A+2))
  last := 2^(u^6-ℓ)-1
  parameterBase := parameterBase
  templateBase := templateBase

instance (u b A ℓ p a t : ℕ) : NeZero (shape u b A ℓ p a t).period :=
  ⟨Nat.ne_of_gt (Nat.two_pow_pos _)⟩

variable (p a t : ℕ)
local notation "s" => shape u b A ℓ p a t

theorem ticks : (s).inside+1=2^ℓ := by
  change 2^ℓ-1+1=2^ℓ
  have := Nat.two_pow_pos ℓ
  omega

theorem blocks : (s).last+1=2^(u^6-ℓ) := by
  change 2^(u^6-ℓ)-1+1=2^(u^6-ℓ)
  have := Nat.two_pow_pos (u^6-ℓ)
  omega

theorem measures (age : u=2^b) (large : max (A+2) e≤u) (length : 2^ℓ≤u^e) :
    (s).inside+1=2^ℓ ∧ ((s).last+1)*(2^ℓ)=2^(u^6) ∧
    (s).halfBits=2^(u^3)*2^(u^10)*2^ℓ/u^(A+2) ∧ 2^ℓ≤2^(u^2) := by
  have hu : 0<u := by rw [age]; exact Nat.two_pow_pos _
  have hb : b≤u := by rw [age]; exact Nat.le_of_lt Nat.lt_two_pow_self
  have d0 : b*(A+2)≤u^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul hb ((le_max_left ..).trans large)
  have h4 : u^4≤u^10 := Nat.pow_le_pow_right hu (by decide)
  have h2 : u^2≤u^3 := Nat.pow_le_pow_right hu (by decide)
  have h6 : u^2≤u^6 := Nat.pow_le_pow_right hu (by decide)
  have time := length.trans (width_pow_le_two_pow_sq ((le_max_right ..).trans large))
  have leL := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp time
  refine ⟨ticks p a t,?_,?_,time⟩
  · rw [blocks p a t,←Nat.pow_add,Nat.sub_add_cancel (leL.trans h6)]
  · change (s).period*((s).inside+1)*2^(u^10-u^4)=_
    rw [ticks p a t,show u^(A+2)=2^(b*(A+2)) by rw [age,Nat.pow_mul],
      ←Nat.pow_add 2 (u^3) (u^10),←Nat.pow_add 2 (u^3+u^10) ℓ,Nat.pow_div (by omega) (by decide)]
    change 2^(u^3+u^4-b*(A+2))*2^ℓ*2^(u^10-u^4)=_
    rw [←Nat.pow_add,←Nat.pow_add]
    congr 1
    omega

/-- The same physical half has enough bits to state the rank saving. -/
theorem rank_room (age : u=2^b) (large : max (A+2) e≤u) (length : 2^ℓ≤u^e)
    (lower : u^(A+2)≤2^ℓ) :
    2^(u^3)*2^(u^10-u)≤ (s).bits*(s).chunks := by
  have h := (measures p a t age large length).2.2.1
  have hpos : 0<u := by rw [age]; exact Nat.two_pow_pos _
  have den : 0<u^(A+2) := Nat.pow_pos hpos
  have available : 2^(u^3)*2^(u^10) ≤ (s).halfBits := by
    rw [h]
    exact (Nat.le_div_iff_mul_le den).mpr (Nat.mul_le_mul_left _ lower)
  rw [Nat.mul_comm (s).bits (s).chunks]
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le _ _))).trans available

/-- Instantiate the same physical group clock used by the native seven-phase tick program. -/
theorem clock_exact (age : u=2^b) (large : A+2≤u) (threshold : e+16≤u) (length : 2^ℓ≤u^e) :
    ∃ c : TickChronology.Clock,c.last+1=2^(u^6) ∧ c.groups=1024*(2*(s).chunks) ∧
      c.chunks=2*(s).chunks ∧ c.evaluateTicks=2^(u^6)/(4*c.groups) ∧ 0<c.groups ∧ 2^(u^6)=4*(c.groups*c.evaluateTicks) := by
  let C := 2*(s).chunks
  let J := 1024*C
  have plenty : max (A+2) e≤u := max_le large (by omega)
  have half := (measures p a t age plenty length).2.2.1
  have a_pos : 0<(s).bits := Nat.two_pow_pos _
  have count_pos : 0<C := by
    change 0<2*((s).period*((s).inside+1))
    exact Nat.mul_pos (by decide) (Nat.mul_pos (Nat.two_pow_pos _) (Nat.succ_pos _))
  have exponent : ∃ g : ℕ,J=2^g := by
    refine ⟨(11+(u^3+u^4-b*(A+2)))+ℓ,?_⟩
    change 1024*(2*((s).period*((s).inside+1)))=_
    rw [ticks p a t,Nat.pow_add 2 (11+(u^3+u^4-b*(A+2))) ℓ,Nat.pow_add 2 11]
    change 1024*(2*(2^(u^3+u^4-b*(A+2))*2^ℓ))=(2048*_)*_
    ring
  have quota : 1024*(2*(2^(u^3)*2^(u^10)*2^ℓ/u^(A+2)))/(s).bits=J := by
    rw [←half]
    change 1024*(2*((s).chunks*(s).bits))/(s).bits=1024*(2*(s).chunks)
    rw [show 1024*(2*((s).chunks*(s).bits))=(1024*(2*(s).chunks))*(s).bits by ring,Nat.mul_div_cancel _ a_pos]
  have hJ : J≤2^(2*u^4) := by
    rw [←quota]
    exact group_count_budget (A:=A) threshold length
  have clockArgs := TickChronology.clock_budget (by omega : 6≤u) exponent hJ count_pos
      (by dsimp [J]; omega : C≤J)
  let c := TickChronology.reserve clockArgs.1 count_pos clockArgs.2.1 clockArgs.2.2
  refine ⟨c,?_,rfl,rfl,rfl,clockArgs.1,clockArgs.2.2⟩
  change 2^(u^6)-1+1=2^(u^6)
  have := Nat.two_pow_pos (u^6)
  omega

theorem clock_exists (age : u=2^b) (large : A+2≤u) (threshold : e+16≤u) (length : 2^ℓ≤u^e) :
    ∃ c : TickChronology.Clock,c.last+1=2^(u^6) ∧ c.groups=1024*(2*(s).chunks) ∧
      c.chunks=2*(s).chunks ∧ c.evaluateTicks=2^(u^6)/(4*c.groups) ∧ 0<c.groups := by
  obtain ⟨c,t,g,scan,ev,pos,_⟩:=clock_exact p a t age large threshold length
  exact ⟨c,t,g,scan,ev,pos⟩

end ThreeFlat.Diagonal.AlignedHShape

end OAI
