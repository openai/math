import OAI.Hierarchy.TraceRecordScale

namespace OAI
/-! # Sizes of retained width files and the counted native stage loop -/

namespace Hierarchy.TraceAdmission
open TraceDistribution Filter
open scoped Topology

/-- Absorb the loop-back, one fixed block of stage calls, and its exit into the
same record budget as the packed adaptive graph. -/
theorem counted_overhead {w n rows coeff volume ticks : ℕ} (blocks : n≤64*w)
    (pos : 0<volume) (work : ticks≤n*coeff*volume) :
    n*(7+(rows*(rows*ticks)+1))+4 ≤
      (12+rows*rows*coeff)*(n+1)*volume*(64*w+1) := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
  calc
    _ ≤ n*(7+(rows*(rows*(n*coeff*(v+1)))+1))+4 := by gcongr
    _ ≤ (12+rows*rows*coeff)*(n+1)*(v+1)*(n+1) := by ring_nf; omega
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.succ_le_succ blocks)

/-- The squared fixed row-count coefficient in the actual counted loop and the
extra repetition counter all fit in the three-fifths trace budget. -/
theorem counted_room {u s : ℕ→ℕ} (scale : Scale u s) (rows coeff : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ ticks : ℕ,
      let k:=u w+1-w/2
      ticks≤s w*coeff*(1+k*2^k) →
      s w*(7+(rows*(rows*ticks)+1))+4≤2^(3*w/5) := by
  have upper := (tendsto_order.mp scale.cap).2 2 (by norm_num)
  filter_upwards [upper, lane_room scale 1, record_room scale (12+rows*rows*coeff),
    eventually_ge_atTop 1] with w rate blocks heap hw
  intro ticks k cost
  have pos : (0:ℝ)<w := by exact_mod_cast (show 0<w by omega)
  have cap : u w≤2*w := by exact_mod_cast ((div_lt_iff₀ pos).mp rate).le
  have small : s w≤k := by simpa [k] using blocks
  exact (counted_overhead (by dsimp [k] at small; omega : s w≤64*w)
    (by omega : 0<1+k*2^k) cost).trans heap

/-- A relocated sparse archive has room for the static headers, packed record
and chronological write arena when each lies below the three-fifths budget. -/
theorem placement {w β headers hist heapWords cap : ℕ} (hw : 7≤w)
    (headerRoom : headers ≤ 2^(3*w/5)) (histRoom : hist ≤ 2^(3*w/5))
    (heapRoom : heapWords ≤ 2^(3*w/5)) (recordRoom : 64*w*hist≤cap) :
    let S := (2^w)^4
    β+headers≤β+S ∧ β+S+hist≤β+5*S ∧ β+5*S+heapWords≤β+6*S ∧
      heapWords≤2^w ∧ 64*w*hist≤cap := by
  let q := 2^w
  have size : 2^(3*w/5)≤q := Nat.pow_le_pow_right (by decide) (by omega)
  have top : q≤q^4 := Nat.le_self_pow (by decide) _
  have h₁ := headerRoom.trans size
  have h₂ := histRoom.trans size
  have h₃ := heapRoom.trans size
  change β+headers≤β+q^4 ∧ β+q^4+hist≤β+5*q^4 ∧ β+5*q^4+heapWords≤β+6*q^4 ∧
    heapWords≤q ∧ 64*w*hist≤cap
  exact ⟨by omega,by omega,by omega,h₃,recordRoom⟩

end Hierarchy.TraceAdmission

end OAI
