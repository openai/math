import OAI.Computability.BorderVNP.TransmissionStartupRate
import OAI.Computability.BorderVNP.TransmissionJointGeometry
import OAI.Computability.BorderVNP.GeometryAdviceAllocation

/-! # The actual demand directory before the geometry output and cell-placement tables -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open Filter TeamScales Packing.Directory
open GeometryAdviceRate (packetWords)

/-- A private site contributes two slice records. The initial site block width `g`
satisfies `r*t₀ ≤ V*g` since the initial slot sequence contains the literal field of
every processor. This bounds all live slices by their actual site count. -/
theorem demand_reserve_le {D : Packing.Directory.Layout} {packs V r : ℕ}
    (procs : D.processors = r) (count : D.entries = packs*V)
    (fields : D.fields = 2) (block : 0 < D.block) (slots : r*D.literal ≤ V*D.block) :
    7*D.candidates ≤ 14*(packs*V+D.teams*(V+2*r)) := by
  have h : r*(D.literal/D.block) ≤ V := by
    apply Nat.le_of_mul_le_mul_right (c := D.block) _ block
    rw [Nat.mul_assoc]
    exact (Nat.mul_le_mul_left _ (Nat.div_mul_le_self ..)).trans slots
  calc
    _ = 14*(packs*V+D.teams*(r*(D.literal/D.block)+2*r)) := by
      rw [Layout.candidates,procs,count,fields]; ring
    _ ≤ _ := by gcongr

/-- The initial site count and the pack growth from (7.1) give sublinear space per
processor for all seven words of every unfiltered demand candidate. -/
theorem eventually_raw_demand {α τ : ℝ} (ha : 0 < α) (ha' : α < 1/1000) (ht : 0 ≤ τ)
    {K : ℕ} (hK : 1 ≤ K) (growth : τ*Real.logb 2 K ≤ α) (A : ℝ) (factor : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (r V : ℕ) (D : Packing.Directory.Layout),
      D.teams = teams α τ K n → D.processors = r → D.entries = K^epochs τ n*V → D.fields = 2 →
      0 < D.block → r*D.literal ≤ V*D.block → (V:ℝ) ≤ A*r*(n:ℝ)^(9/10:ℝ) →
      factor*(7*D.candidates) ≤ r*n := by
  have gap := eventually_rpow_gap (by linarith : 2*α+(9/10:ℝ) < 1) ((factor:ℝ)*14*(2*(abs A)+2))
  filter_upwards [gap,eventually_ge_atTop 1] with n large hn
  intro r V D ts ps cnt fs bk slots cap
  let low : ℝ := (n:ℝ)^(9/10:ℝ)
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n:ℝ) := by linarith
  have one : 1 ≤ low := Real.one_le_rpow hn' (by norm_num)
  have small : 1 ≤ width n α := Nat.le_floor (by simpa using Real.one_le_rpow hn' ha.le)
  have room : (D.teams:ℝ) ≤ (n:ℝ)^(2*α) := ts ▸ teams_le hK hn ht growth
  have packs : K^epochs τ n ≤ D.teams := ts ▸ Nat.le_mul_of_pos_left _ small
  have copies : (↑(K^epochs τ n):ℝ) ≤ (n:ℝ)^(2*α) := (show (↑(K^epochs τ n):ℝ) ≤ D.teams by exact_mod_cast packs).trans room
  have hv : (V:ℝ) ≤ (abs A)*r*low := cap.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self A) (Nat.cast_nonneg r)) (by positivity : 0 ≤ (n:ℝ)^(9/10:ℝ)))
  have vr : (V:ℝ)+2*r ≤ ((abs A)+2)*r*low := by
    calc
      _ ≤ (abs A)*r*low+2*r*low := add_le_add hv (le_mul_of_one_le_right (by positivity) one)
      _ = _ := by ring
  have raw := demand_reserve_le ps cnt fs bk slots
  have hraw : (7*D.candidates : ℝ) ≤ 14*((K^epochs τ n:ℕ)*(V:ℝ)+D.teams*(V+2*(r:ℝ))) := by exact_mod_cast raw
  rw [Real.rpow_one] at large
  have target : (factor:ℝ)*(7*D.candidates) ≤ (r:ℝ)*n := by
    calc
      _ ≤ (factor:ℝ)*(14*((K^epochs τ n:ℕ)*(V:ℝ)+D.teams*(V+2*(r:ℝ)))) := mul_le_mul_of_nonneg_left hraw (Nat.cast_nonneg factor)
      _ ≤ (factor:ℝ)*(14*((n:ℝ)^(2*α)*((abs A)*r*low)+(n:ℝ)^(2*α)*(((abs A)+2)*r*low))) := by gcongr
      _ = (r:ℝ)*(((factor:ℝ)*14*(2*(abs A)+2))*(n:ℝ)^(2*α+(9/10:ℝ))) := by
        dsimp only [low]; rw [Real.rpow_add hnpos]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left large (Nat.cast_nonneg r)
  exact_mod_cast target

/-- The end of the real packed-word geometry allocation consumes at most six times
its serialized bit count after the unfiltered demand reserve. -/
theorem geometry_stop_le (base rows u k o b w : ℕ) (hb : 1 ≤ b) (hw : 1 ≤ w) :
    GeometryAdvice.Allocation.stop (base+7*rows) u k o b w ≤
      base+7*rows+6*(packetWords k u o b*w) := by
  have ho : o ≤ o*b := Nat.le_mul_of_pos_right _ hb
  have n : 8+4*k+2*u+o*(b+1) ≤ 2*packetWords k u o b := by
    rw [Nat.mul_add,Nat.mul_one]; unfold packetWords; omega
  apply (GeometryAdvice.Allocation.stop_le ..).trans
  apply Nat.add_le_add_left
  calc
    _ ≤ (2*packetWords k u o b)*(3*w) := by gcongr; omega
    _ = _ := by ring

/-- With the directory at the first free address and geometry placed immediately
after its maximum capacity, their combined end and all intervening writes fit below
the machine word modulus. The remaining interval beyond this end can be made any
fixed fraction of the reserved `r*n` words. -/
theorem eventually_geometry_stop {α τ : ℝ} (ha : 0 < α) (ha' : α < 1/1000) (ht : 0 ≤ τ)
    {K : ℕ} (hK : 1 ≤ K) (growth : τ*Real.logb 2 K ≤ α) (A : ℝ) (factor : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (r V base u k o b w : ℕ) (D : Packing.Directory.Layout),
      D.teams = teams α τ K n → D.processors = r → D.entries = K^epochs τ n*V → D.fields = 2 →
      0 < D.block → r*D.literal ≤ V*D.block → (V:ℝ) ≤ A*r*(n:ℝ)^(9/10:ℝ) →
      1 ≤ b → 1 ≤ w → packetWords k u o b*w ≤ r*width n (95/100:ℝ) →
      let stop := GeometryAdvice.Allocation.stop (base+7*D.candidates) u k o b w
      factor*(stop-base) ≤ r*n ∧ (0 < factor → base+r*n < 2^w → stop < 2^w) := by
  have geom := eventually_rpow_gap (by norm_num : (95/100:ℝ) < 1) ((factor:ℝ)*12)
  filter_upwards [eventually_raw_demand ha ha' ht hK growth A (2*factor),geom] with n raw room
  intro r V base u k o b w D ts ps cnt fs bk lit cap hb hw serialized stop
  have rc := raw r V D ts ps cnt fs bk lit cap
  rw [Real.rpow_one] at room
  have half : 12*factor*width n (95/100:ℝ) ≤ n := by
    have round : (width n (95/100:ℝ):ℝ) ≤ (n:ℝ)^(95/100:ℝ) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    rw [Nat.mul_comm 12 factor]
    exact_mod_cast (mul_le_mul_of_nonneg_left round (show 0 ≤ (factor:ℝ)*12 by positivity)).trans room
  have gc : 2*factor*(6*(packetWords k u o b*w)) ≤ r*n := by
    calc
      _ ≤ 2*factor*(6*(r*width n (95/100:ℝ))) := by gcongr
      _ = r*(12*factor*width n (95/100:ℝ)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ half
  have endRoom := geometry_stop_le base D.candidates u k o b w hb hw
  change stop ≤ base+7*D.candidates+6*(packetWords k u o b*w) at endRoom
  have scale : 2*factor*(stop-base) ≤ 2*(r*n) := by
    calc
      _ ≤ 2*factor*(7*D.candidates+6*(packetWords k u o b*w)) := by gcongr; omega
      _ = 2*factor*(7*D.candidates)+2*factor*(6*(packetWords k u o b*w)) := Nat.mul_add ..
      _ ≤ _ := by omega
  have bound : factor*(stop-base) ≤ r*n := by rw [Nat.mul_assoc] at scale; omega
  exact ⟨bound,fun pos fit => by have h := (Nat.le_mul_of_pos_left (stop-base) pos).trans bound; omega⟩

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
