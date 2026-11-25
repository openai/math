import OAI.Hierarchy.DescentEstimatorProgramBill
import OAI.Hierarchy.DescentGlobalControlRoom

namespace OAI
/-! # Once per dated estimator, the common GL program and literal dictionaries fit the reserved public budget -/
namespace Hierarchy.DescentPackedWalsh.EstimatorArena
open DescentPackedWalshReduction DescentCompiler Filter
variable (E : EstimatorArena)
private def remaining (m b h W K d Q solve rom : ℕ) :=
  let words := 4*W+6*(0+1)*(W+16*K*b*Q)+
    (4*W+2008*(0+1)*W+25600*K*(0+1)*Q*(b+1)+12800*K*Q*(W+1)^2)
  let advice:=rom*W
  115*(K*((8*m+12)*h)+4*W+
    (m+1)*(4*W+words+(4+Q*60)*W)+4000*solve*W+
    (2*K*h+2*advice)+
    (4*W+2008*W+25600*K*Q*(b+1)+12800*K*Q*(W+1)^2+2*d*advice)+
    (2*Q*W+advice)+K*(6*m*h+(2*m+1)*rom*h))+
    (109+7*(116+366*m+(m+1)*(351+183*d)+8000*solve))*W

section
local notation "k" => E.dim
local notation "h" => E.payload
local notation "b" => E.precision
local notation "d" => E.plan.depth

theorem common_bound (W K D : ℕ) (size : k≤D) (precision : b≤D) (pay : h≤D)
    (word : W≤D) (ratio : K≤D) (depth : d≤D) :
    115*E.commonBill W K+(109+7*E.controlNames)*W ≤
      50000000*(D+1)^5*2^(5*k)*2^(h/2) := by
  change remaining k b h W K d (2^k) (2^(5*k)) (2^(h/2))≤_
  have q : 2^k≤2^(5*k) := Nat.pow_le_pow_right (by decide) (by omega)
  have mono : remaining k b h W K d (2^k) (2^(5*k)) (2^(h/2))≤
      remaining D D D D D D (2^(5*k)) (2^(5*k)) (2^(h/2)) := by
    unfold remaining
    dsimp only
    gcongr
  apply mono.trans
  obtain ⟨x,eqx⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.two_pow_pos (5*k)).ne'
  obtain ⟨y,eqy⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.two_pow_pos (h/2)).ne'
  rw [eqx,eqy]
  simp only [Nat.succ_eq_add_one]
  unfold remaining
  ring_nf
  omega

end

/-- This part of each real dated estimator has a single shared cost even when its fixed
lookup words and original instruction text are both counted explicitly. -/
theorem common_funded (C D F K : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀J M : ℕ,J≤Nat.log 2 h→2^h≤M→∀E : EstimatorArena,∀w r : ℕ,
    E.payload=h→E.dim≤K*(J+1)^2→E.dim≤D*(h+1)→E.precision≤D*(h+1)→h≤D*(h+1)→
    w≤D*(h+1) → r≤D*(h+1)→E.plan.depth≤D*(h+1)→
    C*(115*E.commonBill w r+(109+7*E.controlNames)*w)≤M/(2^J)^F := by
  filter_upwards [global_control_shared (C*50000000*(D+1)^5) 5 (5*K) 2 F] with h shared
  intro J M age ambient E w r pay dim fast prec width word ratio depth
  have envelope:=E.common_bound w r (D*(h+1)) fast prec (by simpa only [pay] using width) word ratio depth
  have e : 5*E.dim≤(5*K)*(J+1)^2 := by nlinarith only [Nat.mul_le_mul_left 5 dim]
  have room:=shared J (5*E.dim) M age e ambient
  have polynomial : (D*(h+1)+1)^5≤(D+1)^5*(h+1)^5 := by
    rw [←mul_pow]
    apply Nat.pow_le_pow_left
    nlinarith
  rw [pay] at envelope
  calc
    _ ≤ C*(50000000*(D*(h+1)+1)^5*2^(5*E.dim)*2^(h/2)) := Nat.mul_le_mul_left C envelope
    _ ≤ (C*50000000*(D+1)^5*(h+1)^5*2^(5*E.dim))*2^(h/2) := by
      calc
        _ ≤ C*(50000000*((D+1)^5*(h+1)^5)*2^(5*E.dim)*2^(h/2)) := by gcongr
        _ = _ := by ring
    _ ≤ _ := room

end Hierarchy.DescentPackedWalsh.EstimatorArena

end OAI
