import OAI.Computability.BorderVNP.TeamSiteConsistencyPaths
import OAI.Computability.BorderVNP.TeamContractionWireScale

/-! # Instantiating the team path bijection at the paper's exact clock and widths

A single sufficiently large input length works for every positive team size. The native
word width is a positive integral power of the rounded binary logarithm of the global
input capacity. The extra physical bit holds the paired-record phase ordinal.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteConsistency

open VPVNP TeamScales TeamContraction.Wires Filter
open BurstRAM (Word)

/-- Numerical range of every public field and physical block of the one-team path bijection. -/
structure Geometry (teams n p w H q T e : ℕ) : Prop where
  /-- Finite native program counter fits. -/
  pcs : p ≤ 2^w
  /-- Physical tags fit. -/
  width : 2 ≤ w+1
  /-- Charged local block length fits its logical word. -/
  blockWord : H < 2^w
  /-- Largest private burst fits its logical word. -/
  capWord : q < 2^w
  /-- Entire global tick cutoff fits its logical word. -/
  tickWord : T < 2^w
  /-- Every virtual sorter index fits the phase-extended width. -/
  sorter : 2^(Nat.clog 2 teams)*2^e < 2^(w+1)
  /-- All real local initialized memory words fit in the shared logical address space. -/
  header : teams*(3*H) ≤ 2^w
  /-- Physical slot allocation accommodates paired read/write records. -/
  rowCapacity : 2*H ≤ 2^e
  /-- The greedy charged schedule admits the entire native cutoff. -/
  schedule : T ≤ teams*(H-q)
  /-- Padded local sorter block parameter fits within processor input length. -/
  localSort : 2^e ≤ n

/-- All RAM and physical-sorter word hypotheses hold uniformly in the real team size at
the paper's exact rounded time, burst, local-block and polylogarithmic word widths. -/
theorem eventually_setupGeometry {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 3/2) (p D : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ teams : ℕ, 0 < teams →
      Geometry teams n p (logWidth teams n^(D+1)) (block ξ n) (width n (1/2))
        (ticks ξ teams n) (sortExponent (block ξ n)) := by
  filter_upwards [eventually_rpow_gap (show 1-ξ/3 < 1 by linarith) 4,
    eventually_ticks_fit hξ hξ', eventually_ge_atTop (max p 2)] with n sub schedule hn
  intro teams ht
  have hnpos : 0 < n := by omega
  let H := block ξ n
  let L := logWidth teams n
  let w := L^(D+1)
  have floor := Nat.floor_le (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) (1-ξ/3))
  change (H : ℝ) ≤ (n : ℝ)^(1-ξ/3) at floor
  rw [Real.rpow_one] at sub
  have four : 4*H ≤ n := by exact_mod_cast (show 4*(H : ℝ) ≤ n by linarith)
  have pack := schedule teams ht
  change ticks ξ teams n < teams*(H-width n (1/2)) at pack
  have qlt : width n (1/2) < H := by
    by_contra! no
    rw [Nat.sub_eq_zero_of_le no, Nat.mul_zero] at pack
    omega
  have hL : L = Nat.clog 2 (2*n*teams) := by
    unfold L logWidth; rw [← Real.natCeil_logb_natCast]; norm_cast
  have scale : 2*n*teams ≤ 2^L := hL ▸ Nat.le_pow_clog (by decide) _
  have positive : 0 < L := by
    by_contra! hz
    have eq : L=0 := by omega
    rw [eq,pow_zero] at scale
    have := Nat.le_mul_of_pos_right (2*n) ht
    omega
  have lower : L ≤ w := by
    dsimp [w]; rw [pow_succ]; exact Nat.le_mul_of_pos_left _ (pow_pos positive _)
  have bound := scale.trans (Nat.pow_le_pow_right (by decide : 0<2) lower)
  have big : n < 2^w := by have := Nat.le_mul_of_pos_right (2*n) ht; omega
  have dpad := TeamSorting.padding_lt_twice ht
  have epad := TeamSorting.padding_lt_twice (show 0<2*H by omega)
  have localSort : 2^sortExponent H ≤ n := by unfold sortExponent; omega
  change Geometry teams n p w H (width n (1/2)) (ticks ξ teams n) (sortExponent H)
  refine ⟨by omega, by omega, by omega, by omega,
    (TeamTapeHandoff.ticks_fit_word hξ.le hnpos ht).trans_le (Nat.pow_le_pow_right (by decide) lower),
    ?_,?_,Nat.le_pow_clog (by decide) _,pack.le,localSort⟩
  · calc
      2^Nat.clog 2 teams * 2^sortExponent H < (2*teams)*2^sortExponent H :=
        Nat.mul_lt_mul_of_pos_right dpad (Nat.two_pow_pos _)
      _ ≤ (2*teams)*n := Nat.mul_le_mul_left _ localSort
      _ = 2*n*teams := by ring
      _ ≤ 2^w := bound
      _ ≤ 2^(w+1) := Nat.pow_le_pow_right (by decide) (by omega)
  · calc
      teams*(3*H) ≤ teams*(2*n) := Nat.mul_le_mul_left _ (by omega)
      _ = 2*n*teams := by ring
      _ ≤ 2^w := bound

/-- Concatenating all real header chunks respects their common per-processor input cap. -/
theorem header_length_le {teams B : ℕ} (input : Fin teams → List Bool) (fit : ∀ j, (input j).length ≤ B) :
    (List.ofFn input).flatten.length ≤ teams*B := by
  induction teams with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.flatten_cons,List.length_append,Nat.succ_mul]
    have h := ih (fun j => input j.succ) (fun j => fit j.succ)
    have head := fit 0
    omega

/-- Supply the native machine, its actual input bits, and the private clock to the
verified path bijection with all numerical obligations discharged by the paper's geometry. -/
def Geometry.setup {teams n p w H q T e r k a : ℕ} (geo : Geometry teams n p w H q T e)
    (hr : 0 < teams) (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : TeamOpcode.Macros w a)
    (start : TeamOpcode.State w p r) (privateClock : ℕ) (input : Fin teams → List Bool)
    (own : ∀ j, (input j).length ≤ 3*H) : Setup teams w p r k a e :=
  ⟨P,pub,lib,start,⟨H,geo.blockWord⟩,⟨T,geo.tickWord⟩,⟨q,geo.capWord⟩,privateClock,input,hr,geo.pcs,
    geo.width,geo.sorter,(header_length_le input own).trans geo.header,own,geo.rowCapacity,geo.schedule⟩

end TeamSiteConsistency

end BorderVNP
end Computability
end OAI
