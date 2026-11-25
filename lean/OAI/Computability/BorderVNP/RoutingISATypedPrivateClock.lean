import OAI.Computability.BorderVNP.RoutingISATypedNativeValue
import OAI.Computability.BorderVNP.CellPrivateCompilePhysical

/-! # Uniform clock of the concrete private machine on genuine sparse cells

The typed compiler, private generator and bytecode execution all use their
measured finite-code bounds. A threshold and stretching exponent are chosen
before the batch, the public directory, the exterior bits and the field values.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedBatch

open Filter TeamScales CellMacro CellMacro.Generator CellSparse CompactMachine VPVNP.BurstRAM

private theorem small_width {n : ℕ} (hn : 1 ≤ n) (x : ℝ) (hx : x ≤ 1) : width n x ≤ n := by
  have h := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (show 1 ≤ (n:ℝ) by exact_mod_cast hn) hx)
  simpa only [width,Real.rpow_one,Nat.floor_natCast] using h

private theorem compact_digits {n r M E : ℕ} (hr : 1 ≤ r) (hM : M ≤ n) (hE : E ≤ n) :
    (4*(M+E+1)^3).size+1 ≤ 10*(logWidth r n+1) := by
  have le : 4*(M+E+1)^3 ≤ 32*(n+2)^3 := by
    have a := Nat.pow_le_pow_left (show M+E+1 ≤ 2*(n+2) by omega) 3
    rw [mul_pow] at a
    omega
  have h := size_of_polynomial_field le
  have d := size_le_logWidth n r hr
  norm_num [show (32:ℕ).size=6 by decide] at h
  omega

/-- The real typed routine fits both private limits, and its exact path sum equals
the cell contraction, solely from the public format, raw field width and actual
cell size constraints. No execution-clock or compiler-run premise is needed. -/
theorem eventually_private_cell (A T B j H R k : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r M E w U : ℕ, 1 ≤ r →
      (r:ℝ) ≤ 2^((n:ℝ)^ω) → M ≤ width n (1/5) → E ≤ width n (1/4) → 0 < w → w ≤ n →
      ∀ c : CellInput, c.external.length ≤ E →
      c.directory.StaticBounds A M → c.directory.CompactFields c.privateWires (4*(M+E+1)^3) →
      c.directory.records.length ≤ 4*(M+E+1)^3 → c.directory.reportedCounts.length ≤ 4*(M+E+1)^3 →
      Packet.storedMass c.directory ≤ A*(M+1)^2 →
      Packet.RawFields c.directory c.privateWires U → U.size+1 ≤ B*(logWidth r n+1)^j →
      (∀ rec ∈ c.directory.records, (Packet.record rec).length ≤ H) →
      (∀ fs ∈ c.directory.boxes, ∀ f ∈ fs, f.TableBound T) →
      (∀ bs ∈ c.directory.reportedCounts, bs.length ≤ R*(logWidth r n+1)^k) →
      c.directory.ProfileWidths →
      (CompactFrame.pack w (Packet.input c.directory c.privateWires c.external)).length ≤ width n (1/2) ∧
        cellClock w c ≤ n^25 ∧
        ∑ o ∈ choices cellDriver n (CompactFrame.pack w (Packet.input c.directory c.privateWires c.external)),
          o.2.value = c.weight := by
  obtain ⟨K,e,_,_,compile⟩ := CellPrivate.translateClock_physical A T B j 10 1 H R k
  let coeff := K+B+2
  let degree := max j e
  obtain ⟨ω,hω,physical⟩ := eventually_cell_resources A coeff degree
  refine ⟨ω,hω,?_⟩
  filter_upwards [physical,eventually_ge_atTop 1] with n bound hn
  intro r M E w U hr hrω hM hE hw hwn c hext hs hc hrec hrep hmass hraw hU hformat htable hbits hwidth
  let L := logWidth r n+1
  let X := M+E+1
  have hL : 1 ≤ L := by dsimp only [L]; omega
  have hX : 1 ≤ X := by dsimp only [X]; omega
  have bigJ := Nat.pow_le_pow_right hL (show j ≤ degree from le_max_left ..)
  have bigE := Nat.pow_le_pow_right hL (show e ≤ degree from le_max_right ..)
  have cubic := compact_digits hr (hM.trans (small_width hn _ (by norm_num))) (hE.trans (small_width hn _ (by norm_num)))
  have time := compile c.directory c.privateWires M E U (4*X^3) L hL hs hmass hraw hU hc
    (by simpa only [pow_one,X,L] using cubic) hformat htable hbits
  have boundTime : CellPrivate.translateClock c.directory c.privateWires ≤ coeff*X^96*L^degree :=
    time.trans (Nat.mul_le_mul (Nat.mul_le_mul (by dsimp [coeff]; omega)
      (Nat.pow_le_pow_right hX (show 63 ≤ 96 by decide))) bigE)
  have rawWords (v : ℕ) (hv : v ∈ Packet.words c.directory c.privateWires) : v.size ≤ coeff*L^degree := by
    have val := Packet.words_bounded _ _ hraw v hv
    rcases (max_choice 3 U) with eq|eq
    · rw [eq] at val
      have s := Nat.size_le_size val
      have hp : 1 ≤ L^degree := Nat.one_le_pow _ _ hL
      have cmin : 2 ≤ coeff := by dsimp [coeff]; omega
      exact s.trans ((show (3:ℕ).size ≤ coeff by exact cmin).trans (Nat.le_mul_of_pos_right _ hp))
    · rw [eq] at val
      have u : U.size ≤ B*L^j := (Nat.le_succ _).trans hU
      exact (Nat.size_le_size val).trans (u.trans (Nat.mul_le_mul (by dsimp [coeff]; omega) bigJ))
  obtain ⟨q,clock⟩ := bound r M E w hr hrω hM hE hw hwn c hext hs hc hrec hrep hmass rawWords boundTime
  exact ⟨q,clock,cell_value c hw hwidth clock⟩

end RoutingISA.TypedBatch

end BorderVNP
end Computability
end OAI
