import OAI.ThreeFlat.RAM.TickAgeSpace
import OAI.ThreeFlat.Diagonal.TraceVolumePins

namespace OAI
/-! # Scratch and coefficient-table capacity at every sufficiently large age -/

namespace ThreeFlat.RAM.TickPhysicalABI
open Contraction BitLayout Diagonal.TickWorkspace Diagonal.ApproximateImage Diagonal.TraceVolume
open TickActiveROM

variable {F : Type*} [Field F] [Fintype F]

theorem mounted_space {u e nt ns np teams cap : ℕ} (age : cm ≤ u) (large : 16 ≤ u)
    (exponent : e ≤ u) (params : 2+nt+ns+np ≤ u^e)
    (field : Fintype.card F * Fintype.card F ≤ u) :
    let q := 2^(u^3)
    let a := 2^(u^10-u^4)
    let m := 2^(u^10)/u^cm
    let H := m/40000
    let J := 2*H
    let p := pinCount q nt ns np a
    ∃ fit : Fits (TickWeightedBank.shape F p H J) (16*u^10),
      WordBounds (mounted u a teams cap q nt ns np) fit := by
  intro q a m H J p
  let V := 2^(u^10)
  have uV : u ≤ V := (Nat.le_self_pow (by decide : 10≠0) u).trans Nat.lt_two_pow_self.le
  have fieldRoom := field.trans uV
  have pinsBound := (pins_at_scale age exponent params).2
  have pinRoom : 2+p ≤ V := by
    have ht : 2^(u^10-2*u) ≤ V := Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
    dsimp only [p,q,a,pinCount]
    omega
  have mm : m ≤ V := Nat.div_le_self _ _
  have h : 40000*H ≤ m := by simpa [H,mul_comm] using Nat.div_mul_le_self m 40000
  have hid : H ≤ V := by omega
  have cell : J ≤ V := by dsimp [J]; omega
  have low : footprint (TickWeightedBank.shape F p H J) < stride u :=
    low_frame large (by omega) hid cell fieldRoom
  have pr : 0 < stride u := by unfold stride; positivity
  have space := word_space (show 1 ≤ u by omega) (show 0 < stride u from pr)
  have all : stride u < 2^(16*u^10) := by have h := lower u 0; omega
  have fit : Fits (TickWeightedBank.shape F p H J) (16*u^10) := low.le.trans all.le
  exact ⟨fit,word_bounds large pinRoom hid cell fieldRoom fit⟩

theorem catalog_fits {u : ℕ} (large : 16 ≤ u) {t : ℕ} (count : 8*t ≤ u) :
    base u 10+8*t < 2^(16*u^10) := by
  have uV : u ≤ 2^(u^10) := (Nat.le_self_pow (by decide : 10≠0) u).trans Nat.lt_two_pow_self.le
  have wide : 2^(u^10) ≤ stride u := Nat.le_self_pow (by decide : 4≠0) _
  have room := word_space (show 1 ≤ u by omega) (show 10 < stride u by omega)
  omega

end ThreeFlat.RAM.TickPhysicalABI

end OAI
