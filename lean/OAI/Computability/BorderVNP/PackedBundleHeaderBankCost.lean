import OAI.Computability.BorderVNP.PackedBundleRoutingReturn
import OAI.Computability.BorderVNP.PackedFrozenLayerCost

/-! # Cubic gate bound for the physical original-report header banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.BundleSort

open RoutingISA CellAddressCircuit CellPacketGeometry CellPacketGeometry.LiveWords
open Inherited Inherited.FrozenTape ParseBatchSort PackedHistogram VPVNP.VerifierNetwork

variable {s m n C d k w J W R : ℕ} {σ : Type*} [Fintype σ]

/-- The public description scan includes the actual power-of-two padding,
both Batcher passes and the per-key prefix additions. -/
private theorem descriptionPrefix_cubic (desc : ℕ) (rows : J+1≤R)
    (widths : k≤W ∧ w≤W ∧ Nat.clog 2 R≤W) :
    (descriptionPrefix J k w desc).size ≤ 1001*R*(W+1)^3 := by
  obtain ⟨hk,hw,hl⟩ := widths
  let b := Nat.clog 2 J
  have hb : b ≤ W := (Nat.clog_mono_right 2 (show J≤R by omega)).trans hl
  have padded : 2^b ≤ 2*R := (pow_clog_le J).trans (Nat.mul_le_mul_left 2 rows)
  let per := (k+w)+(((w+b)+1+k) + b^2*(24*((w+b)+1+k)+1) +
    w*(60*k+40*w+63) + b^2*(24*(w+b)+1))
  have bound : per ≤ 500*(W+1)^3 := by
    calc
      _ ≤ (W+W)+(((W+W)+1+W) + W^2*(24*((W+W)+1+W)+1) +
        W*(60*W+40*W+63) + W^2*(24*(W+W)+1)) := by dsimp only [per]; gcongr
      _ ≤ _ := by nlinarith only [Nat.zero_le (W^3),Nat.zero_le (W^2),Nat.zero_le W]
  have src := descriptionPrefix_size J k w desc
  have h : (descriptionPrefix J k w desc).size ≤ 2^b*per+1 := src.trans_eq (by dsimp only [b,per]; ring)
  have charge := Nat.mul_le_mul padded bound
  have pos : 0 < R*(W+1)^3 := Nat.mul_pos (by omega) (by positivity)
  calc
    _ ≤ 2^b*per+1 := h
    _ ≤ 2*R*(500*(W+1)^3)+1 := Nat.add_le_add_right charge 1
    _ ≤ _ := by simp only [Nat.mul_assoc,Nat.mul_left_comm R 500]; omega

private theorem viewOffsets_cubic (F : Fields s m n C d k w σ)
    (rows : 1+CellAddressCircuit.count s m n C≤R) (widths : d≤W ∧ k≤W ∧ w≤W ∧ Nat.clog 2 R≤W) :
    (CellAddressViews.frame F).size + (SuppliedOffsets.frame F).size ≤ 8500*R*(W+1)^3 := by
  obtain ⟨hd,hk,hw,hl⟩ := widths
  have views := LayerRows.cellView_cubic F rows ⟨hd,hk,hw,hl⟩
  have labelRows : s+(m+m+n)+1 ≤ R := by unfold CellAddressCircuit.count at rows; omega
  have ptrRows : C+(m+m+n)+1 ≤ R := by unfold CellAddressCircuit.count at rows; omega
  have logAt (v : ℕ) (fit : v ≤ R) := (Nat.clog_mono_right 2 fit).trans hl
  have label : (labels F).size ≤ 1000*R*(W+1)^3 := by
    apply (labels_size F).trans
    apply (lookupCost_cubic s (m+m+n) d k W (logAt _ (by omega)) hd hk).trans
    gcongr
  have ptr : histogramBudget C (m+m+n) k w ≤ 1000*R*(W+1)^3 := by
    apply (lookupCost_cubic C (m+m+n) k w W (logAt _ (by omega)) hk hw).trans
    gcongr
  have bit : w*(100*(w+1)) ≤ 100*(W+1)^3 := by
    calc
      _ ≤ W*(100*(W+1)) := by gcongr
      _ ≤ _ := by nlinarith only [Nat.zero_le (W^3),Nat.zero_le (W^2),Nat.zero_le W]
  have word := Nat.mul_le_mul (show (m+m+n)+C ≤ R by omega) bit
  have off := SuppliedOffsets.frame_size F
  change (SuppliedOffsets.frame F).size ≤ (CellAddressViews.frame F).size + (labels F).size +
    histogramBudget C (m+m+n) k w + ((m+m+n)+C)*w*(100*(w+1)) at off
  rw [Nat.mul_assoc ((m+m+n)+C)] at off
  rw [show R*(100*(W+1)^3)=100*R*(W+1)^3 by ring] at word
  simp only [Nat.mul_assoc] at views label ptr word ⊢
  omega

variable (banks : CellBanks.Layout) (F : Fields s m n banks.cells d k w σ)

/-- The installed header banks include the cell views, marker source,
original relative and absolute pointers, actual per-row fields, and both
stable-sort output banks. The supplied validity frame is shared once. -/
theorem headerBanks_cubic (old : Fin J → Fin s) (desc gap : ℕ) (shape : Fin J → Shape)
    (valid : Frame σ Unit) (rows : 1+CellAddressCircuit.count s m n banks.cells+J+n ≤ R)
    (widths : d≤W ∧ k≤W ∧ w≤W ∧ Nat.clog 2 R≤W) :
    let b := Nat.clog 2 (banks.cells+6*J+banks.cells)
    (headerBanks banks F b old desc gap shape valid).size ≤ valid.size+1000000*R*(W+1)^3 := by
  intro b
  obtain ⟨hd,hk,hw,hl⟩ := widths
  let C := banks.cells
  let U := R*(W+1)^3
  have raw : 1+CellAddressCircuit.count s m n C ≤ R := by change 1+CellAddressCircuit.count s m n C+J+n≤R at rows; omega
  have rc : C+J+1≤R := by change 1+CellAddressCircuit.count s m n C+J+n≤R at rows; unfold CellAddressCircuit.count at rows; omega
  have hr : 0<R := by omega
  have hu : 0<U := Nat.mul_pos hr (by positivity)
  have sc (a : ℕ) : a*R*(W+1)^3 = a*U := Nat.mul_assoc ..
  have cfg := bankConfig_size (w:=w) banks gap valid
  have pre := descriptionPrefix_cubic desc (show J+1≤R by omega) ⟨hk,hw,hl⟩
  have views := viewOffsets_cubic F raw ⟨hd,hk,hw,hl⟩
  have inputWords : C*w ≤ U := by
    have word : w ≤ (W+1)^3 := by nlinarith only [hw,Nat.zero_le (W^3),Nat.zero_le (W^2),Nat.zero_le W]
    exact Nat.mul_le_mul (by omega) word
  have terms (j c : ℕ) (jr : j≤R) (cr : c≤R) :
      (j*(k+6*w)+(c*w+1))*(100*(w+1)) ≤ 1000*U := by
    calc
      _ ≤ (R*(W+6*W)+(R*W+R))*(100*(W+1)) := by gcongr; omega
      _ = R*((W+6*W+W+1)*(100*(W+1))) := by ring
      _ ≤ R*(1000*(W+1)^3) := by apply Nat.mul_le_mul_left; nlinarith only [Nat.zero_le (W^3),Nat.zero_le (W^2),Nat.zero_le W]
      _ = _ := by unfold U; ring
  have ops := geometryOperands_size F old desc (bankConfig banks gap valid)
  have inner := terms J C (by omega) (by omega)
  have short : (J*(k+2*w)+(C*w+1))*(100*(w+1)) ≤ 1000*U := by apply le_trans _ inner; gcongr; omega
  have headers := headerFrame_size F.cells shape (geometryOperands F old desc (bankConfig banks gap valid))
  have hist : histogramBudget C J k w ≤ 1000*U := by
    apply (lookupCost_cubic C J k w W ((Nat.clog_mono_right 2 (by omega : C+J≤R)).trans hl) hk hw).trans
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 1000 rc)).trans_eq (sc _)
  have tail := terms J 0 (by omega) (by omega)
  have heads : (geometryHeaders F old desc (bankConfig banks gap valid) shape).size ≤ valid.size+14000*U := by
    change (headerFrame F.cells shape _).size ≤ _
    rw [sc] at pre views
    change _ ≤ valid.size+C*w+1 at cfg
    dsimp only [C] at hist short
    simp only [Nat.zero_mul,Nat.zero_add] at tail
    omega
  have marker : C+6*J+C+1 ≤ 8*R := by omega
  have pad : 2^b ≤ 16*R := (pow_clog_le _).trans ((Nat.mul_le_mul_left 2 marker).trans_eq (by ring))
  have hb : b ≤ W+3 := by
    apply Nat.clog_le_of_le_pow
    have rp := (Nat.le_pow_clog (by decide : 1<2) R).trans (Nat.pow_le_pow_right (by decide) hl)
    exact (by simpa only [pow_add,show (2:ℕ)^3=8 by decide,Nat.mul_comm 8] using
      (show C+6*J+C ≤ 8*2^W from (by omega : C+6*J+C≤8*R).trans (Nat.mul_le_mul_left 8 rp)))
  let h := geometryHeaders F old desc (bankConfig banks gap valid) shape
  have rawSource := source_size C b h
  have stage := sort_cubic (k:=k) (w:=w) hb (by omega) (by omega)
  have cube : (W+3+1)^3 ≤ 64*(W+1)^3 := (Nat.pow_le_pow_left (by omega : W+3+1≤4*(W+1)) 3).trans_eq (by ring)
  have net := (Nat.mul_le_mul pad (Nat.mul_le_mul_left 500 cube)).trans_eq
    (by unfold U; ring : 16*R*(500*(64*(W+1)^3)) = 512000*U)
  have small : k+w≤2*(W+1)^3 := by nlinarith only [hk,hw,Nat.zero_le (W^3),Nat.zero_le (W^2),Nat.zero_le W]
  have wiring := (Nat.mul_le_mul pad small).trans_eq (by unfold U; ring : 16*R*(2*(W+1)^3)=32*U)
  rw [sc]
  change (geometry (source C b h)).size ≤ valid.size+1000000*U
  rw [geometry_size]
  change h.size ≤ valid.size+14000*U at heads
  omega

/-- Emitting the two complete banks charges all their physical word bits,
including the rows beyond the final real header marker. -/
theorem headerBanks_bits (old : Fin J → Fin s) (desc gap : ℕ) (shape : Fin J → Shape)
    (valid : Frame σ Unit) (rows : 1+CellAddressCircuit.count s m n banks.cells+J+n ≤ R)
    (widths : d≤W ∧ k≤W ∧ w≤W ∧ Nat.clog 2 R≤W) :
    let b := Nat.clog 2 (banks.cells+6*J+banks.cells)
    (headerBanks banks F b old desc gap shape valid).size + (2^b+2^b)*w ≤
      valid.size + 1000032*R*(W+1)^3 := by
  intro b
  have gates := headerBanks_cubic banks F old desc gap shape valid rows widths
  have marker : banks.cells+6*J+banks.cells+1 ≤ 8*R := by unfold CellAddressCircuit.count at rows; omega
  have pad : 2^b ≤ 16*R := (pow_clog_le _).trans ((Nat.mul_le_mul_left 2 marker).trans_eq (by ring))
  have word : w ≤ (W+1)^3 := by nlinarith only [widths.2.2.1,Nat.zero_le (W^2),Nat.zero_le (W^3),Nat.zero_le W]
  have bits := Nat.mul_le_mul (show 2^b+2^b≤32*R by omega) word
  change (headerBanks banks F b old desc gap shape valid).size ≤ _ at gates
  simp only [Nat.mul_assoc] at gates bits ⊢
  omega

end Packing.BottomReports.BundleSort

end BorderVNP
end Computability
end OAI
