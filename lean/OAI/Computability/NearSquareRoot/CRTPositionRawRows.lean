import OAI.Computability.NearSquareRoot.CRTControlledRowPackets
import OAI.Computability.NearSquareRoot.CRTControlledSizes

/-! # Linear-space rows with low addresses packed during the scan -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionRows
open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Strip IntegerMultiplication.Code
open NearSquareRoot.Space

private theorem powFits {q s d D n : ℕ} (le : s ≤ q) (dD : d ≤ D) (cut : payloadBits D q ≤ n) :
    (s+1)^d ≤ 2^n := by
  calc
    _ ≤ (q+1)^d := Nat.pow_le_pow_left (Nat.succ_le_succ le) _
    _ ≤ (q+1)^D := Nat.pow_le_pow_right (by omega) dD
    _ ≤ 2^(payloadBits D q) := by simpa using payload_capacity D q 1 (by decide)
    _ ≤ _ := Nat.pow_le_pow_right (by decide) cut

/-- The carving program sees each raw low-address record, whereas its expensive
inner algorithm sees one record per middle address. The high reserve pays for
the raw ruler and each row still has exactly its original bit volume. -/
theorem rawRowsOn {X : Type} {r : Regime X} (hi mid lo k m : X → ℕ)
    (size : ∀ x, hi x + (mid x + lo x) = k x)
    (hHi : r.Has (tally ∘ hi)) (hRaw : r.Has (fun x => tally (mid x+lo x)))
    (view : (x : X) → Adopt ((line 2 (hi x)).cart (line 2 (mid x+lo x))) (line 2 (k x)))
    (f g : (x : X) → Block 2 (k x) → Tree)
    (input : ∀ x a, (f x a).count ≤ 2*m x+1) (output : ∀ x a, (g x a).count ≤ 2*m x+1)
    (rate : X → ℝ)
    (row : Breeze (fun z => rate z.1) (fixedRowRegime r hi hHi)
      (fun z => 2^(mid z.1)) (fun z => 2^(lo z.1)*m z.1)
      (fun z => Tree.fork ((fixedRowRegime r hi hHi).header z)
        (stripe (line 2 (mid z.1+lo z.1)) fun b => f z.1 ((view z.1).cast (z.2,b))))
      (fun z => stripe (line 2 (mid z.1+lo z.1)) fun b => g z.1 ((view z.1).cast (z.2,b)))) :
    ∃ D : ℕ, ∀ {Y : Type} (pick : Y → X) (Q factor : Y → ℕ),
      (∀ y, r.scale (pick y) ≤ Q y) → (∀ y, hi (pick y) ≤ Q y) → (∀ y, 0 < m (pick y)) →
      (∀ y, payloadBits D (Q y) ≤ lo (pick y)) →
      (∀ y, payloadBits D (Q y) ≤ hi (pick y)) →
      (∀ y, 2 * rate (pick y) ≤ factor y) → (∀ y, factor y ≤ 2^(hi (pick y))) →
      let V y := 2^(k (pick y))*m (pick y)
      BoundedTask (fun y => V y*(factor y+1)) V
        (together r.header (stackRun (fun x => line 2 (k x)) f) ∘ pick)
        (stackRun (fun x => line 2 (k x)) g ∘ pick) := by
  obtain ⟨d,e,run⟩ := packedPrefixRowsOn hi (fun x => mid x+lo x) k hHi hRaw view f g row
  obtain ⟨p,C,hHeader⟩ := r.gauge
  let D := d+e+p+1
  refine ⟨D,?_⟩
  intro Y pick Q factor scale hiQ hm low high hr room
  let V y := 2^(k (pick y))*m (pick y)
  let H y := 2^(hi (pick y))
  let N y := 2^(mid (pick y)+lo (pick y))
  let W y := N y*m (pick y)
  let constant := C+12
  have form y : H y*W y = V y := by
    dsimp only [V,H,N,W]; rw [← Nat.mul_assoc,←pow_add,size]
  have pos y : 1 ≤ W y := Nat.mul_pos (Nat.two_pow_pos _) (hm y)
  have area y : V y ≤ constant*V y := Nat.le_mul_of_pos_left _ (by dsimp [constant]; omega)
  have raw y : 2^(lo (pick y)) ≤ W y := by
    exact (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)).trans (Nat.le_mul_of_pos_right _ (hm y))
  have metadata y : max (H y) (N y) * (r.scale (pick y)+1)^e ≤ constant*V y := by
    have t := powFits (scale y) (by dsimp [D]; omega : e ≤ D) (low y)
    have b := powFits (scale y) (by dsimp [D]; omega : e ≤ D) (high y)
    apply le_trans _ (area y)
    rw [←form, max_mul_of_nonneg _ _ (Nat.zero_le _)]
    apply max_le (Nat.mul_le_mul_left _ (t.trans (raw y)))
    calc
      _ ≤ N y*H y := Nat.mul_le_mul_left _ b
      _ = H y*N y := Nat.mul_comm ..
      _ ≤ H y*W y := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (hm y))
  have packets y : H y*((r.header (pick y)).count+2*hi (pick y)+N y*(2*m (pick y)+1+1)+5)+1 ≤ constant*V y := by
    have bounded := (powFits (scale y) (by dsimp [D]; omega : p≤D) (low y)).trans (raw y)
    have header : (r.header (pick y)).count ≤ C*W y := (hHeader (pick y)).trans (Nat.mul_le_mul_left C bounded)
    have hiFits : hi (pick y) ≤ W y := by
      have b := powFits (le_refl (Q y)) (by dsimp [D]; omega : 1 ≤ D) (low y)
      rw [pow_one] at b
      exact (hiQ y).trans ((Nat.le_succ _).trans (b.trans (raw y)))
    have cells : N y*(2*m (pick y)+1+1) ≤ 4*W y := by
      calc
        _ ≤ N y*(4*m (pick y)) := Nat.mul_le_mul_left _ (by have := hm y; omega)
        _ = _ := by dsimp [W]; ring
    have each : (r.header (pick y)).count+2*hi (pick y)+N y*(2*m (pick y)+1+1)+5 ≤ (C+11)*W y := by
      rw [Nat.add_mul]; have := pos y; omega
    have a := Nat.mul_le_mul_left (H y) each
    rw [Nat.mul_left_comm (H y) (C+11),form] at a
    have vpos : 1 ≤ V y := (form y) ▸ Nat.mul_pos (Nat.two_pow_pos _) (pos y)
    change _ ≤ (C+11+1)*V y
    rw [Nat.succ_mul (C+11) (V y)]
    exact (Nat.succ_le_succ a).trans (Nat.add_le_add_left vpos _)
  have F := run pick factor (fun y => constant*V y) Q (fun y => m (pick y)) W
    (fun y => 2*m (pick y)+1) scale hm
    (fun y _ => Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) ((show payloadBits d (Q y) ≤
      payloadBits D (Q y) from Nat.mul_le_mul_right _ (by dsimp [D]; omega)).trans (low y))))
    (fun y _ => by dsimp only [W,N]; rw [pow_add,Nat.mul_assoc])
    (fun y _ => hr y) metadata (fun y => input (pick y)) (fun y => output (pick y))
    packets (fun y => (form y).le.trans (area y)) room
  apply F.bound constant constant
  · intro y
    change (constant*V y)*(factor y+1)+1 ≤ constant*(V y*(factor y+1)+1)
    rw [Nat.mul_assoc,Nat.mul_succ constant (V y*(factor y+1))]; have : 0 < constant := by dsimp [constant]; omega
    omega
  · intro y; change constant*V y+1 ≤ constant*(V y+1)
    rw [Nat.mul_succ constant (V y)]; have : 0 < constant := by dsimp [constant]; omega
    omega

end Controlled.PositionRows

end NearSquareRoot
end Computability
end OAI
