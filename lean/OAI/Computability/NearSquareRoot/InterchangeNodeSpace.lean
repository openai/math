import OAI.Computability.NearSquareRoot.InterchangeExpose
import OAI.Computability.NearSquareRoot.InterchangeCenterEntry
import OAI.Computability.NearSquareRoot.InterchangeCenterSpace
import OAI.Computability.NearSquareRoot.InterchangeFatRecursion

/-! # Time and physical space for one recursive interchange node

The spectral calls run on the padded smaller rows. Each of the reserve
calls runs on the whole row and parks at most a logarithmic header forest.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress.Request

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic IntegerMultiplication.Loom NearSquareRoot.InterchangeFrame
  NearSquareRoot.InterchangeSpace NearSquareRoot.InterchangeSpectralFibre

variable {I F : Type} {b : ℕ} [NeZero b] (a m : ℕ) (xs : I → Request b)

/-- The main swap on the centered padded row bank, with a physical child-space budget. -/
abbrev BMain (digit : F → Tree) (W C : ℕ) :=
  ∀ (v : (i : I) → domain (b:=b) (J:=Fin (positions a m)) (north xs b) (aisle a m xs)
    (south a m xs) (localWidth a m xs) i → Tree),
    Manifest _ (payloadWidth xs) v → (∀ i k, record digit ((xs i).recordWidth) (v i k)) →
    BHop (job b) (regime xs) (fun i => (centerRows a m xs b i).count) (payloadWidth xs)
      (subZone a m xs digit W) C
      (together (regime xs).header (stackRun (centerRows a m xs b) v))
      (stackRun (centerRows a m xs b) (fun i => v i ∘ swapMain (OuterReserves.main a m)))

/-- Native request to native response, with one recursive parent command
shared by the two child lists and the actual padded-row time charge. -/
theorem internal_bounded_ledger (digit : F → Tree) (W C : ℕ) (hW : 3 ≤ W) (hWb : W < b)
    (hn : 0 < positions a m) (inside : ∀ i, positions a m < (xs i).width)
    (ok : ∀ i, Packed digit (xs i)) (machine : BMain a m xs digit W C) [Finite F] :
    let θ := (↑(C * BatchRows.groups b W) : ℝ)/b + (2*a:ℕ)
    ∃ (small full : I → List (Request b)) (park : I → ℕ) (H : ℕ),
      (∀ i, stepAccount (Packed digit) (positions a m) θ (xs i) (small i ++ full i)) ∧
      (∀ i y, y ∈ small i → 3 * y.rows.count ≤ 2 * (xs i).rows.count) ∧
      (∀ i, park i ≤ H * (Nat.log 2 (xs i).recordVolume + 1)) ∧
      CenterBody (regime xs) (fun i => (xs i).rows.count) (payloadWidth xs) (job b)
        small full park ((job b).issue ∘ xs) ((job b).reply ∘ xs) := by
  intro θ
  have hb : 2 ≤ b := by omega
  let g := BatchRows.groups b W
  let S i := (centerRows a m xs g i).count
  let N i := (centerRows a m xs b i).count
  let valid i (q : Request b) :=
    Packed digit q ∧ q.width = localWidth a m xs i ∧ q.recordWidth = payloadWidth xs i
  let good i := record digit (payloadWidth xs i)
  obtain ⟨v,hv,gv,enter,finish⟩ := expose a m xs hb hn digit ok
  have st := center_told xs hb (fun i => (ok i).1) (positions a m)
  obtain ⟨s,f,sz,sc,fc,fz,body⟩ := OuterReserves.bounded_center a m (north xs b) (aisle a m xs)
    (south a m xs) (localWidth a m xs) (payloadWidth xs) good hb (lane_has xs _) st.1 st.2.1 st.2.2
    v hv gv _ _ (machine v hv gv)
  have same (i : I) : N i = (xs i).rows.count := center_count a m xs i (ok i).2.1
  have smaller (i : I) : 3 * S i ≤ 2 * N i :=
    (Nat.mul_le_mul_right (S i) hW).trans (BatchFrame.row_volume (order a m)
      (fun i => (xs i).before) (aisle a m xs) (south a m xs) (localWidth a m xs)
      (by omega : 0 < W) hWb.le i)
  have small (i : I) : Phase valid S C i (s i) := by
    refine ⟨by exact_mod_cast sc i, fun q hq => ?_⟩
    exact packed_child hb (lanes_pos hn (inside i))
      (packed_dimensions hb W (by omega) hWb (xs i) (positions a m) (ok i).1) digit q (sz i q hq)
  have full (i : I) : Phase valid N (2*a) i (f i) := by
    refine ⟨(fc i).le, fun q hq => ?_⟩
    exact packed_child hb (lanes_pos hn (inside i))
      (admissible_center 1 (localTail a m xs i) hb (ok i).1) digit q (fz i q hq)
  let H := (2*a)*(2*b+9)+1
  refine ⟨s, f, fun i => (InterchangeBatch.headers header (f i)).count, H, ?_, ?_, ?_, ?_⟩
  · intro i
    have h := merge_ledgers (b:=b) (small:=S) (N:=N) (s:=2*a) (c:=C) (g:=g) (by omega)
      (fun j => by have := smaller j; omega)
      (fun j => (BatchFrame.row_volume_exact (order a m) (fun i => (xs i).before)
        (aisle a m xs) (south a m xs) (localWidth a m xs) W j).le)
      i (s i) (f i) (small i) (full i)
    obtain ⟨closed,cost⟩ := h
    exact ⟨fun q hq => ⟨(closed q hq).1.1,(closed q hq).1.2.1,
      (closed q hq).1.2.2,(closed q hq).2.trans (same i).le⟩,by simpa only [same] using cost⟩
  · intro i q hq
    rw [((small i).2 q hq).2, ← same]
    exact smaller i
  · intro i
    let R := Nat.log 2 (xs i).recordVolume + 1
    have h := headers_count_log (f i) (N i) hb fun q hq => ⟨((full i).2 q hq).1.1.1, ((full i).2 q hq).2⟩
    rw [fc] at h
    have logs := Nat.log_mono_right ((same i).le.trans (xs i).rows_le_recordVolume) (b:=2)
    have scale : (2*b+8)*(Nat.log 2 (N i)+1)+1 ≤ (2*b+9)*R := by
      calc
        _ ≤ (2*b+8)*R + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right logs 1)) _
        _ ≤ (2*b+8)*R + R := Nat.add_le_add_left (by dsimp [R]; omega) _
        _ = (2*b+9)*R := by ring
    have total := Nat.add_le_add_right (Nat.mul_le_mul_left (2*a) scale) 1
    calc
      _ ≤ _ := h.trans total
      _ ≤ (2*a)*((2*b+9)*R)+R := Nat.add_le_add_left (by dsimp [R]; omega) _
      _ = H*R := by dsimp only [H]; ring
  · have nEq : countRows (b:=b) (order a m) (north xs b) (aisle a m xs) (south a m xs)
        (localWidth a m xs) = fun i => (xs i).rows.count := funext same
    have outEq : stackRun (centerRows a m xs b) (fun i => v i ∘ swapper _ _ _) =
        (job b).reply ∘ xs := funext finish
    change CenterBody _ (countRows (b:=b) (order a m) _ _ _ _) _ _ _ _ _
      (together _ _) (stackRun (centerRows a m xs b) _) at body
    rw [nEq,outEq] at body
    exact body.preceded enter

end InterchangeAddress.Request

end NearSquareRoot
end Computability
end OAI
