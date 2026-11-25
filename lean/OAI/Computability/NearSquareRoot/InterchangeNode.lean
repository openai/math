import OAI.Computability.NearSquareRoot.InterchangeMixed
import OAI.Computability.NearSquareRoot.InterchangePackedRequest
import OAI.Computability.NearSquareRoot.InterchangeOuterReserves

/-! # A recursive node with both padded bank calls and full-volume reserve calls -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress.Request

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic IntegerMultiplication.Loom NearSquareRoot.InterchangeFrame
  NearSquareRoot.InterchangeSpectralFibre

variable {I F : Type} {b : ℕ} [NeZero b] (a m : ℕ) (xs : I → Request b)

abbrev positions := a + m + a
abbrev localWidth (i : I) := lanes (positions a m) (xs i).width
abbrev localTail (i : I) := tail (positions a m) (xs i).width
abbrev north (g : ℕ) (i : I) := (xs i).before ++ [g]
abbrev aisle (i : I) := gap b 1 (localTail a m xs i) (xs i).between
abbrev south (i : I) := post b (localTail a m xs i) (xs i).after_
abbrev order := Equiv.refl (Fin (positions a m))
abbrev centerRows (g : ℕ) := layoutRows (b:=b) (order a m) (north xs g) (aisle a m xs)
  (south a m xs) (localWidth a m xs)
abbrev payloadWidth (i : I) := (xs i).recordWidth

omit [NeZero b] in
theorem center_count (i : I) (hw : 0 < (xs i).width) :
    (centerRows a m xs b i).count = (xs i).rows.count := by
  let t := localTail a m xs i
  let f := localWidth a m xs i
  let p := (xs i).before
  let g := (xs i).between
  let s := (xs i).after_
  have h := ((axis (order a m) b 1 f t p g s).view.cost).symm.trans
    ((parent (order a m) b 1 f t p g s).cost)
  change _ = (stock b p g s (xs i).width).count
  rw [width_eq hw (positions a m)]
  exact h

abbrev subZone (digit : F → Tree) (W : ℕ) (i : I) (y : Request b) :=
  ((allowed (localWidth a m xs) (fun i => (centerRows a m xs (BatchRows.groups b W) i).count)
    (payloadWidth xs) i y) ∧ ∀ k, record digit ((xs i).recordWidth) (y.contents k)) ∧
    inherited b (north xs (BatchRows.groups b W) i) (aisle a m xs i) (south a m xs i) y

/-- A configured pencil and spectral repair acting on the padded bank has
only the main single-stream calls in its docket. The outer reserve pairs
are run afterward on the merged stream. -/
abbrev Main (digit : F → Tree) (W C : ℕ) :=
  ∀ (v : (i : I) → domain (b:=b) (J:=Fin (positions a m)) (north xs b) (aisle a m xs)
    (south a m xs) (localWidth a m xs) i → Tree),
    Manifest _ (payloadWidth xs) v → (∀ i k, record digit ((xs i).recordWidth) (v i k)) →
    Hopto (job b) (regime xs) (fun i => (centerRows a m xs b i).count) (payloadWidth xs)
      (subZone a m xs digit W) C
      (together (regime xs).header (stackRun (centerRows a m xs b) v))
      (stackRun (centerRows a m xs b) (fun i => v i ∘ swapMain (OuterReserves.main a m)))

theorem internal_ledger (digit : F → Tree) (W C : ℕ) (hW : 0 < W) (hWb : W < b)
    (hn : 0 < positions a m) (inside : ∀ i, positions a m < (xs i).width)
    (ok : ∀ i, Packed digit (xs i)) (machine : Main a m xs digit W C) [Finite F] :
    let θ := (↑(C * BatchRows.groups b W) : ℝ)/b + (2*a:ℕ)
    ∃ uses : I → List (Request b), (∀ i,
      (∀ y ∈ uses i, Packed digit y ∧ y.width = localWidth a m xs i ∧
         y.recordWidth = payloadWidth xs i ∧ y.rows.count ≤ (xs i).rows.count) ∧
      ((uses i).map fun y => (y.rows.count : ℝ)).sum ≤ θ * (xs i).rows.count) ∧
      Quest (job b) (regime xs) (fun i => (xs i).rows.count) (payloadWidth xs)
        uses ((job b).issue ∘ xs) ((job b).reply ∘ xs) := by
  intro θ
  have hb : 2 ≤ b := by omega
  let N i := (centerRows a m xs b i).count
  let g := BatchRows.groups b W
  let S i := (centerRows a m xs g i).count
  let valid i (y : Request b) := Packed digit y ∧ y.width = localWidth a m xs i ∧ y.recordWidth = payloadWidth xs i
  let good i := record digit (payloadWidth xs i)
  have wf i := lanes_pos hn (inside i)
  have st := center_told xs hb (fun i => (ok i).1) (positions a m)
  have geo := layoutRows_station (b:=b) (order a m) (north xs b) (aisle a m xs) (south a m xs)
    (localWidth a m xs) hb (lane_has xs _) st.1 st.2.1 st.2.2
  have small : Program (job b) (regime xs) (payloadWidth xs) (Phase valid S C) good
      (centerRows a m xs b) (fun _ => swapMain (OuterReserves.main a m)) :=
    monitored _ _ _ _ _ (fun i y h => packed_child hb (wf i)
      (packed_dimensions hb W hW hWb (xs i) (positions a m) (ok i).1) digit y h) machine
  have reserve : Program (job b) (regime xs) (payloadWidth xs) (Phase valid N (2*a)) good
      (centerRows a m xs b) (fun _ => OuterReserves.swapOuter) :=
    monitored _ _ _ _ _ (fun i y h => packed_child hb (wf i)
      (admissible_center 1 (localTail a m xs i) hb (ok i).1) digit y h)
      (OuterReserves.full_volume_calls a m _ _ _ _ _ good hb (lane_has xs _) st.1 st.2.1 st.2.2)
  have ratio i : b * S i = g * N i := BatchFrame.row_volume_exact (order a m)
    (fun i => (xs i).before) (aisle a m xs) (south a m xs) (localWidth a m xs) W i
  have small_le i : S i ≤ N i := by
    have e := (ratio i).le.trans (Nat.mul_le_mul_right _ (BatchFrame.groups_bounds hW hWb).2)
    exact Nat.le_of_mul_le_mul_left e (by omega)
  have full := small.chain geo reserve (account:=Mixed valid N θ)
    (fun i x y => merge_ledgers (b:=b) (by omega) small_le (fun i => (ratio i).le) i x y)
  have correct : (fun i => (fun k => swapMain (OuterReserves.main a m) (OuterReserves.swapOuter k) :
        _ → Keys (north xs b i) (aisle a m xs i) (south a m xs i) _ (Block b (localWidth a m xs i)))) =
      fun i => swapper (north xs b i) (aisle a m xs i) (south a m xs i) := by
    funext i k
    exact (OuterReserves.complete k).1
  change Program _ _ _ _ _ _ _ at full
  simp only [Function.comp_def,correct] at full
  obtain ⟨uses, legal, work⟩ := framed_step hb hn (order a m) xs (fun i => (ok i).1) inside
    (job b) good (Mixed valid N θ) (fun i => (ok i).2.2) (packed_manifest digit xs ok) full
  refine ⟨uses, ?_,work⟩
  intro i
  have e := center_count a m xs i (ok i).2.1
  obtain ⟨hy,cost⟩ := legal i
  refine ⟨fun y h => ?_,?_⟩
  · obtain ⟨⟨hs,hw,hl⟩,hc⟩ := hy y h
    exact ⟨hs,hw,hl,hc.trans e.le⟩
  · simpa only [N,e] using cost

end InterchangeAddress.Request

end NearSquareRoot
end Computability
end OAI
