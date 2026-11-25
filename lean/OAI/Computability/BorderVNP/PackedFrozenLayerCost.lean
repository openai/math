import OAI.Computability.BorderVNP.PackedFrozenLayerTape
import OAI.Computability.BorderVNP.PackedFrozenCarryCost
import OAI.Computability.BorderVNP.PackedRoutingCost

/-! # Sparse gate budget of the retained interval tape

The two virtual incidence scans, two shared prefix reads, all interval commands and
the successor-key lookup have linear cost in the sewn rectangle times a cubic polynomial
in the largest word and sorting depth. The shared clip pass is charged separately.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.LayerRows

open Crossing Shortening Shortening.StaticRows Shortening.SeedIntervals CellAddressCircuit CellAddressViews
open PackedHistogram VPVNP.VerifierNetwork
open private sort_poly padded from OAI.Computability.BorderVNP.PackedRoutingCost

variable {s old np C d k w R W : ℕ} {σ : Type*} [Fintype σ] (F : Fields s old np C d k w σ)

private theorem addressBound_cubic (rows : 1+CellAddressCircuit.count s old np C ≤ R)
    (widths : d ≤ W ∧ k ≤ W ∧ w ≤ W ∧ Nat.clog 2 R ≤ W) :
    2+gateBound s old np C d k w+labelBound s old np d k+Fintype.card (View s old np C)*w*(60*k+16) ≤
      3200*R*(W+1)^3 := by
  obtain ⟨hd,hk,hw,hl⟩ := widths
  let unit := R*(W+1)^3
  have ar : 1+((old+C)+(s+C))+(((old+old)+np)+C) ≤ R := by simpa [CellAddressCircuit.count,Nat.add_assoc] using rows
  have hr : 0 < R := by omega
  have hu : 0 < unit := Nat.mul_pos hr (by positivity)
  have logBound (x : ℕ) (hx : x ≤ R) := (Nat.clog_mono_right 2 hx).trans hl
  have label : labelBound s old np d k ≤ 1000*unit := by
    change lookupCost s (old+old+np) d k ≤ _
    apply (lookupCost_cubic _ _ _ _ W (logBound _ (by omega)) hd hk).trans
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 1000 (by omega : s+(old+old+np)+1 ≤ R))).trans_eq (by ring)
  have cap : CellAddressCircuit.count s old np C ≤ R := by omega
  have part := Nat.mul_le_mul (padded cap hr) (sort_poly hk hw (logBound _ cap))
  rw [show 2*R*(500*(W+1)^3) = 1000*unit by dsimp [unit]; ring] at part
  have gate : gateBound s old np C d k w ≤ 2001*unit := by dsimp only [gateBound]; omega
  have per : w*(60*k+16) ≤ 100*(W+1)^3 := by
    calc _ ≤ W*(60*W+16) := by gcongr
         _ ≤ _ := by nlinarith only [Nat.zero_le (W^3),Nat.zero_le (W^2),Nat.zero_le W]
  have tail := Nat.mul_le_mul (show old+old+np+(s+3*C) ≤ R by omega) per
  rw [show R*(100*(W+1)^3) = 100*unit by dsimp [unit]; ring] at tail
  simp only [View,End,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  rw [Nat.mul_assoc (old+old+np+(s+3*C)),Nat.mul_assoc 3200 R]
  omega

private theorem view_cubic (rows : 1+CellAddressCircuit.count s old np s ≤ R) (widths : d ≤ W ∧ w ≤ W ∧ Nat.clog 2 R ≤ W) :
    (Views.frame F).size ≤ 3200*R*(W+1)^3 :=
  (Views.frame_size F).trans (addressBound_cubic rows ⟨widths.1,widths.1,widths.2⟩)

/-- A physical cell allocation scan fits the same cubic word budget as a virtual-site scan. -/
theorem cellView_cubic (rows : 1+CellAddressCircuit.count s old np C ≤ R)
    (widths : d ≤ W ∧ k ≤ W ∧ w ≤ W ∧ Nat.clog 2 R ≤ W) :
    (CellAddressViews.frame F).size ≤ 3200*R*(W+1)^3 := by
  have bound := addressBound_cubic rows widths
  exact (CellAddressViews.frame_size F).trans (by omega)

private theorem prefix_size (col : Fin s → Fin w → σ) :
    (Layer.prefixFrame F col).size ≤ lookupCost s (old+old+np) d w := by
  have h := queries_size (layout (Fin s) (End old np)) (fun i => fixed (σ := σ) (F.sites i))
    (fun i j => .input (col i j)) (fun r j => .input (F.ptr r j))
    1 le_rfl (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  simpa only [Layer.prefixFrame,PackedLookup.lookup,lookupCost,End,Fintype.card_sum,Fintype.card_fin,Nat.mul_one] using h

variable {D m seeds C' d' k' : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
variable (newF : Fields (siteCapacity e s seeds) (edgeCapacity e old seeds) np C' d' k' w σ)
variable (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w)) (work extent : Fin s → Fin w → σ)
local notation3 "V" => siteCapacity e s seeds
local notation3 "E" => edgeCapacity e old seeds
local notation3 "Q" => Fintype.card (Layer.Row old D np)

/-- Each of the sorting and lookup rectangles is bounded by the actual sewn sparse dimensions.
This includes every clipped interval row and every port even when its word width is zero. -/
theorem volume (ports : np ≤ s) :
    1+CellAddressCircuit.count s old np s+CellAddressCircuit.count V E np V+Q ≤ 12*(V+E+1) := by
  have hs : s ≤ V := Nat.le_add_right _ _
  have he : old ≤ E := by
    rw [edgeCapacity_eq]
    exact (Nat.le_mul_of_pos_left _ (by positivity : 0 < 3*(2*D+1))).trans (Nat.le_add_right _ _)
  have band : 2*(2*D+1)*old ≤ E := by
    rw [edgeCapacity_eq]
    nlinarith only [Nat.zero_le ((2*D+1)*old),Nat.zero_le (Fintype.card (TemplateEdge e)*seeds)]
  have q : Q ≤ E+s := by
    simp only [Layer.Row,Band,Fintype.card_sum,Fintype.card_prod,Fintype.card_option,Fintype.card_bool,Fintype.card_fin]
    nlinarith only [band,ports]
  unfold CellAddressCircuit.count
  omega

/-- Complete gate bound for the physical retained commands, including translation to the
successor's actual keys, linear in the sparse sewn site and edge dimensions. -/
theorem budget_cubic (ports : np ≤ s)
    (widths : d ≤ W ∧ d' ≤ W ∧ w ≤ W ∧ Nat.clog 2 (12*(V+E+1)) ≤ W) :
    budget e F newF cut work extent + lookupCost s Q d d' ≤ cut.size + 20000*(12*(V+E+1))*(W+1)^3 := by
  let R := 12*(V+E+1)
  let unit := R*(W+1)^3
  have hr : 0 < R := by unfold R; positivity
  have hu : 0 < unit := Nat.mul_pos hr (by positivity)
  obtain ⟨hd,hd',hw,hl⟩ := widths
  have vol := volume (old := old) (seeds := seeds) e ports
  change 1+CellAddressCircuit.count s old np s+CellAddressCircuit.count V E np V+Q ≤ R at vol
  have vo := view_cubic F (by omega : 1+CellAddressCircuit.count s old np s ≤ R) ⟨hd,hw,hl⟩
  have vn := view_cubic newF (by omega : 1+CellAddressCircuit.count V E np V ≤ R) ⟨hd',hw,hl⟩
  have big : 1+((old+s)+(s+s))+(((old+old)+np)+s)+CellAddressCircuit.count V E np V+Q ≤ R := by
    simpa only [CellAddressCircuit.count,Nat.add_assoc] using vol
  have bound (a z : ℕ) (cap : s+a+1 ≤ R) (fit : z ≤ W) : lookupCost s a d z ≤ 1000*unit := by
    apply (lookupCost_cubic _ _ _ _ W ((Nat.clog_mono_right 2 (by omega : s+a ≤ R)).trans hl) hd fit).trans
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ cap)).trans_eq (by dsimp [unit]; ring)
  have work' := (prefix_size F work).trans (bound _ _ (by omega) hw)
  have extent' := (prefix_size F extent).trans (bound _ _ (by omega) hw)
  have keys := bound Q d' (by omega) hd'
  have cost (a c : ℕ) (cap : a ≤ c*(W+1)^3) : Q*a ≤ c*unit :=
    (Nat.mul_le_mul (by omega : Q ≤ R) cap).trans_eq (by dsimp [unit]; ring)
  have coord : (1+d+6*w)*(30*d+16) ≤ 500*(W+1)^3 := by
    calc _ ≤ (1+W+6*W)*(30*W+16) := by gcongr
         _ ≤ _ := by nlinarith only [Nat.zero_le (W^3),Nat.zero_le (W^2),Nat.zero_le W]
  have words : 4500*(w+1)^2 ≤ 4500*(W+1)^3 := by
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by positivity) (by decide : 2≤3))
  have hc := cost _ _ coord
  have hw' := cost _ _ words
  unfold budget
  rw [Layer.table_size,Nat.mul_assoc Q (1+d+6*w)]
  change _ ≤ cut.size+20000*R*(W+1)^3
  simp only [Nat.mul_assoc 3200 R] at vo vn
  rw [Nat.mul_assoc 20000 R,←show unit = R*(W+1)^3 from rfl]
  omega

end Packing.Inherited.FrozenTape.LayerRows

end BorderVNP
end Computability
end OAI
