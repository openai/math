import OAI.Hierarchy.TaggedShorterNetwork

namespace OAI
/-! # Physical cost of the two-level pool, including idle slots and hole pins -/

noncomputable section
namespace Hierarchy.TaggedShorterCost
open ThreeFlat Routing Spill
open TaggedShorterCompaction TaggedShorterNetwork

def cost (S D M H c T : ℕ) := (5*c*(S*D)+177000*(M*H))*T

theorem arithmetic {S D M h d w c L : ℕ} (rows : 2^h≤D)
    (hS : Nat.log 2 S ≤ L) (hD : Nat.log 2 D ≤ L) :
    S*(Nat.log 2 S+2*(2^h*((d+w)+1))+4)*c +
      2*S*(D*(Nat.log 2 D+(d+w)+4)*c) +
      M*(177000*2^h*(1+h+d+w)) ≤ cost S D M (2^h) c (L+h+d+w+5) := by
  let T := L+h+d+w+5
  have first : Nat.log 2 S+4 ≤ D*T := by
    apply le_trans (b:=T) (by dsimp [T]; omega)
    exact Nat.le_mul_of_pos_left _ ((Nat.two_pow_pos _).trans_le rows)
  have second : 2^h*(d+w+1) ≤ D*T := Nat.mul_le_mul rows (by dsimp [T]; omega)
  have stage : Nat.log 2 S+2*(2^h*(d+w+1))+4 ≤ 3*(D*T) := by omega
  have near : Nat.log 2 D+(d+w)+4 ≤ T := by dsimp [T]; omega
  have moduleCap : 1+h+d+w ≤ T := by dsimp [T]; omega
  calc
    _ ≤ S*(3*(D*T))*c + 2*S*(D*T*c) + M*(177000*2^h*T) := by gcongr
    _ = _ := by unfold cost; ring

/-- The actual two sparse compactors and the full installed oracle banks
satisfy the same cell bill before the external holes are relabelled. -/
theorem exists_boards_raw (F : Type*) [CommSemiring F] :
    ∃ cutoff c : ℕ, ∀ (S D M h d w L : ℕ), 2^h ≤ D → cutoff ≤ 2*2^h →
      0<M → M≤S → cutoff≤2*M → Nat.log 2 S ≤ L → Nat.log 2 D ≤ L →
      ∃ (near : Compactor F D (2^h) (d+w)) (far : Compactor F S M (Width (2^h) (d+w))),
        far.network.cells+2*S*near.network.cells+M*(lane F h d w).cells ≤ cost S D M (2^h) c (L+h+d+w+5) := by
  obtain ⟨cut,c,make⟩ := exists_layouts F
  refine ⟨cut,c,fun S D M h d w L hh scale hm hms large hS hD => ?_⟩
  obtain ⟨near,far,bill⟩ := make S D (2^h) M (d+w) (Nat.two_pow_pos _) hh scale hm hms large
  refine ⟨near,far,?_⟩
  have lanePrice : (lane F h d w).cells ≤ 177000*2^h*(1+h+d+w) := by
    rw [lane_cells]
    exact (Nat.le_add_right _ _).trans (TaggedShorterPair.installedCut_cost F h d w)
  rw [network_cells] at bill
  exact (Nat.add_le_add bill (Nat.mul_le_mul_left M lanePrice)).trans (arithmetic hh hS hD)

/-- The physical board is purchased once per format. Its compacted cell and
hidden-bit bill is linear in total candidate volume and actual module volume,
times the payload width and the logarithm of the board size. -/
theorem exists_boards (F : Type*) [CommSemiring F] :
    ∃ cutoff c : ℕ, ∀ (S D M h d w L : ℕ), 2^h ≤ D → cutoff ≤ 2*2^h →
      0<M → M≤S → cutoff≤2*M → Nat.log 2 S ≤ L → Nat.log 2 D ≤ L →
      ∃ (near : Compactor F D (2^h) (d+w)) (far : Compactor F S M (Width (2^h) (d+w))),
        let N := (TaggedShorterBank.cut near far (lane F h d w)).compactHidden
        N.cells+N.internal ≤ 4*cost S D M (2^h) c (L+h+d+w+5)+1 := by
  obtain ⟨cut,c,make⟩ := exists_boards_raw F
  refine ⟨cut,c,fun S D M h d w L hh scale hm hms large hS hD => ?_⟩
  obtain ⟨near,far,price⟩ := make S D M h d w L hh scale hm hms large hS hD
  exact ⟨near,far,(TaggedShorterBank.cut_size near far (lane F h d w)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 4 price) 1)⟩

/-- Every physical incidence in the single exposed hole is counted,
including the two separate copies at every idle module. -/
theorem pin_count (S D M h d w : ℕ) :
    Fintype.card (TaggedShorterBank.OpenPins S D M (d+w) (Hole h w)) =
      S+2*S*D*(d+w+1) + 2*M*(2^h)*(2*w+h) := by
  have cardBool : Nat.card Bool = 2 := Nat.card_eq_fintype_card.trans Fintype.card_bool
  rw [←Nat.card_eq_fintype_card]
  simp only [TaggedShorterBank.OpenPins,Input,RecordPins,SlotBits,Hole,
    TaggedShorterPair.Hole,Tagged.pins,Nat.card_sum,Nat.card_prod,Nat.card_fin,cardBool,Finite.card_option]
  ring

end Hierarchy.TaggedShorterCost

end
end OAI
