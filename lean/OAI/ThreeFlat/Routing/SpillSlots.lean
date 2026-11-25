import OAI.ThreeFlat.Routing.SpillHalvings

namespace OAI
/-! # Sparse records and the partial compaction relation -/

noncomputable section
open scoped Classical
namespace ThreeFlat.Routing.Spill

/-- Each record has one activity flag at `none` and the payload at `some j`. -/
abbrev SlotBits (S : Type*) (width : ℕ) := S × Option (Fin width)

def occupied {S : Type*} [Fintype S] {w : ℕ} (x : SlotBits S w → Bool) : Finset S :=
  Finset.univ.filter (fun i => x (i,none) = true)

def payloads {S : Type*} [Fintype S] {w : ℕ} (x : SlotBits S w → Bool) : Multiset (Fin w → Bool) :=
  (occupied x).val.map (fun i j => x (i,some j))

def ZeroBlanks {S : Type*} {w : ℕ} (x : SlotBits S w → Bool) :=
  ∀ i, x (i,none) = false → ∀ j, x (i,some j) = false

abbrev RecordPins (n w : ℕ) := SlotBits (Fin n) w

/-- A sparse compactor checks a single partial output, accepts every input
with at most half the final bank occupied, and preserves records including
multiplicities whenever it accepts. -/
structure Compactor (F : Type*) [CommSemiring F] (n r w : ℕ) extends
    Stage F (RecordPins n w) (RecordPins r w) where
  complete : ∀ x, 2*(occupied x).card ≤ r → ∃ y, run x = some y
  preserves : ∀ x y, run x = some y → payloads y = payloads x
  normalized : ∀ x y, run x = some y → ZeroBlanks y

theorem card_payloads {S : Type*} [Fintype S] {w : ℕ} (x : SlotBits S w → Bool) :
    (payloads x).card = (occupied x).card := Multiset.card_map _ _

end ThreeFlat.Routing.Spill

end
end OAI
