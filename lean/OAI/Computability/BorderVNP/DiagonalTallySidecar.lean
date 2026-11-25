import OAI.Computability.BorderVNP.DiagonalTallyBitsPack
import OAI.Computability.BorderVNP.CellPacketSiteTail

/-!
# Compact immutable metadata for the unary powers at an original site

The sidecar begins after the reserved one-copy box body. It lists only weighted
positions, in that box's fixed order. The relative report lane is local to the original
box, while the absolute address of each occurrence is assigned by the actual bundle.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TallySidecar

open VPVNP.BurstRAM VPVNP.TapeWord DiagonalResidueRAM

/-- An original weighted position, with no field for a placement-dependent address. -/
structure Position where
  /-- Parameter number in the batch coefficient map. -/
  parameter : ℕ
  /-- Binary place of the corresponding unary power. -/
  place : ℕ
  /-- One-copy lane tied to the external use report by the cell's public equality record. -/
  stagedReportRel : ℕ
  deriving DecidableEq

/-- The three fixed-width metadata words for one original position. -/
def Position.fields (x : Position) : List ℕ := [x.parameter,x.place,x.stagedReportRel]

/-- The initial count is followed by the fixed three-word rows in source order. -/
def fields (ps : List Position) : List ℕ := ps.length :: ps.flatMap Position.fields

/-- Fixed-width least-significant-first words in the delivered string. -/
def words (H : ℕ) (ps : List Position) : List (List Bool) :=
  (fields ps).map fun k => wordBits (word H k)

/-- The literal sidecar that is placed after the common body reservation. -/
def bits (H : ℕ) (ps : List Position) : List Bool := (words H ps).flatten

/-- All fields fit in the declared site-word width. -/
def Fits (H : ℕ) (ps : List Position) : Prop := ∀ k∈fields ps, k<2^H

/-- Each stored metadata word decodes to exactly the original number. -/
theorem words_values (H : ℕ) (ps : List Position) (hf : Fits H ps) :
    (words H ps).map value = fields ps := by
  rw [words,List.map_map]
  apply List.map_congr_left (g := id) (l := fields ps) (by
    intro k hk
    simp [value_wordBits,word_val _ _ (hf k hk)]) |>.trans
  exact List.map_id _

theorem fields_length (ps : List Position) : (fields ps).length=1+3*ps.length := by
  have h : (ps.flatMap Position.fields).length=3*ps.length := by
    induction ps with
    | nil => rfl
    | cons x xs ih => simp [Position.fields,ih,Nat.mul_succ,Nat.add_comm]; omega
  simp [fields,h,Nat.add_comm]

/-- Exact delivery overhead for one site, including its empty-list encoding. -/
theorem bits_length (H : ℕ) (ps : List Position) : (bits H ps).length = H*(1+3*ps.length) := by
  simp [bits,words,List.length_flatten,List.map_map,Function.comp_def,List.map_const',
    fields_length,Nat.mul_comm]

/-- Reserving a common body capacity and a common bound on the number of marked
positions yields a finite fixed delivery width independent of the chosen profile. -/
theorem description_cap (H bodyCap maxMarked : ℕ) (body : List Bool) (ps : List Position)
    (hbody : body.length≤bodyCap) (hmarked : ps.length ≤ maxMarked) :
    H+body.length+(bits H ps).length ≤ H+bodyCap+H*(1+3*maxMarked) := by
  rw [bits_length]
  exact Nat.add_le_add (Nat.add_le_add_left hbody H) (Nat.mul_le_mul_left H (by omega))

private theorem bitsAt_of_values {w : ℕ} (m : Memory w) (p : ℕ) (xs : List Bool)
    (h : ∀ j, (hj : j<xs.length) → (m (p+j)).val=xs[j].toNat) : DiagonalTallyBits.BitsAt m p xs := by
  induction xs generalizing p with
  | nil => trivial
  | cons x xs ih =>
    refine ⟨?_,ih (p+1) ?_⟩
    · have hh := h 0 (by simp)
      rw [Nat.add_zero] at hh
      exact hh
    intro j hj
    have a := h j.succ (by simpa using hj)
    rw [List.getElem_cons_succ] at a
    simpa only [Nat.add_assoc,Nat.add_comm 1 j] using a

/-- Reading a flat bit string as an ordered list of fields loses neither addresses nor bits. -/
theorem wordsAt_of_flat {w : ℕ} (m : Memory w) (p : ℕ) (xs : List (List Bool))
    (h : ∀ j, (hj : j<xs.flatten.length) → (m (p+j)).val=xs.flatten[j].toNat) :
    DiagonalTallyBits.WordsAt m p xs := by
  induction xs generalizing p with
  | nil => trivial
  | cons b bs ih =>
    simp only [List.flatten_cons,List.length_append] at h
    refine ⟨bitsAt_of_values m p b ?_,ih (p+b.length) ?_⟩
    · intro j hj
      have hh := h j (by omega)
      simpa [List.getElem_append_left hj] using hh
    · intro j hj
      have hh := h (b.length+j) (by omega)
      simpa [List.getElem_append_right (by omega : b.length ≤ b.length+j),Nat.add_assoc] using hh

/-- The genuine delivered site string supplies exactly these field words at its
profile-independent offset, while retaining the opaque box's original bytes. -/
theorem delivered_words {description w : ℕ} (m : Memory w) (slot H capacity : ℕ)
    (fs : List CellSparse.Factor) (ps : List Position)
    (hbox : (CellSparse.Packet.Source.boxBody fs).length≤capacity)
    (hsize : H+capacity+(bits H ps).length≤description)
    (received : ∀ j : Fin description, (m (slot+j.val)).val=
      (CellSparse.Packet.Source.siteWithTally H capacity fs (bits H ps) j).toNat) :
    DiagonalTallyBits.WordsAt m (slot+H+capacity) (words H ps) := by
  have tail := (CellSparse.Packet.Source.siteWithTally_read (fun a => (m a).val) slot H capacity fs
    (bits H ps) hbox hsize received).2
  apply wordsAt_of_flat
  intro j hj
  simpa only [bits,Nat.add_assoc] using tail ⟨j,hj⟩

end TallySidecar

end BorderVNP
end Computability
end OAI
