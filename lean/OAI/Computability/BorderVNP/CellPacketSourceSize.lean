import OAI.Computability.BorderVNP.CellPacketSources

/-! # Word, bit and instruction budgets for a mixed public and private packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Source

open VPVNP.BurstRAM RoutingISA RoutingISA.CellPacket

/-- Each scheduled part emits one chunk descriptor, regardless of its source length. -/
theorem chunks_length {Site : Type} (slot : Site → ℕ) (H : ℕ) (fs : Site → List Factor)
    (parts : List (Part Site)) (base : ℕ) :
    (chunks slot H fs base parts).length = parts.length := by
  induction parts generalizing base with
  | nil => rfl
  | cons p ps ih => cases p <;> simp [chunks, ih]

/-- Public words are charged at their physical width. Every private body is charged
once to the width of the padded site description. -/
theorem chunks_bits_length_le {Site : Type} {w : ℕ} (m : Memory w) (slot : Site → ℕ)
    (H description : ℕ) (fs : Site → List Factor) (parts : List (Part Site)) (base : ℕ)
    (room : ∀ j, H + (boxBody (fs j)).length ≤ description)
    (pub : WordsAt (readings m) base (parts.flatMap Part.publicBuffer)) :
    ((chunks slot H fs base parts).flatMap Chunk.bits).length ≤
      (2*w+2)*(parts.flatMap Part.publicBuffer).length + description*(privateKeys parts).length := by
  induction parts generalizing base with
  | nil => simp [chunks, privateKeys]
  | cons p ps ih =>
    cases p with
    | publicWords xs =>
      change WordsAt (readings m) base (xs ++ ps.flatMap Part.publicBuffer) at pub
      have bounded (x : ℕ) (hx : x ∈ xs) : x < 2^w := by
        obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hx
        have h := pub.left ⟨i,hi⟩
        exact h.symm.trans_lt (m (base+i)).isLt
      have head := CellPacketEncode.packet_length_le xs bounded
      have tail := ih _ pub.right
      change (CellPacketEncode.packet xs ++
        (chunks slot H fs (base+xs.length) ps).flatMap Chunk.bits).length ≤
        (2*w+2)*(xs ++ ps.flatMap Part.publicBuffer).length + description*(privateKeys ps).length
      rw [List.length_append,List.length_append,Nat.mul_add,Nat.add_assoc]
      exact Nat.add_le_add (by simpa only [Nat.mul_comm] using head) tail
    | original j =>
      have tail := ih base pub
      change (boxBody (fs j) ++ (chunks slot H fs base ps).flatMap Chunk.bits).length ≤
        (2*w+2)*(ps.flatMap Part.publicBuffer).length + description*((privateKeys ps).length+1)
      rw [List.length_append,Nat.mul_add,Nat.mul_one]
      have head := room j
      omega

/-- Total reader work from the public word mass, the number of chunks and the
number of separately delivered private descriptions. -/
theorem chunks_work_total_le {Site : Type} (slot : Site → ℕ) (H description w : ℕ)
    (fs : Site → List Factor) (parts : List (Part Site)) (base : ℕ)
    (room : ∀ j, H + (boxBody (fs j)).length ≤ description) :
    ((chunks slot H fs base parts).map (Chunk.work w)).sum ≤
      60*((w+1)*((parts.flatMap Part.publicBuffer).length+parts.length) +
        (description+1)*(privateKeys parts).length) := by
  apply (chunks_work_le slot H description w fs parts base room).trans
  induction parts with
  | nil => simp [privateKeys]
  | cons p ps ih =>
    cases p with
    | publicWords xs =>
      simp only [List.map_cons,List.sum_cons,List.flatMap_cons,Part.publicBuffer,List.length_append,
        List.length_cons]
      change 60*(xs.length+1)*(w+1) + _ ≤
        60*((w+1)*(xs.length + (ps.flatMap Part.publicBuffer).length+(ps.length+1)) +
          (description+1)*(privateKeys ps).length)
      nlinarith only [ih]
    | original j =>
      simp only [List.map_cons,List.sum_cons,List.flatMap_cons,Part.publicBuffer,List.nil_append,
        List.length_cons]
      change 60*(description+1) + _ ≤
        60*((w+1)*((ps.flatMap Part.publicBuffer).length+(ps.length+1)) +
          (description+1)*((privateKeys ps).length+1))
      nlinarith only [ih,Nat.zero_le w]

end CellSparse.Packet.Source

end BorderVNP
end Computability
end OAI
