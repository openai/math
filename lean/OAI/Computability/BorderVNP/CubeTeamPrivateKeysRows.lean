import OAI.Computability.BorderVNP.CubeTeamPrivateKeysPacket

/-! # Ordered private keys of each actual grouping-symbol view -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Physical

variable {n d blocks b h K s : ℕ} (select : Packet n d blocks → Selector n K h) (i : Fin (n+1))

/-- The local private part of a strict row follows the mixed-radix packet
counter and the native body order within each selected packet. -/
def strictPrivateKeys (b s : ℕ) (pair : Symbols d) (high : Bool) : List (Assignment.BitIndex b s select) :=
  (packetVisits blocks i pair).flatMap fun p => packetPrivateKeys b s select i p high

/-- The endpoint's packet scan contains exactly its own physical private bits. -/
theorem strictPrivateKeys_mem (b s : ℕ) (pair : Symbols d) (high : Bool) (k : Assignment.BitIndex b s select) :
    k ∈ strictPrivateKeys select i b s pair high ↔ privateView i k = some (symbolView pair high) := by
  simp only [strictPrivateKeys,List.mem_flatMap,mem_packetVisits,packetPrivateKeys_mem,privateView_strict]

/-- No two packets in a directed row share a private bit identity. -/
theorem strictPrivateKeys_nodup (b s : ℕ) (pair : Symbols d) (high : Bool) :
    (strictPrivateKeys select i b s pair high).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun p _ => packetPrivateKeys_nodup b s select i p high,(packetVisits_nodup blocks i pair).imp ?_⟩
  intro p q ne
  exact List.disjoint_left.mpr fun k hp hq => ne (congrArg Prod.fst (Option.some.inj
    (((packetPrivateKeys_mem ..).mp hp).symm.trans ((packetPrivateKeys_mem ..).mp hq))))

/-- On the diagonal the private loop emits one guess for each selected
singleton slot. In a strict row only the packet body has private positions. -/
def rowPrivateKeys (b s : ℕ) (v : Fin d × Fin d) : List (Assignment.BitIndex b s select) :=
  if lo : v.1 < v.2 then strictPrivateKeys select i b s ⟨v,lo⟩ false
  else if hi : v.2 < v.1 then strictPrivateKeys select i b s ⟨v.swap,hi⟩ true
  else (singleVisits blocks (h*b) i v.1 v.2).map Sum.inl

/-- A private physical bit appears in precisely its directed row. -/
theorem rowPrivateKeys_mem (b s : ℕ) (v : Fin d × Fin d) (k : Assignment.BitIndex b s select) :
    k ∈ rowPrivateKeys select i b s v ↔ privateView i k = some v := by
  obtain ⟨a,c⟩ := v
  rcases lt_trichotomy a c with lo | rfl | hi
  · exact (show rowPrivateKeys select i b s (a,c) = strictPrivateKeys select i b s ⟨(a,c),lo⟩ false by
      simp [rowPrivateKeys,lo]) ▸ strictPrivateKeys_mem select i b s ⟨(a,c),lo⟩ false k
  · rw [privateView_diagonal]
    simp only [rowPrivateKeys,lt_self_iff_false,dite_false,List.mem_map,mem_singleVisits]
    constructor
    · rintro ⟨z,⟨hs,ht⟩,rfl⟩
      exact ⟨z,rfl,hs,ht⟩
    · rintro ⟨z,rfl,hs,ht⟩
      exact ⟨z,⟨hs,ht⟩,rfl⟩
  · have eq : rowPrivateKeys select i b s (a,c) = strictPrivateKeys select i b s ⟨(c,a),hi⟩ true := by
      simp [rowPrivateKeys,hi,hi.not_gt]
    rw [eq]
    exact strictPrivateKeys_mem select i b s ⟨(c,a),hi⟩ true k

/-- Native trials visit each private position of a directed row at most once. -/
theorem rowPrivateKeys_nodup (b s : ℕ) (v : Fin d × Fin d) : (rowPrivateKeys select i b s v).Nodup := by
  unfold rowPrivateKeys
  split
  · exact strictPrivateKeys_nodup ..
  · split
    · exact strictPrivateKeys_nodup ..
    · exact (singleVisits_nodup ..).map Sum.inl_injective

end Cube.Scatter

end BorderVNP
end Computability
end OAI
