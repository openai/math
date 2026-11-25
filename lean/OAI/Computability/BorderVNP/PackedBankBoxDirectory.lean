import OAI.Computability.BorderVNP.PackedBankBoxOrdinal
import OAI.Computability.BorderVNP.PackedBankBoxMerged
import OAI.Computability.BorderVNP.CellPacketSources

/-! # Box ordinals in the transmitted sparse cell packet

The chunk schedule mixes opaque original-site strings with fixed paid-term
factors. The public stable count scan indexes this mixed list. Resolving the
private strings and then traversing the actual directory selects the factors
specified by the corresponding paid tensor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankBoxOrdinal

open CellSparse CellSparse.Packet.Source ParseBatchSort Crossing
open scoped Classical

variable {Site : Type} {s k w : ℕ}
variable (x : Input s k w → Bool) (owner : Fin s → ℕ) (boxes : Fin s → List (Box Site))
variable (ho : ∀ i, ownerWord x i = owner i) (hc : ∀ i, countWord x i = (boxes i).length)
variable (room : ∀ c, (table owner boxes c).length < 2^w)

/-- Physical box entries in the order read by the chunk encoder's directory. -/
def resolved (fs : Site → List Factor) (c : ℕ) : List (List Factor) :=
  (table owner boxes c).map (factors fs)

/-- The complete bit packet assembled from these merged boxes is the encoding
of the directory indexed by the public scan. -/
theorem packet_bits (fs : Site → List Factor) (c : ℕ) (slot : Site → ℕ)
    (header wires : ℕ) (rows : List Record) (reports : List (List ℕ)) (start : ℕ) :
    (chunks slot header fs start (plan wires (table owner boxes c) rows reports)).flatMap
      RoutingISA.CellPacket.Chunk.bits =
      CellSparse.Packet.bits ⟨resolved owner boxes fs c,rows,reports⟩ wires :=
  CellSparse.Packet.Source.packet_bits _ _ _ _ _ _ _ _

include ho hc room in
/-- The stable public ordinal resolves the genuine one-copy factors, including
for an inherited box whose bits arrived in a private site string. -/
theorem resolved_getD (fs : Site → List Factor) (r : Fin s) (j : Fin (boxes r).length) :
    (resolved owner boxes fs (owner r)).getD
      (value (fun b => (frame s k w).eval x (r,b)) + j.val) [] =
      factors fs ((boxes r).get j) := by
  have h := frame_getD x owner boxes ho hc room r j (Sum.inl [] : Box Site)
  exact (List.getD_map (table owner boxes (owner r)) (.inl []) (factors fs)).trans (congrArg (factors fs) h)

variable {D m : ℕ} {K : Type*} [Field K]
variable (e : PaidIdentity K D m) (position : e.Entry → ℕ) (a : Fin e.count) (v : (e.net a).Site)

include ho hc room in
/-- The emitted public box ID and the mixed directory discharge the lookup
in the paid site's actual occurrence traversal. -/
theorem paid_observations (fs : Site → List Factor) (r : Fin s)
    (atSite : boxes r = [.inl [PaidBox.tableFactor e position a v]]) (copies off : ℕ)
    (physical : Fin (Fintype.card (PaidBox.Bundle (e.net a) v)) → ℕ) (bank : ℕ → Bool) :
    let id := value (fun b => (frame s k w).eval x (r,b))
    let merged := resolved owner boxes fs (owner r)
    let dir := PaidBinding.fragment (PaidBox.widths (e.net a) v) copies off id physical merged
    (∀ rec ∈ dir.records, rec.Valid merged bank) →
      dir.observations bank =
        some (List.ofFn fun i => (false,some (position (PaidBinding.entryAt copies e a v physical bank i)))) := by
  intro id merged dir valid
  let j : Fin (boxes r).length := ⟨0,by simp [atSite]⟩
  have hread := resolved_getD x owner boxes ho hc room fs r j
  have hj : (boxes r).get j = .inl [PaidBox.tableFactor e position a v] := by
    change (boxes r)[0]'j.isLt = _
    simp only [atSite,List.getElem_cons_zero]
  have hbox : merged.getD id [] = [PaidBox.tableFactor e position a v] := by
    simpa only [j,Nat.add_zero,hj,factors,Sum.elim_inl,id_eq,merged,id] using hread
  exact PaidBinding.observations copies off id e position a v physical merged bank hbox valid

end Packing.BankBoxOrdinal

end BorderVNP
end Computability
end OAI
