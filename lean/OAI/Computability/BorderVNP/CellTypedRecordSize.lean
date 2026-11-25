import OAI.Computability.BorderVNP.CellPacketFields
import OAI.Computability.BorderVNP.CellDirectoryTyped
import OAI.Computability.QuantumFactoring.BitStackListOps

/-! # Encoded size of one isolated public wiring record

The variable integer fields cost their binary widths. The number of fields is
the true scalar count in the transport format, including the advertised
histogram values and the routes in the physical order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet

open ExactQuantumFactoring.BitStackProgram

/-- The raw scalar count of a profile header includes two list counts and eight
fields per route. -/
theorem record_profile_length (c : ℕ) (p : Port) (w : ℕ) (hs : List ℕ) (rs : List Route) :
    (record (.profile c p w hs rs)).length = 8 + hs.length + 8*rs.length := by
  have hr : (rs.flatMap route).length = 8*rs.length := by
    induction rs with
    | nil => rfl
    | cons r rs ih => simp [route,port] at ih ⊢; omega
  simp [record,port,vector,fieldList,hr]; omega

private theorem list_length_le {T : Type} (e : T → List Bool) (xs : List T) (L : ℕ)
    (h : ∀ x ∈ xs, (e x).length ≤ L) : (listCode e xs).length ≤ xs.length*(2*L+2)+1 := by
  simpa using listCode_length_map_bound e id xs L h

private theorem port_length_le (p : Port) {U : ℕ} (hp : Profile.PortBound U p) :
    (Typed.port p).length ≤ 5*U.size+2 := by
  obtain ⟨hb,hc,hl⟩ := hp
  have := Nat.size_le_size hb; have := Nat.size_le_size hc; have := Nat.size_le_size hl
  simp only [Typed.port,Typed.portFields,prodCode,pairBits_length,Nat.size_eq_bits_len]
  omega

private theorem route_length_le (r : Route) {U : ℕ}
    (hr : r.term ≤ U ∧ r.lanes ≤ U ∧ Profile.PortBound U r.original ∧ Profile.PortBound U r.compact) :
    (Typed.route r).length ≤ 24*(U.size+1) := by
  have ht := Nat.size_le_size hr.1
  have hl := Nat.size_le_size hr.2.1
  have ho := port_length_le r.original hr.2.2.1
  have hc := port_length_le r.compact hr.2.2.2
  simp only [Typed.route,Typed.routeFields,prodCode,pairBits_length,Nat.size_eq_bits_len]
  omega

/-- One record in the CQF procedure encoding has length linear in its actual
number of transported scalars and the maximum binary field width. -/
theorem typed_record_length (r : Record) {U : ℕ} (hu : RecordFields r U) :
    (Typed.record r).length ≤ 64*(record r).length*(U.size+1) := by
  cases r with
  | zero c l p =>
    obtain ⟨⟨hc,hl,hp⟩,_⟩ := hu
    have := Nat.size_le_size hc; have := Nat.size_le_size hl; have := port_length_le p hp
    simp only [Typed.record,Typed.recordFields,sumCode,List.length_cons,prodCode,pairBits_length,Nat.size_eq_bits_len]
    change _ ≤ 64*6*(U.size+1); omega
  | equal c l p q =>
    obtain ⟨⟨hc,hl,hp,hq⟩,_⟩ := hu
    have := Nat.size_le_size hc; have := Nat.size_le_size hl; have := port_length_le p hp; have := port_length_le q hq
    simp only [Typed.record,Typed.recordFields,sumCode,List.length_cons,prodCode,pairBits_length,Nat.size_eq_bits_len]
    change _ ≤ 64*9*(U.size+1); omega
  | box i b c s =>
    obtain ⟨_,hi,hb,hc,hs⟩ := hu
    have := Nat.size_le_size hi; have := Nat.size_le_size hb; have := Nat.size_le_size hc; have := Nat.size_le_size hs
    simp only [Typed.record,Typed.recordFields,sumCode,List.length_cons,prodCode,pairBits_length,Nat.size_eq_bits_len]
    change _ ≤ 64*5*(U.size+1); omega
  | profile c p w hist rs =>
    obtain ⟨⟨hc,hw,_,_,hp,hr⟩,hh⟩ := hu
    have := Nat.size_le_size hc; have := Nat.size_le_size hw; have := port_length_le p hp
    have hx := list_length_le Nat.bits hist U.size (fun x h => by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (hh x h))
    have hz := list_length_le Typed.route rs (24*(U.size+1)) (fun r h => route_length_le r (hr r h))
    rw [record_profile_length]
    simp only [Typed.record,Typed.recordFields,Typed.naturals,sumCode,List.length_cons,prodCode,pairBits_length,Nat.size_eq_bits_len]
    nlinarith only [hx,hz,Nat.size_le_size hc,Nat.size_le_size hw,port_length_le p hp,
      Nat.zero_le (hist.length*U.size),Nat.zero_le (rs.length*U.size),Nat.zero_le U.size,Nat.zero_le hist.length,Nat.zero_le rs.length]

/-- For a fixed number of fields in each source record, only a logarithmic input
reaches the individual leaf serializer on that record. -/
theorem typed_record_length_of_field_count (D : Directory) (p : ℕ) {U B : ℕ}
    (h : RawFields D p U) (hrows : ∀ r ∈ D.records, (record r).length ≤ B) :
    ∀ r ∈ D.records, (Typed.record r).length ≤ 64*B*(U.size+1) := fun r hr =>
  (typed_record_length r (h.records r hr)).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hrows _ hr)))

end CellSparse.Packet

end BorderVNP
end Computability
end OAI
