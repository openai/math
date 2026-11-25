import OAI.Hierarchy.DescentOrdinaryParallelSide
import OAI.Hierarchy.DescentIssuedDonorChart

namespace OAI
/-! The short trimmed heap names fit the actual full-host pitch, including the last leaf. -/
namespace Hierarchy.DescentHostDirectory.SiteDecode
open DescentColonies
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V] {k g slots : ℕ}

omit [DecidableEq V] in
theorem local_number_pitch {q : Key V} (legal : q∈keys k slots) :
    localNumber k slots q<(2^(k+1)-1)*slots :=by
  obtain ⟨_,items⟩:=Finset.mem_product.mp legal
  obtain ⟨tree,slot⟩:=Finset.mem_product.mp items
  obtain ⟨depth,hi⟩:=codes_valid tree
  have end₀:=Finset.mem_range.mp slot
  have cut:=Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide : 0<2) (Nat.add_le_add_right depth 1)) 1
  have head:nodeNumber q.2.1.1 q.2.1.2<2^(k+1)-1:=(node_range hi).2.trans_le cut
  change (0*2^(k+1)+nodeNumber q.2.1.1 q.2.1.2)*slots+q.2.2<_
  rw [Nat.zero_mul,Nat.zero_add]
  calc
    _<nodeNumber q.2.1.1 q.2.1.2*slots+slots := Nat.add_lt_add_left end₀ _
    _=(nodeNumber q.2.1.1 q.2.1.2+1)*slots := by ring
    _≤_ := Nat.mul_le_mul_right slots head

omit [DecidableEq V] in
theorem trimmed_pitch (hub : V→Bool) {q : Key V} (legal : q∈keys k slots) :
    trim k g slots (hub q.1) (localNumber k slots q)<(2^(k+1)-1)*slots :=by
  rw [trim_key k g slots hub q legal]
  exact local_number_pitch (merged_mem_keys hub k g slots legal)

omit [DecidableEq V] in
/-- Dense physical names and the previous padded CPU names compare identically on genuine keys. -/
theorem pitch_comparison {u v : Key V} (hu : u∈keys k slots) (hv : v∈keys k slots) (i j : ℕ) :
    (i*((2^(k+1)-1)*slots)+localNumber k slots u < j*((2^(k+1)-1)*slots)+localNumber k slots v)
      ↔ i*(2^(k+1)*slots)+localNumber k slots u<j*(2^(k+1)*slots)+localNumber k slots v :=by
  have span : (2^(k+1)-1)*slots≤2^(k+1)*slots:=Nat.mul_le_mul_right _ (Nat.sub_le ..)
  have a:=local_number_pitch hu
  have b:=local_number_pitch hv
  rw [DescentOrdinaryDonorHalo.lex a b,DescentOrdinaryDonorHalo.lex (a.trans_le span) (b.trans_le span)]

end Hierarchy.DescentHostDirectory.SiteDecode

end OAI
