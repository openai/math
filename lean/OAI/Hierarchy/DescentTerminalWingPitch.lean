import OAI.Hierarchy.DescentTerminalBookMeasured

namespace OAI
/-! Rows whose group population fits one word have a unique integer representation at every covering pitch. -/
namespace Hierarchy.DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.Routing
open scoped BigOperators Classical Fin.CommRing
noncomputable section

theorem covered_chunks {n M : ℕ} (positive : 0<n) (covered : n≤M) : chunks n M=1 := by
  unfold chunks poolBatchCount
  apply Nat.div_eq_of_lt_le <;> omega

private theorem low_word {H n a : ℕ} (x : Fin H→Fin n→Cell a) (h : Fin H) (M : ℕ)
    (positive : 0<n) (covered : n≤M) (c : Fin (chunks n M)) :
    (data x (h,c)).val=(encode a n (x h)).val := by
  have c0 : c.val = 0 := Nat.lt_one_iff.mp (c.isLt.trans_le (covered_chunks positive covered).le)
  let term (i : ℕ) := (if hi:i<n then (x h ⟨i,hi⟩).val else 0)*(2^a)^i
  change (∑i:Fin M,(if hi:c.val*M+i.val<n then x h ⟨_,hi⟩ else 0).val*(2^a)^i.val)=
    ∑i:Fin n,(x h i).val*(2^a)^i.val
  simp only [c0,Nat.zero_mul,Nat.zero_add]
  rw [show (∑i:Fin M,(if hi:i.val<n then x h ⟨_,hi⟩ else 0).val*(2^a)^i.val)=∑i:Fin M,term i.val by
    apply Finset.sum_congr rfl
    intro i _
    by_cases sm:i.val<n <;> simp [sm,term]]
  rw [show (∑i:Fin n,(x h i).val*(2^a)^i.val)=∑i:Fin n,term i.val by
    apply Finset.sum_congr rfl
    intro i _
    simp [term,i.isLt]]
  rw [Fin.sum_univ_eq_sum_range term M,Fin.sum_univ_eq_sum_range term n]
  symm
  apply Finset.sum_subset (Finset.range_mono covered)
  intro i _ outside
  simp [term,show ¬i<n by simpa using outside]

/-- No word-copy program is needed: all additional slots carry numerical zero. -/
theorem covered_pitch {w H n a M N : ℕ} (bank : Bank) (x : Fin H→Fin n→Cell a) (m : Memory w)
    (positive : 0<n) (left : n≤M) (right : n≤N) (read : DescentPackedColony.Reads bank x M m) :
    DescentPackedColony.Reads bank x N m := by
  rintro ⟨h,c⟩
  let z:Fin (chunks n M):=⟨0,by rw [covered_chunks positive left];decide⟩
  have addr {P:ℕ} (fits:n≤P) (j:Fin (chunks n P)) : (row H n P (h,j)).val=h.val := by
    have j0 : j.val = 0 := Nat.lt_one_iff.mp (j.isLt.trans_le (covered_chunks positive fits).le)
    change j.val+chunks n P*h.val=h.val
    rw [j0, covered_chunks positive fits, Nat.zero_add, Nat.one_mul]
  have old:=read (h,z)
  rw [addr left z,low_word x h M positive left z] at old
  rw [addr right c,low_word x h N positive right c]
  exact old

end
end Hierarchy.DescentSIMDLookup

end OAI
