import OAI.Hierarchy.DescentTerminalHeaderGroups

namespace OAI
/-! # A terminal grain contributes exactly one full slot to its port row -/

namespace Hierarchy.DescentTerminalGrainProfiles
open DescentTerminalDenseHeader DescentTerminalHeaderGroups DescentTerminalDenseWindow
open ThreeFlat.Routing Computability.VPVNP.RAMSerialization
open scoped Classical
noncomputable section

/-- The first `used` slots carry a full grain. The remaining slots are padding. -/
def mask (q p used : ℕ) : Profile q p :=
  fun j=>if j.val<used then Fin.last p else 0

def rows (q p n : ℕ) : List (Profile q p) :=
  List.ofFn fun r : Fin (poolBatchCount n q)=>mask q p (min q (n-r.val*q))

@[simp] theorem rows_length (q p n : ℕ) : (rows q p n).length=poolBatchCount n q := by
  simp [rows]

@[simp] theorem rows_zero (q p : ℕ) : rows q p 0=[] := by
  cases q with
  | zero=>simp [rows,poolBatchCount]
  | succ q=>
    have h : poolBatchCount 0 (q+1)=0 := by
      simp only [poolBatchCount,Nat.zero_add,Nat.add_sub_cancel]
      exact Nat.div_eq_of_lt (by omega)
    apply List.length_eq_zero_iff.mp
    simpa using h

theorem chunk_rows {n q p : ℕ} (lengths : Fin n→ℕ) (small : ∀i,lengths i≤p)
    (full : ∀i,lengths i=p) : chunkRows lengths small q=rows q p n := by
  unfold chunkRows rows
  congr 1
  funext r s
  apply Fin.ext
  change lengthAt lengths (r.val*q+s.val)=(mask q p (min q (n-r.val*q)) s).val
  have hs:=s.isLt
  by_cases live:r.val*q+s.val<n
  · have use : s.val< min q (n-r.val*q):=by omega
    simp [lengthAt,mask,live,use,full]
  · have skip : ¬s.val< min q (n-r.val*q):=by omega
    simp [lengthAt,mask,live,skip]

theorem pref_full {n p : ℕ} (lengths : Fin n→ℕ) (full : ∀i,lengths i=p) {a : ℕ} (ha:a≤n) :
    pref lengths a=a*p := by
  induction a with
  | zero=>simp [pref]
  | succ a ih=>
    rw [pref,ih (by omega),Nat.succ_mul]
    simp [lengthAt,show a<n by omega,full]

theorem piece_full {p n : ℕ} (hp:0<p) (divides:p∣n) (k:Fin (poolBatchCount n p)) :
    DescentTerminalDenseGraphRead.pieceSize p n k.val=p := by
  obtain ⟨t,rfl⟩:=divides
  have limit : poolBatchCount (p*t) p≤t :=
    (ceilDiv_le_iff_le_mul hp).2 (by simp)
  have ahead:=Nat.mul_le_mul_right p (show k.val+1≤t by omega)
  rw [Nat.succ_mul] at ahead
  unfold DescentTerminalDenseGraphRead.pieceSize
  have sameProduct : t * p = p * t := Nat.mul_comm t p
  exact Nat.min_eq_left (by omega)

end
end Hierarchy.DescentTerminalGrainProfiles

end OAI
