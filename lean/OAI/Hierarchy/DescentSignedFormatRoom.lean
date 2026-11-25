import OAI.Hierarchy.DescentSignedStageFormat

namespace OAI
/-! # Address bounds for the packed signed stage -/
namespace Hierarchy.DescentDatedAddressBook.SignedStage
open DescentSIMDLookup DescentHaloWalkRAM Filter
noncomputable section
variable {ι : ℕ → Type*}

private theorem field_pos (q : SignedStage) : 0 < q.fieldBits := by
  apply Nat.clog_pos (by decide : 1 < 2)
  omega

theorem alphabet_dims (q : SignedStage) :
    2^q.k ≤ 2^q.fieldBits ∧ breadth q.oldDegree ≤ 2^q.fieldBits ∧
    q.residentSlots ≤ 2^q.fieldBits ∧ q.newCap ≤ 2^q.fieldBits ∧ q.lowSites ≤ 2^q.fieldBits := by
  have packed:=q.field_room.1
  have seats : q.residentSlots ≤ q.tickets := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have slots : 0 < q.localSlots := Nat.succ_pos _
  have grid : 2^q.k ≤ q.lowSites := by
    change 2^q.k ≤ 2^(q.k+1)*q.localSlots
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ q.k)).trans
      (Nat.le_mul_of_pos_right _ slots)
  dsimp only [rawAlphabet] at packed
  exact ⟨by omega,by omega,by omega,by omega,by omega⟩

/-- Every geometry field is a member of the public alphabet.  The three host and group dimensions
are the only quantities which also use the outside calendar. -/
theorem format_scalar_room (q : ∀h,ι h → SignedStage)
    (old : Bounded (fun h i=>(q h i).oldHosts)) (next : Bounded (fun h i=>(q h i).newHosts))
    (groups : Bounded (fun h i=>(q h i).groups)) (room : ∀h i,2*(q h i).unit ≤ h) :
    SignedExtent.ScalarRoom (fun h i=>(q h i).format h) := by
  let s:=fun h i=>(q h i).format h
  have live (h i) : 0<(s h i).lanes := (occupancy h (q h i).unit (q h i).positive (room h i)).1
  have ex (h i) (a : ℕ) (member : a ∈ (s h i).feedExponents) : a ≤ 1*h := by
    have cap:=(s h i).exponent_room (live h i) a member
    have fit:=lanes_fit h (q h i).unit
    change (s h i).lanes*(q h i).unit ≤ h/2 at fit
    calc a ≤ (s h i).feedUnit*(s h i).lanes := cap
         _ ≤ h/2 := (Nat.mul_le_mul_right (s h i).lanes ((q h i).width h)).trans
           (by simpa only [Nat.mul_comm (q h i).unit] using fit)
         _ ≤ 1*h := by simpa only [Nat.one_mul] using Nat.div_le_self h 2
  have packed (h i) : (s h i).digitArea ≤ 1*h := ex h i _ (by simp [SignedExtent.feedExponents, SignedExtent.digitArea])
  have limit : Bounded (fun h i=>2^(q h i).fieldBits) := by
    apply Bounded.pow_of_linear (K:=1)
    exact Eventually.of_forall fun h i=>(Nat.le_mul_of_pos_right _ (live h i)).trans (packed h i)
  let bound := fun (h : ℕ) (i : ι h) => alphabet_dims (q h i)
  have pieces : Bounded (fun h i=>chunks (q h i).groups (s h i).lanes) := by
    apply (groups.add (Bounded.const 1)).of_le
    intro h i
    let n:=(q h i).groups
    let m:=(s h i).lanes
    have nz : 0 < m := live h i
    change (n+m-1)/m ≤ n+1
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul nz).2
    simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul]
    have full:=Nat.le_mul_of_pos_right n nz
    omega
  exact ⟨limit.of_le (fun h i=>(bound h i).1),old,limit.of_le (fun h i=>(bound h i).2.1),
    limit.of_le (fun h i=>(bound h i).2.2.1),next.mul pieces,limit.of_le (fun h i=>(bound h i).2.2.2.1),
    ⟨1,Eventually.of_forall fun h i=>ex h i _ (by simp [s,SignedExtent.feedExponents])⟩,
    ⟨1,Eventually.of_forall packed⟩,next,old.mul pieces,limit.of_le (fun h i=>(bound h i).2.2.2.2),
    fun h i=>field_pos (q h i),live,⟨1,Eventually.of_forall fun h i=>max_le
      (ex h i _ (by simp [s,SignedExtent.feedExponents])) (ex h i _ (by simp [s,SignedExtent.feedExponents]))⟩,
    ⟨1,Eventually.of_forall fun h i=>ex h i _ (by simp [s,SignedExtent.feedExponents])⟩⟩

end
end Hierarchy.DescentDatedAddressBook.SignedStage

end OAI
