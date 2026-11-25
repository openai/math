import OAI.Hierarchy.DescentGraphVolumes
import OAI.Hierarchy.DescentNativeNeighbors
import OAI.Hierarchy.DescentPackMass
import OAI.Hierarchy.DescentPackingSupport
import OAI.Hierarchy.DescentColonyLayout

namespace OAI
/-! # The actual affine-colored nonhub graph achieves the sparse pairing bound -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentColonies DescentWalshTables
open scoped BigOperators Classical
noncomputable section
theorem filtered_amount {U : Type*} (f : U→ℕ) (keep : U→Bool) (xs : List U) :
    amount f (xs.filter keep)=amount (fun u=>if keep u then f u else 0) xs := by
  induction xs with
  | nil => simp [amount]
  | cons u us ih => cases h : keep u <;> simp [amount,h] at ih ⊢ <;> exact ih

variable {V : Type} [Fintype V] [DecidableEq V] {k d : ℕ} {P : Type*} {bits : P→ℕ}
variable (N : Network d P bits) (core : Finset N.Edge) (position : N.Site→V)
variable (block : N.Site→Block k) (full : N.Site→ℕ) (near : V→Finset V) (D a B unit : ℕ)
variable (small : ∀ (v : V) (x : Block k), blockMass N position block full v x ≤ unit * B)

private abbrev homes := occupiedHome N position block full near D a (unit*B) small
private abbrev colonies := occupied N (unit*B) near D a (blockMass N position block full) small position block
private abbrev trafficAt :
    N.Site → colonies N position block full near D a B unit small → ℕ :=
  nativeTraffic N core (homes N position block full near D a B unit small)
private abbrev bitAddress (u : N.Site) := (DescentColonies.address k).symm (block u)

local notation "localTraffic" => (trafficAt N core position block full near D a B unit small)
local notation "hostMap" => (homes N position block full near D a B unit small)
local notation "Occupied" => (colonies N position block full near D a B unit small)
local notation "blockBits" => (bitAddress N block)

omit [Fintype V] in
theorem actual_slab_cap (hu : 0<unit) (covered : ∀u,unit*live localTraffic u≤full u) (c : Occupied) (i : Bits k) :
    slab (live localTraffic) blockBits (groupStream hostMap c) i≤B := by
  apply Nat.le_of_mul_le_mul_left (c:=unit) _ hu
  let col := occupiedAddress N (unit*B) near D a (blockMass N position block full) small position block
  apply le_trans _ (small (col c).1 (DescentColonies.address k i))
  unfold slab
  rw [filtered_amount]
  let pay (u : N.Site) :=
    if decide (bitAddress N block u = i) = true then
      live localTraffic u else 0
  let host := homes N position block full near D a B unit small
  refine (Eq.le (congrArg (unit * ·) (amount_groupStream pay host c))).trans ?_
  dsimp only [pay,host]
  simp only [blockMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  by_cases h : hostMap u=c
  · have v : position u=(col c).1 := by
      have read := occupiedAddress_colonyOf N (unit*B) near D a (blockMass N position block full) small position block u
      exact congrArg Prod.fst (read.symm.trans (congrArg col h))
    by_cases key : blockBits u=i
    · have ix : block u=DescentColonies.address k i := (Equiv.symm_apply_eq ..).mp key
      simp [h,key,v,ix,covered]
    · simp [h,key]
  · simp [h]

/-- The summed Walsh imbalance of the specified color on the occupied colonies of this graph. -/
def affineBalance (alpha : Bits k) (beta : ZMod 2) : Prop :=
  let A := fun c : Occupied => slab (live localTraffic) blockBits (groupStream hostMap c)
  ∑ c : Occupied, |∑ i, sign (binaryRow alpha i+beta)*(A c i:ℝ)| ≤
    Real.sqrt ((B:ℝ)*Fintype.card Occupied*∑ c, ∑ i,(A c i:ℝ))

omit [Fintype V] in
theorem exists_affineBalance (hu : 0<unit) (covered : ∀u,unit*live localTraffic u≤full u) :
    ∃ (alpha : Bits k) (beta : ZMod 2),
      affineBalance N core position block full near D a B unit small alpha beta := by
  exact DescentPackingColors.exists_coloring _ (B:ℝ) (fun _ _ => Nat.cast_nonneg _)
    (fun c i => by exact_mod_cast actual_slab_cap N core position block full near D a B unit small hu covered c i)

/-! The supplied color acts on the actual ordered streams. -/
omit [Fintype V] in
theorem sparse_pairs_of_bound (Δ : ℕ) (degree : ∀v,(near v).card≤Δ) (hu : 0<unit) (covered : ∀u,unit*live localTraffic u≤full u)
    (adj : ∀e∈core,position (N.dst e)∈near (position (N.src e)))
    (rev : ∀e∈core,position (N.src e)∈near (position (N.dst e)))
    (same : ∀e∈core,block (N.src e)=block (N.dst e)) (alpha : Bits k) (beta : ZMod 2)
    (balanced : affineBalance N core position block full near D a B unit small alpha beta) :
      let color := fun u=>decide (binaryRow alpha (blockBits u)+beta=0)
      let Q := Fintype.card Occupied
      let K := (Δ+1)*(D+1+2*2^D)
      let X : ℝ := core.card
      X/2-Real.sqrt ((B:ℝ)*Q*X)/2-2*B*K*Q ≤
        (Fintype.card (NativePair N core hostMap color B):ℝ) := by
  let col := occupiedAddress N (unit*B) near D a (blockMass N position block full) small position block
  let K := (Δ+1)*(D+1+2*2^D)
  have cap (u : N.Site) : live localTraffic u≤B := by
    apply Nat.le_of_mul_le_mul_left (c:=unit) _ hu
    apply (covered u).trans
    apply le_trans _ (small (position u) (block u))
    have term := Finset.single_le_sum (s:=(Finset.univ : Finset N.Site))
      (f:=fun t => if position t=position u ∧ block t=block u then full t else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
    simpa only [blockMass,eq_self, true_and,ite_true] using term
  have pairs := DescentMatchedCost.paired_support_of_bound (fun _ : Occupied=>localTraffic)
    (groupStream hostMap) (fun _=>blockBits) B
    (fun _ u _=>cap u) (oneNeighbor near D col) K alpha beta
    (fun c v h=>thick_in_allow localTraffic _ blockBits alpha beta _ (fun old member dest positive => by
      have homeEq : hostMap old=c := (mem_groupStream ..).mp member
      rw [←homeEq]
      exact positive_neighbor N (unit*B) near D a (blockMass N position block full) small position block core adj rev same _ _ positive) v h)
    (oneNeighbor_card near D Δ col degree) balanced
  dsimp only at pairs ⊢
  have total : ∑c : Occupied,(amount (live localTraffic) (groupStream hostMap c):ℝ)=(core.card:ℝ) := by
    exact_mod_cast group_wire_amount N core hostMap
  rw [total] at pairs
  unfold NativePair AllPairs
  conv_rhs => rw [Fintype.card_sigma, Nat.cast_sum]
  simp only [K, thinList, thickList, trafficAt, group_side] at pairs ⊢
  refine pairs.trans_eq ?_
  apply Finset.sum_congr (Finset.ext fun c => ⟨fun _ => Finset.mem_univ c, fun _ => Finset.mem_univ c⟩)
  intro c _
  congr! 15

omit [Fintype V] in
/-- The selected affine function acts on actual whole block coordinates.
The total old population appearing in the square root is precisely the
number of physical core bundles of the current graph. -/
theorem sparse_pairs (Δ : ℕ) (degree : ∀v,(near v).card≤Δ) (hu : 0<unit) (covered : ∀u,unit*live localTraffic u≤full u)
    (adj : ∀e∈core,position (N.dst e)∈near (position (N.src e)))
    (rev : ∀e∈core,position (N.src e)∈near (position (N.dst e)))
    (same : ∀e∈core,block (N.src e)=block (N.dst e)) :
    ∃ (alpha : Bits k) (beta : ZMod 2),
      let color := fun u=>decide (binaryRow alpha (blockBits u)+beta=0)
      let Q := Fintype.card Occupied
      let K := (Δ+1)*(D+1+2*2^D)
      let X : ℝ := core.card
      X/2-Real.sqrt ((B:ℝ)*Q*X)/2-2*B*K*Q ≤
        (Fintype.card (NativePair N core hostMap color B):ℝ) := by
  obtain ⟨alpha,beta,h⟩ := exists_affineBalance N core position block full near D a B unit small hu covered
  exact ⟨alpha,beta,sparse_pairs_of_bound N core position block full near D a B unit small Δ degree hu covered
    adj rev same alpha beta h⟩

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
