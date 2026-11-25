import OAI.Hierarchy.DescentSparseNeighborPorts

namespace OAI
/-! # Inverse lookup of an authentic live edge in its source's sorted aperture -/

noncomputable section
namespace Hierarchy.DescentPacking.SparseBinRAM
open Sparse ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {C : Type*} [Fintype C] [DecidableEq C] {S : Finset C} {n w : ℕ}

namespace Aperture

def atRank (A : Aperture S n) (i : Fin n) := A.key ((order A.key).symm i)

theorem rank_key (A : Aperture S n) (j : Fin (roster S).length) (i : Fin n) :
    A.atRank i=code ((roster S).get j) ↔ i.val=j.val := by
  by_cases fits : i.val < (roster S).length
  · let a : Fin (roster S).length := ⟨i.val,fits⟩
    have eqn : order A.key (A.entry a)=i := Fin.ext (A.entry_rank a)
    have hit : A.atRank i=code ((roster S).get a) := by
      change A.key ((order A.key).symm i)=_
      rw [←eqn,Equiv.symm_apply_apply,A.entry_key]
    rw [hit]
    exact ⟨fun e=>congrArg Fin.val ((roster_strict S).injective e),
      fun e=>congrArg (fun u=>(code ((roster S).get u))) (Fin.ext e : a=j)⟩
  · have none := A.padding_key i (Nat.le_of_not_gt fits)
    exact iff_of_false (fun e=>(code_lt _).ne' (none.symm.trans e)) (fun e=>fits (e ▸ j.isLt))

def atNat (A : Aperture S n) (i : ℕ) := if h : i<n then A.atRank ⟨i,h⟩ else Fintype.card C

theorem lookup_hit (A : Aperture S n) (j : Fin (roster S).length) (tags : Bank) (base target : Expr)
    (m : Memory w) (r : Word w) (off : ℕ) (orig : base.eval m r=(off:Word w))
    (wanted : (target.eval m r).val=code ((roster S).get j)) (cap : off+n≤tags.size) (word : tags.size<2^w)
    (fields : ∀i : Fin n,(m (tags.base+off+i.val)).val=A.atRank i) :
    (localTarget n tags base target).eval m r=(j.val:Word w) := by
  rw [localTarget_eval n tags base target m r off _ A.atNat orig wanted cap word
    (fun i hi=>by simpa [atNat,hi] using fields ⟨i,hi⟩)]
  have jq := j.isLt.trans_le A.capacity
  let pred := fun k=>decide (A.atNat k=code ((roster S).get j))
  have property (k : ℕ) (hk : k<n) : pred k=true ↔ k=j.val := by
    simpa only [pred,atNat,dite_eq_left hk,decide_eq_true_eq] using A.rank_key j ⟨k,hk⟩
  have found : (List.range n).find? pred=some j.val := by
    cases e : (List.range n).find? pred with
    | none => exact False.elim (List.find?_eq_none.mp e j.val (List.mem_range.mpr jq) ((property _ jq).mpr rfl))
    | some k =>
      have bound := List.mem_range.mp (List.mem_of_find?_eq_some e)
      exact congrArg some ((property k bound).mp (List.find?_some e))
  change (((List.range n).find? pred).getD n:Word w)=_
  rw [found]
  rfl

end Aperture

namespace Rect
open DescentSixParty.StarKeys Computability.BorderVNP.Crossing DescentColonies DescentHostDirectory
variable {H k Dims d : ℕ} {P : Type*} {bits : P→ℕ}
    (N : Network Dims P bits) (B : ℕ) (near : Fin H→Finset (Fin H)) (D a : ℕ)
    (loads : Fin H→Block k→ℕ) (small : ∀v i,loads v i≤B)
    (position : N.Site→Fin H) (block : N.Site→Block k)

local notation "Col" => occupied N B near D a loads small position block
local notation "home" => colonyOf N B near D a loads small position block
local notation "col" => occupiedAddress N B near D a loads small position block

/-- The real depth and interval address fit the fixed rectangular port table. -/
theorem ranges (c : Col) : (col c).2.1≤k ∧ (col c).2.2<2^(col c).2.1 := by
  obtain ⟨u,rfl⟩ := colonyOf_surjective N B near D a loads small position block c
  rw [occupiedAddress_colonyOf]
  let depth := depthAt B near D a loads small (position u) (block u)
  have h : depth≤k := (depth_le ..).trans (Nat.sub_le ..)
  exact ⟨h,group_lt h _⟩

def realCell : Col↪Fin H×Fin (2^(k+1)) :=
  dyadicCell col k (fun c=>(ranges N B near D a loads small position block c).1)
    (fun c=>(ranges N B near D a loads small position block c).2)

theorem thick_kept (core : Finset N.Edge) (color : N.Site→Bool)
    (adj : ∀e∈core,position (N.dst e)∈near (position (N.src e)))
    (rev : ∀e∈core,position (N.src e)∈near (position (N.dst e)))
    (same : ∀e∈core,block (N.src e)=block (N.dst e))
    (next : DescentPackedExchange.Port H d→Option (Fin H))
    (complete : ∀v u,u∈near v→∃j,next (v,j)=some u) (c v : Col)
    (positive : 0<Fintype.card (ThickPool (nativeTraffic N core home) (thickList home color c) v)) :
    v∈keep (nearby (realCell N B near D a loads small position block) (ports (col c).1 next)) :=
  neighbor_mem (oneNeighbor_mem near D col _ (fun _=>rfl) next complete
    (thick_support N B near D a loads small position block core color adj rev same c v positive))

theorem live_target_kept (core : Finset N.Edge)
    (adj : ∀e∈core,position (N.dst e)∈near (position (N.src e)))
    (rev : ∀e∈core,position (N.src e)∈near (position (N.dst e)))
    (same : ∀e∈core,block (N.src e)=block (N.dst e))
    (next : DescentPackedExchange.Port H d→Option (Fin H))
    (complete : ∀v u,u∈near v→∃j,next (v,j)=some u) (u : N.Site) (v : Col)
    (positive : 0<nativeTraffic N core home u v) :
    v∈keep (nearby (realCell N B near D a loads small position block) (ports (col (home u)).1 next)) :=
  neighbor_mem (oneNeighbor_mem near D col _ (fun _=>rfl) next complete
    (positive_neighbor N B near D a loads small position block core adj rev same u v positive))

end Rect
end Hierarchy.DescentPacking.SparseBinRAM

end
end OAI
