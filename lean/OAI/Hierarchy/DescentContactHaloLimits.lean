import OAI.Hierarchy.DescentContactSparseSensors
import OAI.Hierarchy.DescentResetSignedHaloPacked

namespace OAI
/-! # All packed raw contact coordinates fit, including empty signed and padded rows -/
namespace Hierarchy.DescentResetSignedHaloMatrix
open DescentSortedRoster DescentResetOriginHaloRAM DescentSIMDLookup DescentPackedChildNeighbor.SIMD
open scoped Classical Fin.CommRing
noncomputable section

theorem rank_tight {S D H N : ℕ} (p : Fin S→Fin D→Option (Fin S)) (home : Fin N→Fin S)
    (h : Fin H) (j : Fin (D+1)) : rank p home h j≤D+1:=by
  unfold rank
  split
  next valid=>
    let v:=home ⟨h.val,valid⟩
    let table:=present (closed p) v
    let key:=((closed p) v j).getD v
    have entered : key∈table:=by
      cases e : closed p v j with
      | none=>simp [key,e,table,present_closed]
      | some x=>
        change _∈Finset.univ.filter _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,by simp [key,e]⟩
    have small : table.card≤D+1:=by
      have sub : table⊆Finset.univ.image (fun i : Fin (D+1)=>(closed p v i).getD v):=by
        intro x hx
        obtain ⟨i,eqn⟩:=(Finset.mem_filter.mp hx).2
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simp [eqn]⟩
      have card := (Finset.card_le_card sub).trans Finset.card_image_le
      simpa using card
    have strict : table.filter (·<key)⊂table:=
      (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨key,entered,by simp⟩
    exact (Finset.card_lt_card strict).trans_le small
  next=>omega

theorem lookup_le {b a n : ℕ} (v : Fin n→Cell b) (q : Cell a) (l : List (Fin n)) (B : ℕ)
    (bound : ∀i,(v i).val≤B) : (lookup v q l).val≤B:=by
  induction l with
  | nil=>simp [DescentPackedChildNeighbor.SIMD.lookup]
  | cons i t ih=>
    unfold DescentPackedChildNeighbor.SIMD.lookup DescentPackedChildNeighbor.SIMD.merge
    split
    · exact ih
    · unfold DescentPackedChildNeighbor.SIMD.field
      split
      · exact bound i
      · simp

theorem raw_range {S D b a : ℕ} (p : Fin S→Fin D→Option (Fin S)) (h : Fin S) (q : Cell a) :
    (lookup (short (b:=b) p id h) q (List.finRange (D+1))).val≤D+1:=
  lookup_le _ _ _ _ (fun j=>(Nat.mod_le _ _).trans (rank_tight p id h j))

theorem same_row {S D : ℕ} (p q : Fin S→Fin D→Option (Fin S)) (h : Fin S) (eqn : ∀j,p h j=q h j)
    (j : Fin (D+1)) : rank p id h j=rank q id h j:=by
  have row : closed p h=closed q h:=by
    funext i
    induction i using Fin.lastCases with
    | last=>simp [closed]
    | cast i=>simpa [closed] using eqn i
  simp only [rank,h.isLt,dite_eq_left,id_eq,before,present,row]

end
end Hierarchy.DescentResetSignedHaloMatrix

namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentContactCoordinateJoint DescentContactProbePitch DescentResetSignedHaloMatrix
open scoped Classical Fin.CommRing
noncomputable section
variable (A : Shape) (start : ℕ) {k : ℕ}
set_option quotPrecheck false
set_option hygiene false
local notation "D" => A.donor
local notation "R" => 2^(Nat.clog 2 ((D).degree+2))
local notation "N" => DescentOldContactSender.count (D).degree (D).lows (D).cap (D).n (D).residual
variable (board : NonlinearExpanders.Graph (D).n k) (xs : Fin (D).hosts→Fin (D).groups→Fin N→Cell (D).fieldBits)
  (next : Fin (D).hosts→Fin (D).degree→Option (Fin (D).hosts))
  (raw : Fin (D).lows→Fin (2*(D).cap)→Fin (D).hosts→Fin (D).groups→Cell (D).fieldBits)
local notation "cells" => A.rawIndicators start board xs next raw

theorem all_fit (keys : DescentResetLocalRoster.rootSlots (D).residual (2^(D).n)*(2^(D).n+2^(D).height)<2^(D).fieldBits)
    (bits : A.shapes*R≤2^A.metaBits) (q : Fin A.sockets) :
    (∀j h g,A.request q*((cells q).indicators.used j h g).val<2^(D).fieldBits) ∧
    ∀s j h g,DescentContactCoordinateJoint.number R (((cells q).indicators.shape s j h g).val) (((cells q).indicators.halo s j h g).val)<2^A.metaBits:=by
  constructor
  · intro j h g
    have sel : A.request q≤DescentResetLocalRoster.rootSlots (D).residual (2^(D).n)*(2^(D).n+2^(D).height):=
      (finProdFinEquiv.symm q).2.isLt
    have small : ((cells q).indicators.used j h g).val≤1:=by
      change (DescentContactMarkerShape.flag A.markerBits (D).fieldBits ((cells q).marker j h g) 0).val≤1
      unfold DescentContactMarkerShape.flag
      split
      · simp
      · exact Nat.mod_le 1 _
    exact (show A.request q*((cells q).indicators.used j h g).val≤A.request q by
      simpa using Nat.mul_le_mul_left (A.request q) small).trans_lt (sel.trans_lt keys)
  · intro s j h g
    have host : 0<A.shapes:=Nat.zero_lt_of_lt (DescentContactProbePitch.shape h).isLt
    have extent:(((cells q).indicators.shape s j h g).val)<A.shapes:=by
      unfold Indicators.shape
      split
      · exact (Nat.mod_le _ _).trans_lt ((Nat.mod_le _ _).trans_lt (DescentContactProbePitch.shape h).isLt)
      · exact (Nat.mod_le _ _).trans_lt (Nat.mod_lt _ host)
    have limited : (((cells q).indicators.halo s j h g).val)≤(D).degree+1:=
      (Nat.mod_le _ _).trans (raw_range next _ _)
    have ltR : (D).degree+1<R:=(Nat.lt_succ_self _).trans_le (Nat.le_pow_clog (by decide) _)
    calc DescentContactCoordinateJoint.number R _ _ < (((cells q).indicators.shape s j h g).val)*R+R:=by
           unfold DescentContactCoordinateJoint.number;rw [Nat.mul_comm R];omega
         _=((((cells q).indicators.shape s j h g).val)+1)*R:=(Nat.succ_mul ..).symm
         _≤A.shapes*R:=Nat.mul_le_mul_right _ extent
         _≤2^A.metaBits:=bits

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
