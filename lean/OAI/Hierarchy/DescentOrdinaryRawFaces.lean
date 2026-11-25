import OAI.Hierarchy.DescentParentFilterFused
import OAI.Hierarchy.DescentOrdinarySignedRanks
import OAI.Hierarchy.DescentOrdinaryRawTests

namespace OAI
/-! # Both endpoint tests and the multiplicity of the actual eleven-word old donor -/
namespace Hierarchy.DescentOrdinarySignedMeta
open DescentParallelBase DescentParallelBase.ParentFilter DescentHaloWalkRAM DescentSharedCableNames
open DescentSIMDLookup DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {D N K L Q a b : ℕ} {R : Fin N→Fin D→Option (Fin N)}
local notation "P" => breadth D

theorem active_filtered (r : Option (Fused.Raw R Q K L a)) :
    activeRaw (Fused.columns r)=(Fused.filtered r).isSome := by
  cases r with
  | none => simp [activeRaw,Fused.columns,Fused.filtered]
  | some v =>
    simp only [activeRaw,tests,Fused.columns,Option.elim_some,Machine.fields,Fused.filtered,Option.bind_some]
    change (decide (0<v.parent.weight.val) &&
      (decide ((localRank R v.host v.parent.src.path).val=Rebase.value R .rank v.receiver.1 v.path ∧ v.parent.src.low.val=v.receiver.2.val) ||
       decide ((localRank R v.host v.parent.dst.path).val=Rebase.value R .rank v.receiver.1 v.path ∧ v.parent.dst.low.val=v.receiver.2.val))) = _
    simp only [Fin.val_inj]
    unfold ParentFilter.filter
    by_cases empty : v.parent.weight.val=0 <;>
      by_cases src : (localRank R v.host v.parent.src.path).val=Rebase.value R .rank v.receiver.1 v.path ∧
        v.parent.src.low=v.receiver.2 <;>
      by_cases dst : (localRank R v.host v.parent.dst.path).val=Rebase.value R .rank v.receiver.1 v.path ∧
        v.parent.dst.low=v.receiver.2 <;> simp [empty,src,dst,Nat.pos_iff_ne_zero]

theorem tests_witness (r : Fused.Raw R Q K L a) (s t : Fin N×Fin Q)
    (symmetric : ∀v u i,R v i=some u→∃j,R u j=some v) (readR : Gather.reaching R r.receiver.1 r.path=some r.host)
    (real : Witness R r.host r.parent s t) :
    tests (Fused.columns (some r))=(decide (r.receiver=s),decide (r.receiver=t)) := by
  have sr:=ParentFilter.unique R symmetric r.host r.receiver.1 s.1 r.path r.parent.src.path readR real.src
  have tr:=ParentFilter.unique R symmetric r.host r.receiver.1 t.1 r.path r.parent.dst.path readR real.dst
  simp [tests,Fused.columns,Machine.fields,sr,tr,real.srcLow,real.dstLow,Prod.ext_iff,Fin.ext_iff,eq_comm]

variable {U E X T V : Type} [Fintype E] [DecidableEq U] [Fintype X] [Fintype T]
  {n O : ℕ} {B : Ends U n} (C : Blocks B E) (R : Fin N→Fin D→Option (Fin N))
  (symm : ∀v u i,R v i=some u→∃j,R u j=some v)
  (Z : Measured C R X T V Q O K L) (shelf : Measured.Shelf C R Z)
  (small : ∀h path x (s : ParentFilter.Source (breadth D) Q K L) i,Machine.fields R (Z.venue h) path (Z.loc x).1 s i<2^a)
local notation "res" => Measured.roster C R symm Z
local notation "fetched" => Fused.fetched C R Z shelf small

theorem fetched_at (h : U) (e : Local C h) :
    fetched h ((res).address h e) =
      some ⟨Z.venue h,Measured.visit C R symm Z h e,(Z.loc (Z.raw h e)).1,Z.read h e,
        small h _ _ _⟩ := by
  have read : Gather.select (Gather.reaching R) (Z.venue h).1 (Measured.visit C R symm Z h e) = some (Z.loc (Z.raw h e)).1 :=
    Resident.visit_read C h (fun u=>(Z.venue u).1) Z.loc (Z.raw h) (Gather.reaching R) (Measured.near C R symm Z h) e
  change fetched h (finProdFinEquiv (Measured.visit C R symm Z h e, (Z.loc (Z.raw h e)).2)) = _
  simp only [Fused.fetched,Resident.collected,Equiv.symm_apply_apply,read,
    Option.bind_some,Resident.old_at,Fused.previous,shelf.covers,Option.map_some]

include shelf in
omit [Fintype E] in
private theorem resident_ends (h : U) (e : Local C h) :
    (Z.venue h=Z.venue (C.src e.val) ↔ C.src e.val=h) ∧
    (Z.venue h=Z.venue (C.dst e.val) ↔ C.dst e.val=h) := by
  have positive : 0<(Z.read h e).weight.val:=by rw [Z.survives]; exact e.property.1
  obtain ⟨u,up,actual,injectS,injectT,back⟩:=shelf.proper h (Z.raw h e) (Z.read h e) (shelf.covers h e) positive
  have wt:=Z.reached h e
  have srcEq : Z.venue (C.src u)=Z.venue (C.src e.val):=Prod.ext (Option.some.inj (actual.src.symm.trans wt.src)) (actual.srcLow.symm.trans wt.srcLow)
  have dstEq : Z.venue (C.dst u)=Z.venue (C.dst e.val):=Prod.ext (Option.some.inj (actual.dst.symm.trans wt.dst)) (actual.dstLow.symm.trans wt.dstLow)
  have incident:C.src u=h ∨ C.dst u=h:=by
    rcases e.property.2 with src|dst
    · exact Or.inl (injectS (by rw [srcEq,src])).symm
    · exact Or.inr (injectT (by rw [dstEq,dst])).symm
  have same : u=e.val:=congrArg Subtype.val ((Z.raw h).injective (back incident up))
  subst u
  exact ⟨⟨fun eqn=>(injectS eqn).symm,fun eqn=>by rw [eqn]⟩,
    ⟨fun eqn=>(injectT eqn).symm,fun eqn=>by rw [eqn]⟩⟩

include shelf small symm in
/-- Output of the two scalar maps on exactly the old raw fields fetched at a
halo visit and ticket. The mark is read only on an actual surviving parent. -/
theorem funded_fields (marked : E→Prop) (h : U) (j : Fin (P*O)) (bit : Cell 1)
    (bitRead : ∀e:Local C h,(res).address h e=j→(bit.val=1 ↔ marked e.val)) :
    let old:=encode a 11 (Fused.columns (fetched h j))
    let cand:=DescentOrdinarySignedRanks.resident ((res).address h) j
    rawFlags old bit=cand.elim (flags false false false false) (fun e=>
      flags true (decide (C.src e.val=h)) (decide (C.dst e.val=h)) (decide (marked e.val))) ∧
    rawUnits (b:=b) old bit=cand.elim 0 (fun e=>(C.count e.val:Cell b)) := by
  intro old cand
  by_cases yes : ∃e:Local C h,(res).address h e=j
  · obtain ⟨e,rfl⟩:=yes
    have live:=Fused.fetched_read C R symm Z shelf small h ((res).address h e)
    rw [place_at] at live
    have flagsLive:=active_filtered (fetched h ((res).address h e))
    rw [live] at flagsLive
    have raw:=fetched_at C R symm Z shelf small h e
    have endpoints:=resident_ends C R Z shelf h e
    have fields:=tests_witness (⟨Z.venue h,Measured.visit C R symm Z h e,(Z.loc (Z.raw h e)).1,
        Z.read h e,small h _ _ _⟩:Fused.Raw R Q K L a) _ _ symm
      (Measured.fromOld C R symm Z h e) (Z.reached h e)
    have pair : tests (Fused.columns (fetched h ((res).address h e)))=
        (decide (C.src e.val=h),decide (C.dst e.val=h)) := by
      rw [raw,fields]
      simp [endpoints.1,endpoints.2]
    have mass : (Fused.columns (fetched h ((res).address h e)) 10).val=C.count e.val:=by
      rw [raw]; exact Z.survives h e
    simp only [old,cand,DescentOrdinarySignedRanks.resident_at,Option.elim_some,rawFlags,rawUnits,
      Equiv.symm_apply_apply,flagsLive,Option.isSome_some,ite_true,pair,mass,bitRead e rfl]
    exact ⟨trivial,trivial⟩
  · have off : Fused.filtered (fetched h j)=none := (Fused.fetched_read C R symm Z shelf small h j).trans
      (place_empty _ _ j (not_exists.mp yes))
    have noActive:=active_filtered (fetched h j)
    rw [off] at noActive
    simp [old,cand,DescentOrdinarySignedRanks.resident_miss _ j (not_exists.mp yes),rawFlags,rawUnits,noActive,flag_empty]

end
end Hierarchy.DescentOrdinarySignedMeta

end OAI
