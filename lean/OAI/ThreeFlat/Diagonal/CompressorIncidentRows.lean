import OAI.ThreeFlat.Diagonal.ShrinkAssemblyOrder
import OAI.ThreeFlat.Diagonal.CompressorIncidentCatalog
import OAI.ThreeFlat.Diagonal.CompressorIncidentAddresses

namespace OAI
/-! # Uniform ordered active motif rows, including the unused zero suffix -/

noncomputable section

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.NatCast

variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {w t l N : ℕ}
variable {S : Graph.Stage} (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (b : B ≃ Fin N) (lay : Bool) (s : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))

/-- One order for every invocation on the same actual packed site, independent
of the changing scan address and memory pointers. -/
structure SiteOrder (w : ℕ) where
  equiv : Fin (siteKeys (w:=w) P b lay s).length ≃ MotifKernel.Active (partySite P lay) s
  key_eq : ∀ i,(siteKeys (w:=w) P b lay s).get i = positiveKey P b (equiv i).val

theorem SiteOrder.length_eq (O : SiteOrder P b lay s w) :
    (siteKeys (w:=w) P b lay s).length=Fintype.card (MotifKernel.Active (partySite P lay) s) := by
  simpa using Fintype.card_congr O.equiv

variable (E : Codec B w S.colors t l) (ptr : F) (data : Param → Word w) (mem : Memory w) (vs : Fin 1 → Word w)
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ}
variable (R : ArcReads P E ((oldColumns (Demand.formulaOps 1) ptr).map (Formula.value data mem vs)) mem)
variable (W : Demand.WidthReads P E (baseNat b) data mem vs ((atField (Demand.formulaOps 1) ptr) oldWidths) ((atField (Demand.formulaOps 1) ptr) tags) ((atField (Demand.formulaOps 1) ptr) oldLanes) prior)
variable (hi : Function.Injective E.base) (hc : 2≤S.colors) (bits : 2^S.colors<2^w) (masks : 8≤w)
variable (fit : ∀ a,(Demand.key P (baseNat b)) a+1<2^w) (K : ℕ) (v : Placement.Site F) (hv : v.map (Formula.value data mem vs)=siteCode E s)

private theorem getKey {ys : List Hit} {ys' : List (Word w)}
    (h : ys.map (fun r => (Formula.value data mem vs) r.key)=ys') (i : Fin ys.length)
    (hl : ys.length=ys'.length) : ys'.get (finCongr hl i) = (Formula.value data mem vs) (ys.get i).key := by
  subst ys'
  simp [List.get_eq_getElem]


include R W hi hc bits masks hv fit K in
omit [Fintype B] [Fintype H] in
theorem site_order : Nonempty (SiteOrder P b lay s w) := by
  obtain ⟨e,read⟩ := active_enumeration P b E ptr data mem vs R W hi hc bits masks K lay v s hv fit
  have mapped := mapped_keys P b E ptr data mem vs R W hi hc bits masks K lay v s hv
  have len : (selected (Formula.value data mem vs) [] (all ptr S K lay v)).length=(siteKeys (w:=w) P b lay s).length := by simpa using congrArg List.length mapped
  refine ⟨⟨(finCongr len).symm.trans e,?_⟩⟩
  intro j
  let i := (finCongr len).symm j
  have eq : finCongr len i=j := (finCongr len).apply_symm_apply j
  exact (eq ▸ getKey data mem vs mapped i len).trans (read i).1

include R W hi hc bits masks hv fit in
omit [Fintype B] [Fintype H] in
theorem ordered_values (order : SiteOrder P b lay s w) :
    ∃ len : (selected (Formula.value data mem vs) [] (all ptr S K lay v)).length=(siteKeys (w:=w) P b lay s).length, ∀ i : Fin (selected (Formula.value data mem vs) [] (all ptr S K lay v)).length, ∀ j,
      (Formula.value data mem vs) (((selected (Formula.value data mem vs) [] (all ptr S K lay v)).get i).fields j)=descriptor P b ptr data mem vs hc K lay s (order.equiv (finCongr len i)).val j := by
  obtain ⟨e,h⟩ := active_enumeration P b E ptr data mem vs R W hi hc bits masks K lay v s hv fit
  have mapped := mapped_keys P b E ptr data mem vs R W hi hc bits masks K lay v s hv
  have len : (selected (Formula.value data mem vs) [] (all ptr S K lay v)).length=(siteKeys (w:=w) P b lay s).length := by simpa using congrArg List.length mapped
  refine ⟨len,fun i j => ?_⟩
  have same := positiveKey_inj P b fit (((h i).1.symm.trans (getKey data mem vs mapped i len).symm).trans
    (order.key_eq (finCongr len i)))
  rw [←same]
  exact (h i).2 j

private theorem mask_room (h : 8≤w) : 6<2^w :=
  (by decide : 6<2^8).trans_le (Nat.pow_le_pow_right (by decide) h)

variable (tagsR : ((Formula.value data mem vs) ((atField (Demand.formulaOps 1) ptr) tags)).val=2^t) (laneR : ((Formula.value data mem vs) ((atField (Demand.formulaOps 1) ptr) remaining)).val=2^l)
variable (room : capacity S<2^w)

include R W hi hc bits masks tagsR laneR in
omit [Fintype B] [Fintype H] in
theorem count_at (site : F) (address : ((Formula.value data mem vs) site).val=siteNumber b s) :
    (Formula.value data mem vs) (count ptr S K lay site)=((siteKeys (w:=w) P b lay s).length:Word w) := by
  let v' := siteAt ptr site
  have geom : v'.map (Formula.value data mem vs)=siteCode E s := siteAt_code data mem vs E b ptr site s W.baseWord tagsR laneR address
  have mapped := mapped_keys P b E ptr data mem vs R W hi hc bits masks K lay v' s geom
  have len := congrArg List.length mapped
  change (Formula.value data mem vs) (occupied (firsts [] (all ptr S K lay v'))) = _
  rw [occupied_firsts data mem vs (by have := mask_room masks; omega)]
  simpa only [List.length_map] using congrArg (fun n : ℕ => (n:Word w)) len

include R W hi hc bits masks hv K in
omit [Fintype B] [Fintype H] in
/-- The cap bounds the actual count for every site, including empty sites. -/
theorem siteKeys_le : (siteKeys (w:=w) P b lay s).length≤capacity S := by
  have mapped := mapped_keys P b E ptr data mem vs R W hi hc bits masks K lay v s hv
  have len : (selected (Formula.value data mem vs) [] (all ptr S K lay v)).length=(siteKeys (w:=w) P b lay s).length := by simpa using congrArg List.length mapped
  exact len ▸ (selected_length_le (Formula.value data mem vs) [] (all ptr S K lay v)).trans (length_all ptr S K lay v).le

include R W hi hc bits masks fit room tagsR laneR in
omit [Fintype B] [Fintype H] in
/-- The physical count word itself indexes exactly the active motif subtype. -/
theorem site_catalog (site : F) (address : ((Formula.value data mem vs) site).val=siteNumber b s) :
    ∃ (order : SiteOrder P b lay s w)
      (h : ((Formula.value data mem vs) (count ptr S K lay site)).val=(siteKeys (w:=w) P b lay s).length),
      Function.Bijective (order.equiv ∘ (finCongr h)) := by
  let v' := siteAt ptr site
  have geom : v'.map (Formula.value data mem vs)=siteCode E s := siteAt_code data mem vs E b ptr site s W.baseWord tagsR laneR address
  obtain ⟨order⟩ := site_order P b lay s E ptr data mem vs R W hi hc bits masks fit K v' geom
  have bound := siteKeys_le P b lay s E ptr data mem vs R W hi hc bits masks K v' geom
  have h : ((Formula.value data mem vs) (count ptr S K lay site)).val=(siteKeys (w:=w) P b lay s).length := by
    rw [count_at P b lay s E ptr data mem vs R W hi hc bits masks K tagsR laneR site address,
      Fin.val_cast_of_lt (bound.trans_lt room)]
  exact ⟨order,h,order.equiv.bijective.comp (finCongr h).bijective⟩

include R W hi hc bits masks fit room tagsR laneR in
omit [Fintype B] [Fintype H] in
theorem record_at (order : SiteOrder P b lay s w) (linear : F) (i : Fin (siteKeys (w:=w) P b lay s).length) (field : Fin 6)
    (index : i.val<capacity S) (address : ((Formula.value data mem vs) linear).val=6*(capacity S*siteNumber b s+i.val)+field.val) :
    (Formula.value data mem vs) (record ptr S K lay linear) = descriptor P b ptr data mem vs hc K lay s (order.equiv i).val field := by
  obtain ⟨hs,hk,hf⟩ := split_record data mem vs S linear (siteNumber b s) i.val field (mask_room masks) room index address
  let v' := siteAt ptr (rowSite S linear)
  let ys := all ptr S K lay v'
  have geom : v'.map (Formula.value data mem vs)=siteCode E s :=
    siteAt_code data mem vs E b ptr _ s W.baseWord tagsR laneR hs
  obtain ⟨len,reads⟩ := ordered_values P b lay s E ptr data mem vs R W hi hc bits masks fit K v' geom order
  let j : Fin (selected (Formula.value data mem vs) [] ys).length := ⟨((Formula.value data mem vs) (rowRank S linear)).val,by rw [hk,len]; exact i.isLt⟩
  have same : finCongr len j=i := Fin.ext hk
  have sz : ys.length<2^w := by simpa only [ys,length_all] using room
  change (Formula.value data mem vs) (fieldAt (firsts [] ys) (rowRank S linear) (rowField linear)) = _
  rw [fieldAt_firsts_of_lt data mem vs (mask_room masks).le ys sz _ _ field hf j.isLt]
  exact (reads j field).trans (by rw [same])

include R W hi hc bits masks tagsR laneR room in
omit [Fintype B] [Fintype H] in
theorem record_after (linear : F) (i : ℕ) (field : Fin 6) (index : i<capacity S)
    (past : (siteKeys (w:=w) P b lay s).length≤ i) (address : ((Formula.value data mem vs) linear).val=6*(capacity S*siteNumber b s+i)+field.val) :
    (Formula.value data mem vs) (record ptr S K lay linear) = 0 := by
  obtain ⟨hs,hk,hf⟩ := split_record data mem vs S linear (siteNumber b s) i field (mask_room masks) room index address
  let v' := siteAt ptr (rowSite S linear)
  let ys := all ptr S K lay v'
  have geom : v'.map (Formula.value data mem vs)=siteCode E s := siteAt_code data mem vs E b ptr _ s W.baseWord tagsR laneR hs
  have h := mapped_keys P b E ptr data mem vs R W hi hc bits masks K lay v' s geom
  have len : (selected (Formula.value data mem vs) [] ys).length=(siteKeys (w:=w) P b lay s).length := by simpa using congrArg List.length h
  have sz : ys.length<2^w := by simpa only [ys,length_all] using room
  exact fieldAt_firsts_of_le data mem vs (mask_room masks).le ys sz _ _ field hf (by rw [hk,len]; exact past)

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents

end

noncomputable section
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents
open Computability.VPVNP.Compression Placement
open scoped Classical Fin.NatCast
open Computability.VPVNP.BurstRAM PrivateRAM
variable {w : ℕ}

private theorem keys_first {A : Type*} [DecidableEq A] (key : A → Word w)
    (inj : Function.Injective key) (nz : ∀a,key a≠0) (xs : List (Option A))
    (seen : List A) (keys : List (Word w)) (agrees : ∀a,key a∈keys ↔ a∈seen) :
    positiveFirsts keys (xs.map (fun x=>x.elim 0 key))=(Local.firstMotifs seen xs).map key := by
  induction xs generalizing seen keys with
  | nil=>rfl
  | cons z xs ih=>
    cases z with
    | none=>
      change positiveFirsts keys (0 :: xs.map (fun x => x.elim 0 key)) = (Local.firstMotifs seen xs).map key
      rw [positiveFirsts]
      simp only [ne_self_iff_false,false_and,ite_false]
      apply ih;intro a;simp [nz,agrees]
    | some a=>
      have tailRows:=ih (a::seen) (key a::keys) (by intro b;simp [inj.eq_iff,agrees])
      have keep : (key a≠0 ∧ key a∉keys) ↔ a∉seen := by simp [nz,agrees]
      change positiveFirsts keys (key a :: xs.map (fun x => x.elim 0 key)) = _
      rw [positiveFirsts]
      by_cases old:a∈seen <;> simp [keep,old,tailRows,Local.firstMotifs]

private theorem keys_visited {A J : Type*} [DecidableEq A] (key : A → Word w)
    (readSite : J → Option A) (jobs : List J)
    (inj : Function.Injective key) (nz : ∀ a, key a ≠ 0) :
    positiveFirsts [] (jobs.map (fun i => (readSite i).elim 0 key)) =
      (Local.firstMotifs [] (jobs.map readSite)).map key := by
  simpa only [List.map_map, Function.comp_def] using
    keys_first key inj nz (jobs.map readSite) [] [] (by simp)

variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {N t l : ℕ} {S : Graph.Stage}
variable (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors) (b : B ≃ Fin N)
variable (lay : Bool) (s : Site B (BitWord t) (BitWord l))
variable (fit : ∀a,Demand.key P (baseNat b) a+1<2^w)

include fit

set_option maxHeartbeats 1200000 in
omit [Fintype B] [Fintype H] in
theorem siteKeys_assembly : siteKeys (w:=w) P b lay s=(Local.assemblyList P lay s).map (positiveKey P b) := by
  let key := positiveKey (w:=w) P b
  have actual := keys_visited key (Local.atSite P lay s) (visits S.degree S.colors)
    (positiveKey_inj P b fit) (positiveKey_ne P b fit)
  unfold siteKeys Local.assemblyList
  dsimp only [key] at actual
  set_option pp.explicit true in
    convert actual using 1;
      repeat' first | exact Subsingleton.elim _ _ | rfl | apply congrArg | congr 1

omit [Fintype B] [Fintype H] in
theorem assembly_length : (siteKeys (w:=w) P b lay s).length=Local.assemblyCount P lay s := by
  rw [siteKeys_assembly P b lay s fit,List.length_map];rfl

def assemblySiteOrder : SiteOrder P b lay s w where
  equiv := (finCongr (assembly_length P b lay s fit)).trans (Local.assemblyOrder P lay s)
  key_eq i := by
    change (siteKeys P b lay s).get i=positiveKey P b
      (Local.assemblyOrder P lay s (finCongr (assembly_length P b lay s fit) i)).val
    rw [Local.assemblyOrder_value]
    have small : i.val<(Local.assemblyList P lay s).length := by
      have h:=assembly_length P b lay s fit
      exact i.isLt.trans_eq h
    change (siteKeys (w:=w) P b lay s)[i.val] =
      positiveKey P b ((Local.assemblyList P lay s)[i.val]'small)
    have eqv:=congrArg (fun xs : List (Word w)=>xs[i.val]?) (siteKeys_assembly P b lay s fit)
    simpa only [List.getElem?_eq_getElem i.isLt,List.getElem?_map,List.getElem?_eq_getElem small,
      Option.map_some,Option.some.injEq,List.get_eq_getElem] using eqv

omit [Fintype B] [Fintype H] in
theorem SiteOrder.eq_assembly (o : SiteOrder P b lay s w) (i : Fin (siteKeys (w:=w) P b lay s).length) :
    o.equiv i=Local.assemblyOrder P lay s (finCongr (assembly_length P b lay s fit) i) := by
  apply Subtype.ext
  apply positiveKey_inj P b fit
  exact (o.key_eq i).symm.trans ((assemblySiteOrder P b lay s fit).key_eq i)



end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents
end

end OAI
