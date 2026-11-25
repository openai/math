import OAI.ThreeFlat.Diagonal.CompressorIncidentProbe
import OAI.ThreeFlat.Diagonal.CompressorIncidentOrdinals
import Mathlib.Data.List.Nodup

namespace OAI
/-! # Semantic order of the six-word records produced by a shrink-site scan -/

noncomputable section

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.CommRing

variable {w : ℕ}

def positiveFirsts (seen : List (Word w)) : List (Word w) → List (Word w)
  | [] => []
  | x :: xs => let tail := positiveFirsts (x::seen) xs
                if x≠0 ∧ x∉seen then x::tail else tail

theorem selected_keys (V : F → Word w) (seen : List (Word w)) (xs : List Hit) :
    (selected V seen xs).map (fun a => V a.key) = positiveFirsts seen (xs.map fun a => V a.key) := by
  induction xs generalizing seen with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : V x.key≠0 ∧ V x.key∉seen <;> simp [selected,positiveFirsts,h,ih]

private theorem enumerate {A : Type*} (V : F → Word w) (xs : List Hit) (key : A ↪ Word w)
    (fields : A → Fin 6 → Word w) (nz : ∀ z,key z≠0)
    (sound : ∀ r∈xs,V r.key≠0 → ∃ z,V r.key=key z ∧ ∀ j,V (r.fields j)=fields z j)
    (complete : ∀ z,∃ r∈xs,V r.key=key z) :
    ∃ e : Fin (selected V [] xs).length ≃ A, ∀ i,
      V (((selected V [] xs).get i).key) = key (e i) ∧
      ∀ j,V (((selected V [] xs).get i).fields j)=fields (e i) j := by
  classical
  let ys := selected V [] xs
  have yes (i : Fin ys.length) : ys.get i ∈ ys := List.get_mem _ _
  have live (i : Fin ys.length) : V (ys.get i).key ≠ 0 := by
    exact ((mem_selectedKeys_iff V [] xs _).1 (List.mem_map.mpr ⟨_,yes i,rfl⟩)).1
  have chooseRow (i : Fin ys.length) := sound _ (selected_mem V [] xs (yes i)) (live i)
  choose value hkey hfields using chooseRow
  have inj : Function.Injective value := by
    intro i j h
    have eq := (hkey i).trans ((congrArg key h).trans (hkey j).symm)
    have nd := selectedKeys_nodup V [] xs
    apply Fin.ext
    let ys' := ys.map fun r => V r.key
    have e : ys'[i.val]'(by simp [ys']) = ys'[j.val]'(by simp [ys']) := by
      simpa [ys',List.get_eq_getElem] using eq
    exact nd.getElem_inj_iff.mp e
  have onto : Function.Surjective value := by
    intro z
    obtain ⟨r,hr,eq⟩ := (exists_selected_with_key_iff V [] xs (key z) (nz z) (by simp)).mpr (complete z)
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hr
    exact ⟨i,key.injective ((hkey i).symm.trans ((congrArg (fun a : Hit => V a.key) hi).trans eq))⟩
  exact ⟨Equiv.ofBijective value ⟨inj,onto⟩,fun i => ⟨hkey i,hfields i⟩⟩

variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {t l N : ℕ}
variable {S : Graph.Stage} (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (b : B ≃ Fin N)


/-- Keys omit zero, which is the native absence sentinel. -/
def positiveKey (z : P.Motif) : Word w := (((Demand.key P (baseNat b)) z.val+1:ℕ):Word w)

omit [Fintype B] [Fintype H] in
theorem positiveKey_inj (fit : ∀ a,(Demand.key P (baseNat b)) a+1<2^w) : Function.Injective (positiveKey (w:=w) P b) := by
  intro x y h
  apply Subtype.ext
  apply (Demand.key P (baseNat b)).injective
  have eq := congrArg Fin.val h
  change (((Demand.key P (baseNat b)) x.val+1:ℕ):Word w).val=(((Demand.key P (baseNat b)) y.val+1:ℕ):Word w).val at eq
  rw [Fin.val_cast_of_lt (fit _),Fin.val_cast_of_lt (fit _)] at eq
  omega

omit [Fintype B] [Fintype H] in
theorem positiveKey_ne (fit : ∀ a,(Demand.key P (baseNat b)) a+1<2^w) (z : P.Motif) : positiveKey (w:=w) P b z≠0 := by
  intro h
  have eq := congrArg Fin.val h
  change (((Demand.key P (baseNat b)) z.val+1:ℕ):Word w).val=0 at eq
  rw [Fin.val_cast_of_lt (fit _)] at eq
  omega

/-- This order depends only on the packed graph, layout and site. -/
def siteKeys (lay : Bool) (s : (Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))) : List (Word w) :=
  positiveFirsts [] ((visits S.degree S.colors).map fun a =>
    (Local.atSite P lay s a).elim 0 (positiveKey P b))

variable (E : Codec B w S.colors t l) (ptr : F) (data : Param → Word w) (mem : Memory w) (vs : Fin 1 → Word w)
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ}
variable (R : ArcReads P E (((oldColumns (Demand.formulaOps 1) ptr)).map (Formula.value data mem vs)) mem)
variable (W : Demand.WidthReads P E (baseNat b) data mem vs ((atField (Demand.formulaOps 1) ptr) oldWidths) ((atField (Demand.formulaOps 1) ptr) tags) ((atField (Demand.formulaOps 1) ptr) oldLanes) prior)
variable (hi : Function.Injective E.base) (hc : 2≤S.colors) (bits : 2^S.colors<2^w) (masks : 8≤w)
variable (K : ℕ) (lay : Bool) (v : Placement.Site F) (s : (Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))) (hv : v.map (Formula.value data mem vs)=siteCode E s)

include R W hi hc bits masks hv in
omit [Fintype B] [Fintype H] in
theorem visit_lookup (a : Local.Slots S.degree S.colors) :
    ((Formula.value data mem vs) (visit ptr S K lay v a).key=(Local.atSite P lay s a).elim 0 (positiveKey P b)) ∧
    ∀ z,Local.atSite P lay s a=some z →
      ∀ j,(Formula.value data mem vs) ((visit ptr S K lay v a).fields j)=descriptor P b ptr data mem vs hc K lay s z j := by
  let arc := Local.incidentArc P a.1 s a.2
  by_cases bad : P.thick (sourcePosition arc) ∧ P.thick (sourcePosition (P.actual arc))
  · have missing : Local.lookup P a.1 s a.2 = Option.none := by
      unfold Local.lookup
      dsimp only
      split
      · rename_i valid
        exact False.elim (valid bad)
      · rfl
    have absent : Local.atSite P lay s a = Option.none := by rw [Local.atSite, missing]; rfl
    have ne : (1:Word w)≠0 := by
      have room : 1<2^w := (by decide : 1<2^8).trans_le (Nat.pow_le_pow_right (by decide) masks)
      intro h
      have eq := congrArg Fin.val h
      rw [show (1:Word w).val=1 from Fin.val_cast_of_lt room] at eq
      exact Nat.one_ne_zero eq
    constructor
    · rw [absent]
      exact visit_invalid P E ptr data mem vs R K lay v s hv a bad ne
    · intro z hz
      rw [absent] at hz
      cases hz
  · let z : P.Motif := ⟨arc,bad⟩
    have yes := Local.lookup_eq P a.1 s a.2 z rfl
    have hh := visit_valid P E b ptr data mem vs R W hi hc bits masks K lay v s hv a z rfl
    by_cases here : ∃ j,partySite P lay z j=s
    · have hit := (Local.atSite_some P lay s a z).2 ⟨yes,here⟩
      exact ⟨by simpa [hit,positiveKey,here] using hh.1,by simpa [hit] using hh.2⟩
    · have absent : Local.atSite P lay s a = Option.none := by
        cases result : Local.atSite P lay s a with
        | none => rfl
        | some y =>
          obtain ⟨same, member⟩ := (Local.atSite_some P lay s a y).1 result
          have identity : z = y := Option.some.inj (yes.symm.trans same)
          exact False.elim (here (identity.symm ▸ member))
      constructor
      · rw [hh.1, ite_eq_right here, absent]; rfl
      · intro y hy
        rw [absent] at hy
        cases hy

include R W hi hc bits masks hv in
omit [Fintype B] [Fintype H] in
theorem mapped_keys :
    (selected (Formula.value data mem vs) [] (all ptr S K lay v)).map (fun a => (Formula.value data mem vs) a.key)=siteKeys P b lay s := by
  rw [selected_keys,all_eq_visits,List.map_map,siteKeys]
  apply congrArg (positiveFirsts [])
  apply List.map_congr_left
  intro a _
  exact (visit_lookup P b E ptr data mem vs R W hi hc bits masks K lay v s hv a).1

include R W hi hc bits masks hv in
omit [Fintype B] [Fintype H] in
theorem active_enumeration (fit : ∀ a,(Demand.key P (baseNat b)) a+1<2^w) :
    ∃ e : Fin (selected (Formula.value data mem vs) [] (all ptr S K lay v)).length ≃ MotifKernel.Active (partySite P lay) s, ∀ i,
      (Formula.value data mem vs) (((selected (Formula.value data mem vs) [] (all ptr S K lay v)).get i).key)=positiveKey P b (e i).val ∧
      ∀ j,(Formula.value data mem vs) (((selected (Formula.value data mem vs) [] (all ptr S K lay v)).get i).fields j)=descriptor P b ptr data mem vs hc K lay s (e i).val j := by
  let key : MotifKernel.Active (partySite P lay) s ↪ Word w :=
    ⟨fun z => positiveKey P b z.val,fun _ _ h => Subtype.ext (positiveKey_inj P b fit h)⟩
  refine enumerate (Formula.value data mem vs) (all ptr S K lay v) key
    (fun z j => descriptor P b ptr data mem vs hc K lay s z.val j)
    (fun z => positiveKey_ne P b fit z.val) ?_ ?_
  · intro r hr live
    obtain ⟨a,rfl⟩ := (mem_all ptr S K lay v r).1 hr
    have h := visit_lookup P b E ptr data mem vs R W hi hc bits masks K lay v s hv a
    cases eq : Local.atSite P lay s a with
    | none => exact False.elim (live (by simpa [eq] using h.1))
    | some z =>
      refine ⟨⟨z,((Local.atSite_some P lay s a z).1 eq).2⟩, ?_, h.2 z eq⟩
      change Formula.value data mem vs (visit ptr S K lay v a).key = positiveKey (w:=w) P b z
      simpa [eq] using h.1
  · intro z
    obtain ⟨a,ha⟩ := Local.atSite_covers P lay s z.val z.property
    refine ⟨_,(mem_all ptr S K lay v _).2 ⟨a,rfl⟩,?_⟩
    change Formula.value data mem vs (visit ptr S K lay v a).key = positiveKey (w:=w) P b z.val
    simpa [ha] using (visit_lookup P b E ptr data mem vs R W hi hc bits masks K lay v s hv a).1


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents

end

end OAI
