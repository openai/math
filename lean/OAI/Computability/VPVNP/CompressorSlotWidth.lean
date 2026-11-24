import OAI.Computability.VPVNP.CompressorSlotWidthScan
import OAI.Computability.VPVNP.CompressorSlotBaseLookup
import OAI.Computability.VPVNP.ShrinkPayload

/-!
# Width lookup on the sorted shrinking output

The split array is indexed by original old arc (including its lane), role-edge
type, and local subdivision. The canonical outgoing array is indexed by the new
site and its local slot. The two lookups refer to the same selected motif.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotWidthScan

open Compression Compression.PackingData Compression.SurvivingSlots Slots SlotSchedule BurstRAM PrimedStackRAM

variable {V H Tag L : Type} {d c N J nL degree pad w : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (subdiv : Fin 4 → ℕ)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)

/-- The chosen widths in the contiguous old-arc/type/subdivision rows. -/
def SplitRows (oldWidth : P.Motif → Fin 4 → ℕ) (base : ℕ) (m : Memory w) : Prop :=
  ∀ i : Id P.Motif subdiv,
    m (base + (((oldArcIndex P vertices tags lanes i.2.1.val).val*4+i.1.val)*(∑ t,subdiv t)+i.2.2.val)) =
      Fin.ofNat _ (splitWidth (oldWidth i.2.1 i.1) (subdiv i.1) i.2.2)

theorem splitOffset_lt (i : Id P.Motif subdiv) :
    ((oldArcIndex P vertices tags lanes i.2.1.val).val*4+i.1.val)*(∑t,subdiv t)+i.2.2.val <
      (oldBaseArcCount N J d c*nL)*4*(∑t,subdiv t) := by
  let n := (oldArcIndex P vertices tags lanes i.2.1.val).val
  have ho := Nat.mul_le_mul_right 4 (Nat.succ_le_of_lt (oldArcIndex P vertices tags lanes i.2.1.val).isLt)
  rw [Nat.succ_mul] at ho
  have ht : n*4+i.1.val+1 ≤ (oldBaseArcCount N J d c*nL)*4 := by have := i.1.isLt; omega
  have hu := Nat.mul_le_mul_right (∑t,subdiv t) ht
  rw [Nat.succ_mul] at hu
  have hj : i.2.2.val < ∑t,subdiv t := i.2.2.isLt.trans_le
    (Finset.single_le_sum (fun t _ ↦ Nat.zero_le (subdiv t)) (Finset.mem_univ i.1))
  change (n*4+i.1.val)*(∑t,subdiv t)+i.2.2.val < _; omega

theorem SplitRows.congr_below {oldWidth : P.Motif → Fin 4 → ℕ} {base stop : ℕ} {m m' : Memory w}
    (split : SplitRows P subdiv vertices tags lanes oldWidth base m)
    (room : base+(oldBaseArcCount N J d c*nL)*4*(∑t,subdiv t) ≤ stop) (frame : ∀ a < stop, m' a=m a) :
    SplitRows P subdiv vertices tags lanes oldWidth base m' := by
  intro i
  rw [frame _ (by have := splitOffset_lt P subdiv vertices tags lanes i; omega)]
  exact split i

private theorem divLow {n : ℕ} (x : Fin n) (h : ℕ) : (x.val+n*h)/n=h := by
  rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt x.isLt),Nat.div_eq_of_lt x.isLt,Nat.zero_add]
private theorem modLow {n : ℕ} (x : Fin n) (h : ℕ) : (x.val+n*h)%n=x.val := by simp [Nat.mod_eq_of_lt x.isLt]

/-- Reading the digits of a genuine absolute ID produces its exact split-row offset. -/
theorem splitNumber_genuine (i : Id P.Motif subdiv) :
    splitNumber nL (∑ t,subdiv t) (oldBaseArcCount N J d c)
        (arcAddress P subdiv vertices tags lanes pad (.inl i)).val =
      ((oldArcIndex P vertices tags lanes i.2.1.val).val*4+i.1.val)*(∑ t,subdiv t)+i.2.2.val := by
  let old := P.baseMotifIndex vertices tags (P.baseMotif i.2.1)
  let g := lanes (P.sourceLane i.2.1)
  let j := i.2.2.castLE (Finset.single_le_sum (fun t _ ↦ Nat.zero_le (subdiv t)) (Finset.mem_univ i.1))
  have hk : (relativeKey P subdiv vertices tags i).val = j.val + (∑ t,subdiv t)*(old.val+(oldBaseArcCount N J d c)*i.1.val) := by
    change j.val+(∑ t,subdiv t)*old.val+(oldBaseArcCount N J d c*(∑ t,subdiv t))*i.1.val=_
    ring
  have ha : (arcAddress P subdiv vertices tags lanes pad (.inl i)).val = g.val + nL*(relativeKey P subdiv vertices tags i).val := rfl
  have hold : (oldArcIndex P vertices tags lanes i.2.1.val).val = g.val+nL*old.val := rfl
  rw [splitNumber,ha,divLow,modLow,hk,divLow,modLow,divLow,modLow,hold]
  change _ = ( _ * 4 + i.1.val)*(∑ t,subdiv t)+j.val
  ring

/-- Ordinary new outgoing slot number: site first, local slot second. -/
def portIndex : ((V × Tag) × L) × Fin degree ≃ Fin ((N*(J*nL))*degree) :=
  ((((Equiv.prodAssoc V Tag L).trans (siteIndex vertices tags lanes)).prodCongr (Equiv.refl _))).trans finProdFinEquiv

private theorem width_atLane (layout : Bool) (oldWidth : P.Motif → Fin 4 → ℕ)
    (outgoing : PaddedId (V×Tag) (Id P.BaseMotif subdiv) pad ≃ (V×Tag)×Fin degree)
    (z : PaddedId (V×Tag) (Id P.BaseMotif subdiv) pad) (g : L) :
    P.shrinkSlotWidth layout subdiv oldWidth outgoing (outgoing z,g) =
      Sum.elim (fun i : Id P.Motif subdiv ↦ splitWidth (oldWidth i.2.1 i.1) (subdiv i.1) i.2.2)
        (fun _ ↦ 0) (atLane P subdiv layout z g) := by
  cases z with
  | inr p => exact P.shrinkSlotWidth_padding layout subdiv oldWidth outgoing p g
  | inl z =>
    let e := P.survivingLaneEquiv layout subdiv
    have h := P.shrinkSlotWidth_genuine layout subdiv oldWidth outgoing (e.symm (z,g))
    rw [P.shrinkArcEquiv_genuine] at h
    change P.shrinkSlotWidth layout subdiv oldWidth outgoing
      ((outgoing (.inl (e (e.symm (z,g))).1)),(e (e.symm (z,g))).2) = _ at h
    rwa [e.apply_symm_apply] at h

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L] [Module (ZMod 2) Tag]

/-- One actual outgoing slot: both read addresses are inside their allocated
input regions and the written word is the width used in the semantic shrinking step. -/
theorem readback (layout : Bool) (oldWidth : P.Motif → Fin 4 → ℕ)
    (hc : 2 ≤ c) (hφ : P.slots.ValidTagOffsets P.tagShift P.offset)
    (hd : survivingDegree d c subdiv ≤ degree) (hJ : 1 < J) (p : Fin 8 → Word w) (m : Memory w)
    (hdg : (p 0).val=degree) (hl : (p 1).val=nL) (hs : (p 2).val=∑ t,subdiv t)
    (hb : (p 3).val=oldBaseArcCount N J d c) (hg : (p 4).val=keyCount N J d c subdiv*nL)
    (hw : 2 < 2^w) (hrow : (p 5).val+((N*(J*nL))*2)*degree ≤ (p 7).val)
    (hsplit : (p 6).val+(oldBaseArcCount N J d c*nL)*4*(∑t,subdiv t) ≤ (p 7).val)
    (hs0 : (p 6).val < (p 7).val) (e : ((V×Tag)×L)×Fin degree) (split : SplitRows P subdiv vertices tags lanes oldWidth (p 6).val m) :
    let pad := degree-survivingDegree d c subdiv
    let D := slotDirectory P subdiv vertices tags lanes layout (pad := pad)
    let hD := fun b ↦ (slotDirectory_degree P subdiv vertices tags lanes hc layout b).trans (Nat.add_sub_of_le hd)
    let := P.slotIdentifierOrder vertices tags subdiv
    let I := P.regularizedSlotIndexing hc hφ layout subdiv hd tags hJ
    let cursor := Fin.ofNat (2^w) (portIndex vertices tags lanes e).val
    (∀ x, m ((p 5).val+(sortedFields D degree hD x).val) = Fin.ofNat _ (D.address x).val) →
    RecordCount N J nL d c pad subdiv*2 ≤ 2^w →
      (row p cursor).val < (p 7).val ∧ (splitAddr p m cursor).val < (p 7).val ∧
      width p m cursor = Fin.ofNat _ (P.shrinkSlotWidth layout subdiv oldWidth I.outgoing ((e.1.1,e.2),e.1.2)) := by
  intro pad D hD order I cursor tab fits
  let p₀ := (e.1.1,e.2)
  let z := I.outgoing.symm p₀
  let i := atLane P subdiv layout z e.1.2
  have hz : paddedBaseId P subdiv i = z := baseId_atLane P subdiv layout z e.1.2
  have hsrc : I.outgoing z = p₀ := I.outgoing.apply_symm_apply p₀
  have hend := (endpoints_atLane P subdiv tags layout z e.1.2).1
  have hpos : actualEnd P subdiv tags layout false i = (e.1.1.1,e.1.1.2,e.1.2) :=
    hend.trans (congrArg (fun b : V×Tag ↦ (b.1,b.2,e.1.2)) ((I.src_eq z).symm.trans (congrArg Prod.fst hsrc)))
  let owner := siteIndex vertices tags lanes (e.1.1.1,e.1.1.2,e.1.2)
  have hcursorBound : (portIndex vertices tags lanes e).val < ((N*(J*nL))*2)*degree :=
    (portIndex vertices tags lanes e).isLt.trans_le (Nat.mul_le_mul_right degree (by omega))
  have hv : cursor.val = (portIndex vertices tags lanes e).val := Nat.mod_eq_of_lt (by have := (p 7).isLt; omega)
  have hrect : rowNumber (p 0).val cursor.val = (sortedFields D degree hD (i,0)).val := by
    have h := rectangular_slot P subdiv vertices tags lanes hc hφ layout hd hJ i 0
    change (sortedFields D degree hD (i,0)).val = (I.outgoing (paddedBaseId P subdiv i)).2.val+degree*(D.owner (i,0)).val at h
    rw [hz,hsrc] at h
    change (sortedFields D degree hD (i,0)).val = e.2.val+degree*(0+2*(siteIndex vertices tags lanes (actualEnd P subdiv tags layout false i)).val) at h
    rw [h,hpos,hv,hdg]
    change rowNumber degree (e.2.val+degree*owner.val) = e.2.val+degree*(0+2*owner.val)
    rw [rowNumber,divLow,modLow]; ring
  have hlt : (p 5).val+rowNumber (p 0).val cursor.val < (p 7).val := by
    rw [hrect]; have hi : (sortedFields D degree hD (i,0)).val < ((N*(J*nL))*2)*degree := (sortedFields D degree hD (i,0)).isLt; omega
  have hfa : (m ((p 5).val+rowNumber (p 0).val cursor.val)).val/2 = (arcAddress P subdiv vertices tags lanes pad i).val := by
    rw [hrect,tab,Fin.val_ofNat,Nat.mod_eq_of_lt ((D.address (i,0)).isLt.trans_le fits)]
    exact divLow (0 : Fin 2) (arcAddress P subdiv vertices tags lanes pad i).val
  have hwidth := width_atLane P subdiv layout oldWidth I.outgoing z e.1.2
  rw [hsrc] at hwidth
  change P.shrinkSlotWidth layout subdiv oldWidth I.outgoing ((e.1.1,e.2),e.1.2) = Sum.elim _ _ i at hwidth
  have hwval := width_eq p m cursor hw (hlt.trans (p 7).isLt)
  dsimp only at hwval
  rw [hfa,hl,hs,hb,hg] at hwval
  refine ⟨(row_val p cursor hw (hlt.trans (p 7).isLt)).trans_lt hlt,?_⟩
  cases he : i with
  | inr x =>
    have ge : ¬ (arcAddress P subdiv vertices tags lanes pad (.inr x)).val < keyCount N J d c subdiv*nL := by
      change ¬ keyCount N J d c subdiv*nL + _ < _; omega
    rw [he] at hwval hwidth
    obtain ⟨haddr,hvalue⟩ := hwval (fun bad ↦ (ge bad).elim)
    exact ⟨by simpa only [ite_eq_right ge,haddr] using hs0, by rw [hwidth]; exact hvalue.trans (ite_eq_right ge)⟩
  | inl j =>
    have real : (arcAddress P subdiv vertices tags lanes pad (.inl j)).val < keyCount N J d c subdiv*nL :=
      (finProdFinEquiv (relativeKey P subdiv vertices tags j,lanes (P.sourceLane j.2.1))).isLt
    rw [he] at hwval hwidth
    rw [splitNumber_genuine] at hwval
    let old := oldArcIndex P vertices tags lanes j.2.1.val
    let idx := (old.val*4+j.1.val)*(∑ t,subdiv t)+j.2.2.val
    have ho := Nat.mul_le_mul_right 4 (Nat.succ_le_of_lt old.isLt)
    rw [Nat.succ_mul] at ho
    have ht : old.val*4+j.1.val+1 ≤ (oldBaseArcCount N J d c*nL)*4 := by have := j.1.isLt; omega
    have hu := Nat.mul_le_mul_right (∑t,subdiv t) ht
    rw [Nat.succ_mul] at hu
    have hj : j.2.2.val < ∑t,subdiv t := j.2.2.isLt.trans_le
      (Finset.single_le_sum (fun t _ ↦ Nat.zero_le (subdiv t)) (Finset.mem_univ j.1))
    have hi : (p 6).val+idx < (p 7).val := by dsimp only [idx]; omega
    obtain ⟨haddr,hvalue⟩ := hwval (fun _ ↦ hi.trans (p 7).isLt)
    rw [ite_eq_left real] at haddr hvalue
    exact ⟨haddr.trans_lt hi, hvalue.trans (by rw [hwidth]; exact split j)⟩

/-- Every canonical outgoing width is written once, including all zero-width
slots and the dummy tail. -/
theorem write_all (layout : Bool) (oldWidth : P.Motif → Fin 4 → ℕ)
    (hc : 2 ≤ c) (hφ : P.slots.ValidTagOffsets P.tagShift P.offset)
    (hd : survivingDegree d c subdiv ≤ degree) (hJ : 1 < J) (p : Fin 8 → Word w) (m : Memory w)
    (hdg : (p 0).val=degree) (hl : (p 1).val=nL) (hs : (p 2).val=∑ t,subdiv t)
    (hb : (p 3).val=oldBaseArcCount N J d c) (hg : (p 4).val=keyCount N J d c subdiv*nL)
    (hw : 2 < 2^w) (hrow : (p 5).val+((N*(J*nL))*2)*degree ≤ (p 7).val)
    (hsplit : (p 6).val+(oldBaseArcCount N J d c*nL)*4*(∑t,subdiv t) ≤ (p 7).val)
    (hs0 : (p 6).val < (p 7).val) (split : SplitRows P subdiv vertices tags lanes oldWidth (p 6).val m)
    (room : (p 7).val+(N*(J*nL))*degree ≤ 2^w) :
    let pad := degree-survivingDegree d c subdiv
    let D := slotDirectory P subdiv vertices tags lanes layout (pad := pad)
    let hD := fun b ↦ (slotDirectory_degree P subdiv vertices tags lanes hc layout b).trans (Nat.add_sub_of_le hd)
    let := P.slotIdentifierOrder vertices tags subdiv
    let I := P.regularizedSlotIndexing hc hφ layout subdiv hd tags hJ
    let M := (template visit 0).instantiate w p
    let n := (N*(J*nL))*degree
    (∀ x, m ((p 5).val+(sortedFields D degree hD x).val) = Fin.ofNat _ (D.address x).val) →
    RecordCount N J nL d c pad subdiv*2 ≤ 2^w →
    ∃ rs, runSegment M.program 43 (some 0) m (List.replicate n []) = some rs ∧
      endState (some 0) rs = some (Fin.ofNat _ n) ∧
      (∀ e, after m (eventLog rs) ((p 7).val+(portIndex vertices tags lanes e).val) =
        Fin.ofNat _ (P.shrinkSlotWidth layout subdiv oldWidth I.outgoing ((e.1.1,e.2),e.1.2))) ∧
      (∀ addr, addr < (p 7).val ∨ (p 7).val+n ≤ addr → after m (eventLog rs) addr=m addr) ∧
      RAMBuckets.cost Report.probes rs = 4*n := by
  intro pad D hD order I M n tab hspace
  have step e := readback P subdiv vertices tags lanes layout oldWidth hc hφ hd hJ p m hdg hl hs hb hg
    hw hrow hsplit hs0 e split tab hspace
  let ord := portIndex vertices tags lanes (degree := degree)
  obtain ⟨rs,hr,cursor,written,frame,cost⟩ := run p m n room (fun j hj ↦ by
    let e := ord.symm ⟨j,hj⟩
    have hi : (portIndex vertices tags lanes e).val = j := congrArg Fin.val (ord.apply_symm_apply ⟨j,hj⟩)
    obtain ⟨a,b,_⟩ := step e
    rw [hi] at a b; exact ⟨a,b⟩)
  exact ⟨rs,hr,cursor,fun e ↦ (written _ (ord e).isLt).trans (step e).2.2,frame,cost⟩

end CompressorRecords.SlotWidthScan

end VPVNP
end Computability
end OAI
