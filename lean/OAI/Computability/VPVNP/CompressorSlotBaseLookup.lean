import OAI.Computability.VPVNP.CompressorSlotNetwork

/-!
# Extracting the base target and lane displacement from the endpoint arrays

The packed graph is a lift. At source lane zero the destination lane is the
base arc displacement. Unpacking the destination rectangular slot therefore
recovers both base-table words needed by the next substep, for real and dummy
arcs alike.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotSchedule

open Compression Compression.PackingData Compression.SurvivingSlots Slots BurstRAM

variable {V H Tag L : Type*} {d c N J nL pad : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (subdiv : Fin 4 → ℕ)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)

/-- The actual arc at a given source-role lane over the padded base ID. -/
def atLane (layout : Bool) (z : PaddedId (V × Tag) (Id P.BaseMotif subdiv) pad) (g : L) :
    ActualId P subdiv pad :=
  match z with
  | .inl a => .inl ((P.survivingLaneEquiv layout subdiv).symm (a,g))
  | .inr (b,j) => .inr ((b.1,b.2,g),j)

theorem baseId_atLane (layout : Bool) (z : PaddedId (V × Tag) (Id P.BaseMotif subdiv) pad) (g : L) :
    paddedBaseId P subdiv (atLane P subdiv layout z g) = z := by
  cases z with
  | inl a =>
    let e := P.survivingLaneEquiv layout subdiv
    have hb (i : Id P.Motif subdiv) : (e i).1 = baseId P subdiv i := by cases i; rfl
    change Sum.inl (baseId P subdiv (e.symm (a,g))) = _
    rw [← hb, e.apply_symm_apply]
  | inr p => rfl

theorem endpoints_atLane (layout : Bool) (z : PaddedId (V × Tag) (Id P.BaseMotif subdiv) pad) (g : L) :
    let i := atLane P subdiv layout z g
    let src := paddedSource (endpoint (P.roleBase layout) (sourceRole layout)) z
    let dst := paddedTarget (endpoint (P.roleBase layout) (targetRole layout)) (cycleTags tags) z
    let shift := paddedShift (P.roleDisplacement layout (sourceRole layout) (targetRole layout)) z
    actualEnd P subdiv tags layout false i = (src.1,src.2,g) ∧
      actualEnd P subdiv tags layout true i = (dst.1,dst.2,g+shift) := by
  cases z with
  | inl a => exact P.survivingLane_endpoints layout subdiv a g
  | inr p => exact ⟨rfl, by change (_, _, g) = (_, _, g+0); rw [add_zero]; rfl⟩

/-- Numeric order of the next graph's packed bases and their outgoing slots. -/
def baseIndex {degree : ℕ} : (V × Tag) × Fin degree ≃ Fin ((N*J)*degree) :=
  ((((vertices.prodCongr tags).trans finProdFinEquiv).prodCongr (Equiv.refl _))).trans finProdFinEquiv

private theorem divLow {n : ℕ} (x : Fin n) (h : ℕ) : (x.val+n*h)/n = h := by
  rw [Nat.add_mul_div_left _ _ ((Nat.zero_le x.val).trans_lt x.isLt), Nat.div_eq_of_lt x.isLt, Nat.zero_add]

private theorem modLow {n : ℕ} (x : Fin n) (h : ℕ) : (x.val+n*h)%n = x.val := by
  simp [Nat.mod_eq_of_lt x.isLt]

/-- Linear index of a packed base vertex, with its tag index as the low digit. -/
def packedCode (b : V × Tag) : Fin (N*J) := finProdFinEquiv (vertices b.1, tags b.2)

omit [AddCommGroup Tag] [AddCommGroup L] in
theorem site_val (b : V × Tag) (g : L) : (siteIndex vertices tags lanes (b.1,b.2,g)).val =
    (lanes g).val + nL*(packedCode vertices tags b).val := by
  change (lanes g).val + nL*(tags b.2).val + (J*nL)*(vertices b.1).val =
    (lanes g).val + nL*((tags b.2).val + J*(vertices b.1).val)
  ring

/-- Source rectangular slot at lane zero, computed from the base arc's
numeric index by quotient and remainder. -/
def laneZeroRow (degree laneCount i : ℕ) : ℕ := (i/degree)*laneCount*2*degree + i%degree

/-- Decode a packed incoming rectangular index into the base arc and lane. -/
def unpackBaseTarget (degree laneCount rect : ℕ) : ℕ × ℕ :=
  let site := rect / degree / 2
  (site/laneCount*degree + rect%degree, site%laneCount)

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L] [Module (ZMod 2) Tag]

/-- On each lane-zero source row, the adjacent inverse field supplies the
actual graph's target base-arc index and displacement. -/
theorem base_lookup {w rows inverse : ℕ} (hc : 2 ≤ c) (hφ : P.slots.ValidTagOffsets P.tagShift P.offset)
    (layout : Bool) {degree : ℕ} (hd : survivingDegree d c subdiv ≤ degree) (hJ : 1 < J)
    (hzero : (lanes 0).val = 0) (m : Memory w) (p : (V × Tag) × Fin degree)
    (hfields : RecordCount N J nL d c (degree-survivingDegree d c subdiv) subdiv * 2 ≤ 2^w)
    (hrect : (N*(J*nL)*2)*degree ≤ 2^w) :
    let := P.slotIdentifierOrder vertices tags subdiv
    let I := P.regularizedSlotIndexing hc hφ layout subdiv hd tags hJ
    let D := slotDirectory P subdiv vertices tags lanes layout (pad := degree-survivingDegree d c subdiv)
    let hD := fun b ↦ (slotDirectory_degree P subdiv vertices tags lanes hc layout b).trans (Nat.add_sub_of_le hd)
    let source := laneZeroRow degree nL (baseIndex vertices tags p).val
    let field := m (rows+source)
    let target := m (inverse+(field.val+1))
    Tables D degree rows inverse hD m → source < (N*(J*nL)*2)*degree ∧
      field.val+1 < RecordCount N J nL d c (degree-survivingDegree d c subdiv) subdiv * 2 ∧
      unpackBaseTarget degree nL target.val =
      ((baseIndex vertices tags (I.graph.base.target p)).val, (lanes (I.graph.displacement p)).val) := by
  intro order I D hD source field target tab
  let z := I.outgoing.symm p
  let i := atLane P subdiv layout z 0
  have hz : paddedBaseId P subdiv i = z := baseId_atLane P subdiv layout z 0
  have hsrc : I.outgoing z = p := I.outgoing.apply_symm_apply p
  have hdst : I.incoming z = I.graph.base.target p := (I.match_eq z).symm.trans (congrArg I.graph.base.target hsrc)
  have hshift := (I.displacement_eq z).symm.trans (congrArg I.graph.displacement hsrc)
  have hends := endpoints_atLane P subdiv tags layout z 0
  have hs : actualEnd P subdiv tags layout false i = (p.1.1,p.1.2,0) := by
    have h := (I.src_eq z).symm.trans (congrArg Prod.fst hsrc)
    exact hends.1.trans (congrArg (fun b : V×Tag ↦ (b.1,b.2,(0:L))) h)
  let t := I.graph.base.target p
  let g := I.graph.displacement p
  have ht : actualEnd P subdiv tags layout true i = (t.1.1,t.1.2,g) := by
    have h := (I.dst_eq z).symm.trans (congrArg Prod.fst hdst)
    rw [← h]; exact hends.2.trans (congrArg (fun l : L ↦ (_,_,l)) ((zero_add _).trans hshift))
  let q := siteIndex vertices tags lanes (t.1.1,t.1.2,g)
  have hout : (sortedFields D degree hD (i,0)).val = source := by
    have h := rectangular_slot P subdiv vertices tags lanes hc hφ layout hd hJ i 0
    change (sortedFields D degree hD (i,0)).val = (I.outgoing (paddedBaseId P subdiv i)).2.val +
      degree*(D.owner (i,0)).val at h
    rw [hz,hsrc] at h
    change (sortedFields D degree hD (i,0)).val = p.2.val + degree*(0+2*(siteIndex vertices tags lanes
      (actualEnd P subdiv tags layout false i)).val) at h
    rw [hs, site_val, hzero] at h
    change _ = laneZeroRow degree nL (p.2.val+degree*(packedCode vertices tags p.1).val)
    rw [h,laneZeroRow,divLow,modLow]; ring
  have hinc : (sortedFields D degree hD (i,1)).val = t.2.val+degree*(1+2*q.val) := by
    have h := rectangular_slot P subdiv vertices tags lanes hc hφ layout hd hJ i 1
    change (sortedFields D degree hD (i,1)).val = (I.incoming (paddedBaseId P subdiv i)).2.val +
      degree*(D.owner (i,1)).val at h
    rw [hz,hdst] at h
    change (sortedFields D degree hD (i,1)).val = t.2.val + degree*(1+2*(siteIndex vertices tags lanes
      (actualEnd P subdiv tags layout true i)).val) at h
    simpa only [ht] using h
  have hf : field.val = (D.address (i,0)).val := by
    change (m (rows+source)).val = _
    rw [← hout, tab.bySlot, Fin.val_ofNat, Nat.mod_eq_of_lt ((D.address (i,0)).isLt.trans_le hfields)]
  have hother : (D.address (i,0)).val+1 = (D.address (i,1)).val := by
    change 0 + 2*(arcAddress P subdiv vertices tags lanes _ i).val + 1 =
      1+2*(arcAddress P subdiv vertices tags lanes _ i).val
    omega
  have htarget : target.val = t.2.val+degree*(1+2*q.val) := by
    change (m (inverse+(field.val+1))).val = _
    rw [hf, hother, tab.byField, Fin.val_ofNat, Nat.mod_eq_of_lt ((sortedFields D degree hD (i,1)).isLt.trans_le hrect), hinc]
  have hq : q.val = (lanes g).val+nL*(packedCode vertices tags t.1).val := site_val vertices tags lanes t.1 g
  refine ⟨hout ▸ (sortedFields D degree hD (i,0)).isLt, by rw [hf,hother]; exact (D.address (i,1)).isLt, ?_⟩
  rw [htarget, unpackBaseTarget, divLow, modLow, show (1+2*q.val)/2=q.val from divLow (1 : Fin 2) q.val,
    hq, divLow, modLow]
  change ((packedCode vertices tags t.1).val * degree + t.2.val, _) =
    (t.2.val + degree*(packedCode vertices tags t.1).val, _)
  congr 1; ring

end CompressorRecords.SlotSchedule

end VPVNP
end Computability
end OAI
