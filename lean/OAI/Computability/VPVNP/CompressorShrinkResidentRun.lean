import OAI.Computability.VPVNP.CompressorShrinkResidentDirectory
import OAI.Computability.VPVNP.CompressorShrinkResidentsPlan

/-! # Native construction of both local resident tables in chronological memory -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkResidentRun

open Compression BurstRAM PrimedStackRAM PairSimulation.LocalHistory
open ShrinkResidentLayout
open scoped Fin.CommRing Classical

variable {a g w : ℕ} (X : State a (packingLaneBits a g)) (first : ℕ)
variable (absolute roleHead : Word w) (side : Bool)

/-- The owner scan takes four words in order, the dense-to-absolute motif table base, the role
table base, the selected side bit, and the output base for hidden or map owners. -/
def ownerBank (maps : Bool) : Fin 4 → Word w :=
  ![absolute,roleHead,(side.toNat : Word w),((layout X first).owner maps : Word w)]

/-- The preimage collector takes six words for the chosen resident kind, giving its size and
owner base, the packed-site count and counter base, the row capacity, and the ID row base. -/
def outputBank (maps : Bool) := (layout X first).params a maps w

/-- The resident arena and both input tables fit the address space, each input table lies
outside the arena, and six is representable as a word. -/
structure Areas : Prop where
  fit : (layout X first).endAddr < 2^w
  absoluteRoom : absolute.val+(shrinkMotifOrder X).length ≤ 2^w
  roleRoom : roleHead.val+4*DemandRAM.absoluteCount X ≤ 2^w
  absoluteApart : absolute.val+(shrinkMotifOrder X).length ≤ first ∨ (layout X first).endAddr ≤ absolute.val
  roleApart : roleHead.val+4*DemandRAM.absoluteCount X ≤ first ∨ (layout X first).endAddr ≤ roleHead.val
  tagFit : 6 < 2^w

variable {X first absolute roleHead} (space : Areas X first absolute roleHead)

include space in
theorem Areas.owner (maps : Bool) : ShrinkResidentDirectory.Areas X maps (ownerBank X first absolute roleHead side maps) := by
  let L := layout X first
  have dims : (ShrinkResidentDirectory.oldOrder X maps).length = L.size maps := rfl
  obtain ⟨start,cnt,rows,stop⟩ := L.ranges maps
  have fit : L.endAddr < 2^w := space.fit
  have word : (ownerBank X first absolute roleHead side maps 3).val = L.owner maps := Nat.mod_eq_of_lt (show L.owner maps < 2^w by omega)
  refine ⟨space.absoluteRoom,space.roleRoom,?_,?_,?_,space.tagFit⟩
  · rw [word,dims]; omega
  · rw [word,dims]; exact space.absoluteApart.imp (fun h => h.trans start) (fun h => (show L.owner maps+L.size maps ≤ L.endAddr by omega).trans h)
  · rw [word,dims]; exact space.roleApart.imp (fun h => h.trans start) (fun h => (show L.owner maps+L.size maps ≤ L.endAddr by omega).trans h)

/-- Reports from the three successive scans that build a directory of hidden residents or map
residents at the packed sites. -/
structure Passes (w : ℕ) where
  /-- Reports from writing the packed owner of each resident in motif-major order. -/
  owners : List (Report w)
  /-- Reports from setting each packed site’s resident counter to zero before collecting its
  IDs. -/
  clear : List (Report w)
  /-- Reports from appending each resident’s dense ID to its owner’s row and incrementing that
  site’s counter. -/
  collect : List (Report w)

/-- Memory after replaying the owner-column writes on the entry memory, ready for the
counter-clear scan. -/
def Passes.mid (p : Passes w) (m : Memory w) := after m (eventLog p.owners)
/-- Memory after the owner scan and the counter-clear scan, where the ID collection starts. -/
def Passes.cleared (p : Passes w) (m : Memory w) := after (p.mid m) (eventLog p.clear)
/-- Memory after collecting the resident IDs on top of the owner and counter scans. -/
def Passes.final (p : Passes w) (m : Memory w) := after (p.cleared m) (eventLog p.collect)
/-- The complete directory trace in execution order, from the owner writes through counter
clearing to ID collection. -/
def Passes.all (p : Passes w) := p.owners++p.clear++p.collect

theorem Passes.after_all (p : Passes w) (m : Memory w) : after m (eventLog p.all) = p.final m := by
  simp only [all,final,cleared,mid,eventLog,List.flatMap_append,after,List.foldl_append]

variable (X first absolute roleHead) (maps : Bool)

/-- Certifies the three native scans, their ordered per-site resident directory, and
preservation outside the resident tables. The total charge is nine per resident and two per
packed site. -/
structure Built (m : Memory w) (p : Passes w) : Prop where
  owners : ShrinkResidentDirectory.Written X maps (ownerBank X first absolute roleHead side maps) side m p.owners
  clear : runSegment ((template SliceRAM.clearOps 0).instantiate w (fun _ => outputBank X first maps 3)).program 8
    (some 0) (p.mid m) (List.replicate (layout X first).sites []) = some p.clear
  collect : runSegment ((template collectPreimage 3).instantiate w (outputBank X first maps)).program 23
    (some 0) (p.cleared m) (List.replicate ((layout X first).size maps) []) = some p.collect
  directory : ShrinkHistoryRows.Directory (ShrinkResidentDirectory.oldOrder X maps) (ShrinkHistoryRows.packedOrder X)
    (ShrinkResidentDirectory.place X maps side) (outputBank X first maps) (p.final m)
  frame (x : ℕ) (hx : x < (layout X first).owner maps ∨ (layout X first).rows maps+(layout X first).size maps ≤ x) :
    p.final m x = m x
  charge : RAMBuckets.cost Report.probes p.all = 9*(layout X first).size maps + 2*(layout X first).sites

private theorem clearCost (rs : List (Report w)) (h : ∀ r ∈ rs, r.probes = 1) :
    RAMBuckets.cost Report.probes rs = 2*rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [RAMBuckets.cost, h r (List.mem_cons_self ..), ih (fun _ hv => h _ (List.mem_cons_of_mem _ hv)), List.length_cons,Nat.mul_succ]
    omega

include space in
/-- Starting from actual CD and role data, this deterministic three-stage
scan gives precisely the ordered local hidden IDs or map IDs. -/
theorem run (mem : Memory w) (dir : ShrinkResidentDirectory.Absolute X absolute mem)
    (roles : DemandRAM.RoleColumns X side roleHead.val mem) :
    ∃ p : Passes w, Built X first absolute roleHead side maps mem p := by
  let L := layout X first
  let bank := outputBank (w := w) X first maps
  have ho : (ShrinkResidentDirectory.oldOrder X maps).length = L.size maps := rfl
  have hn : (ShrinkHistoryRows.packedOrder X).length = L.sites := rfl
  obtain ⟨areas,h0,h1,h2,h3,h4,h5⟩ := ShrinkResidentLayout.frame X first maps space.fit
  change (bank 0).val=L.size maps at h0
  change (bank 1).val=L.owner maps at h1
  change (bank 2).val=L.sites at h2
  change (bank 3).val=L.counts maps at h3
  change (bank 4).val=rowCapacity a maps at h4
  change (bank 5).val=L.rows maps at h5
  have newFit : (ShrinkHistoryRows.packedOrder X).length ≤ 2^w := (h2 ▸ (bank 2).isLt).le
  have allowed := space.owner side maps
  obtain ⟨own,hw⟩ := ShrinkResidentDirectory.run X maps (ownerBank X first absolute roleHead side maps) rfl allowed newFit dir roles
  have cap (v) : Fintype.card {x // ShrinkResidentDirectory.place X maps side x = v} ≤ (bank 4).val := by
    exact (show Fintype.card {x // ShrinkResidentDirectory.place X maps side x = v} ≤ rowCapacity a maps from by
      cases maps
      · exact (ShrinkHistoryRows.hidden_count X side v).le
      · exact (ShrinkHistoryRows.map_count X side v).le).trans h4.symm.le
  obtain ⟨cs,rs,hc,hr,rows,clen,rlen,cwork,rwork,rf⟩ := ShrinkHistoryRows.build
    (ShrinkResidentDirectory.oldOrder X maps) (ShrinkHistoryRows.packedOrder X)
    (ShrinkResidentDirectory.place X maps side) bank areas h0 h2 cap (after mem (eventLog own))
    (hw.ownerAt X maps (ownerBank X first absolute roleHead side maps) allowed bank rfl h0)
  let pass : Passes w := ⟨own,cs,rs⟩
  refine ⟨pass,hw,hc,hr,rows,?_,?_⟩
  · intro x hx
    obtain ⟨_,oc,cr,_⟩ := L.ranges maps
    have ss := size_eq_rows X first maps
    change L.size maps=L.sites*rowCapacity a maps at ss
    have other : OutsidePreimageWrites bank x := by
      change (x < (bank 3).val ∨ (bank 3).val+(bank 2).val ≤ x) ∧
        (x < (bank 5).val ∨ (bank 5).val+(bank 2).val*(bank 4).val ≤ x)
      rw [h3,h2,h5,h4,←ss]
      change x < L.owner maps ∨ L.rows maps+L.size maps ≤ x at hx
      omega
    have wo : (ownerBank X first absolute roleHead side maps 3).val = L.owner maps := h1
    apply (rf x other).trans (hw.frame x ?_)
    rw [wo,ho]
    change x < L.owner maps ∨ L.rows maps+L.size maps ≤ x at hx
    omega
  · change RAMBuckets.cost Report.probes ((own++cs)++rs) = _
    have rc : RAMBuckets.cost Report.probes rs = 5*rs.length := preimagePass_cost (fun r h => (rwork r h).1)
    rw [RAMBuckets.cost_append,RAMBuckets.cost_append,hw.charge,clearCost cs (fun r h => (cwork r h).1),rc,clen,rlen,ho,hn]
    change 4*L.size maps+2*L.sites+5*L.size maps = 9*L.size maps+2*L.sites
    omega

/-- The entire resident workspace is disjoint from the two persistent
input arrays. A finished stage therefore leaves their typed readbacks live
for the next stage. -/
theorem Built.inputs {m : Memory w} {r : Passes w} (h : Built X first absolute roleHead side maps m r)
    (dir : ShrinkResidentDirectory.Absolute X absolute m) (roles : DemandRAM.RoleColumns X side roleHead.val m)
    (sp : Areas X first absolute roleHead) :
    ShrinkResidentDirectory.Absolute X absolute (r.final m) ∧
      DemandRAM.RoleColumns X side roleHead.val (r.final m) := by
  let L := layout X first
  obtain ⟨before,_,_,endBound⟩ := L.ranges maps
  have same (x : ℕ) (hx : x < first ∨ L.endAddr ≤ x) : r.final m x = m x :=
    h.frame x (hx.imp (fun lo => lo.trans_le before) (fun hi => endBound.trans hi))
  have absSafe {i : ℕ} (hi : i < (shrinkMotifOrder X).length) :
      absolute.val+i < first ∨ L.endAddr ≤ absolute.val+i :=
    sp.absoluteApart.imp (fun ha => (Nat.add_lt_add_left hi _).trans_le ha) (fun ha => ha.trans (Nat.le_add_right ..))
  have roleSafe {i j : ℕ} (hi : i<DemandRAM.absoluteCount X) (hj : j<4) :
      roleHead.val+4*i+j < first ∨ L.endAddr ≤ roleHead.val+4*i+j :=
    sp.roleApart.imp (fun ha => (show _ < roleHead.val+4*DemandRAM.absoluteCount X by omega).trans_le ha)
      (fun ha => (ha.trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..))
  constructor
  · intro i
    have hc := Fintype.card_congr (ShrinkMotifOrder.stateNumber X)
    rw [Fintype.card_fin] at hc
    have hi : i.val < (shrinkMotifOrder X).length := i.isLt.trans_eq hc.symm
    rw [same _ (absSafe hi)]
    exact dir i
  · constructor
    · intro e
      rw [same _ (roleSafe (DemandRAM.absoluteIndex X e).isLt (by decide : 3<4))]
      exact roles.cd e
    · intro e role
      have small : SlotOwners.roleOffset role < 4 := by cases role <;> decide
      rw [same _ (roleSafe (DemandRAM.absoluteIndex X e.val).isLt small)]
      exact roles.packed e role

private theorem hidden_length_le (v) : (ShrinkHistoryRows.residents (ShrinkHistoryRows.hiddenOrder X)
    (X.packingData.shrinkInternalOwner side) v).length ≤ rowCapacity a false := by
  let f := X.packingData.shrinkInternalOwner side
  have changeFiber : {u // v=f u} ≃ {u // f u=v} := Equiv.subtypeEquivRight fun _ => eq_comm
  exact (Fintype.card_congr changeFiber).le.trans (ShrinkHistoryRows.hidden_count X side v).le

/-- The later map-directory calls retain both the earlier hidden counts
and every earlier hidden ID. -/
theorem retained_hidden {m : Memory w} {h r : Passes w}
    (hb : Built X first absolute roleHead side false m h)
    (rb : Built X first absolute roleHead side true (h.final m) r)
    (fit : (layout X first).endAddr < 2^w) :
    ShrinkHistoryRows.Directory (ShrinkHistoryRows.hiddenOrder X) (ShrinkHistoryRows.packedOrder X)
      (X.packingData.shrinkInternalOwner side) (outputBank X first false) (r.final (h.final m)) := by
  let L := layout X first
  let p := outputBank (w := w) X first false
  obtain ⟨_,_,_,hSites,hCount,hCap,hRow⟩ := ShrinkResidentLayout.frame X first false fit
  change (p 2).val=L.sites at hSites
  change (p 3).val=L.counts false at hCount
  change (p 4).val=rowCapacity a false at hCap
  change (p 5).val=L.rows false at hRow
  have order (v) : ((ShrinkHistoryRows.packedOrder X).entries.symm v).val < L.sites :=
    ((ShrinkHistoryRows.packedOrder X).entries.symm v).isLt
  have next : L.owner true = L.rows false+L.size false := rfl
  constructor
  · intro v
    have addr : (p 3).val+((ShrinkHistoryRows.packedOrder X).entries.symm v).val < L.owner true := by
      rw [hCount,next]
      have := order v
      change L.counts false+_ < L.counts false+L.sites+L.size false
      omega
    rw [rb.frame _ (.inl addr)]
    exact hb.directory.count v
  · intro v j
    have vv := Nat.mul_le_mul_right (rowCapacity a false) (order v)
    rw [Nat.succ_mul] at vv
    have hv := j.isLt.trans_le (hidden_length_le X side v)
    have dim := size_eq_rows X first false
    change L.size false=L.sites*rowCapacity a false at dim
    have addr : (p 5).val+((ShrinkHistoryRows.packedOrder X).entries.symm v).val*(p 4).val+j.val < L.owner true := by
      rw [hRow,hCap,next,dim]
      omega
    rw [rb.frame _ (.inl addr)]
    exact hb.directory.idAt v j

include space in
/-- Six deterministic native visits execute on the same memory image
as the two resident headers describe. No guessed bits are used to recover
the resident lists. -/
theorem both (m : Memory w) (dir : ShrinkResidentDirectory.Absolute X absolute m)
    (roles : DemandRAM.RoleColumns X side roleHead.val m) :
    ∃ h r : Passes w, Built X first absolute roleHead side false m h ∧
      Built X first absolute roleHead side true (h.final m) r ∧
      ShrinkHistoryRows.Directory (ShrinkHistoryRows.hiddenOrder X) (ShrinkHistoryRows.packedOrder X)
        (X.packingData.shrinkInternalOwner side) (outputBank X first false) (r.final (h.final m)) ∧
      RAMBuckets.cost Report.probes (h.all++r.all) = 90*(layout X first).motifs+4*(layout X first).sites := by
  obtain ⟨h,hh⟩ := run X first absolute roleHead side space false m dir roles
  obtain ⟨dir',roles'⟩ := hh.inputs X first absolute roleHead side false dir roles space
  obtain ⟨r,hr⟩ := run X first absolute roleHead side space true (h.final m) dir' roles'
  refine ⟨h,r,hh,hr,retained_hidden X first absolute roleHead side hh hr space.fit,?_⟩
  rw [RAMBuckets.cost_append,hh.charge,hr.charge]
  change 9*((layout X first).motifs*4)+2*(layout X first).sites +
    (9*((layout X first).motifs*6)+2*(layout X first).sites) = _
  omega

end CompressorRecords.ShrinkResidentRun

end

end VPVNP
end Computability
end OAI
