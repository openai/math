import OAI.Computability.VPVNP.CompressorSlotState
import OAI.Computability.VPVNP.CompressorRecordsDemandOutput
import OAI.Computability.VPVNP.CompressorSlotOwnerAux
import OAI.Computability.VPVNP.CompressorRecordsBlockPlanner
import OAI.Computability.VPVNP.CompressorSlicePreparation
import OAI.Computability.VPVNP.CompressorSlotPhaseCosts
import OAI.Computability.VPVNP.CompressorSlotWidth

/-!
# Preparing the input tables for the selected slot directory

Four independent one-call phases publish the subdivision lengths. The following
scans write the selected roles, compute the cyclic site successor and clear every
append counter. The old arc and split-width rows precede the newly allocated
tables and survive all seven phases.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlots.Preparation

open Compression Compression.PackingData SlotOwners SlotLevel Slots
open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

private abbrev word (i : ℕ) : Word w := Fin.ofNat _ i

/-- Public address and value words for writing one of the four subdivision counts to its
designated cell. -/
def publishBank (base : ℕ) (values : Fin 4 → ℕ) (w : ℕ) (i : Fin 4) : Fin 2 → Word w :=
  ![word (base+i.val), word (values i)]

/-- The single-call report that writes one subdivision count and returns cursor one. -/
def published (base : ℕ) (values : Fin 4 → ℕ) (w : ℕ) (i : Fin 4) : Report w :=
  ⟨[.tick,.tick,.tick,.write (word (base+i.val)) (word (values i)),.tick,.tick], some 1⟩

/-- The four one-call phases restart their local cursor and publish one value each. -/
theorem publish_run (base : ℕ) (values : Fin 4 → ℕ) (mem : Memory w) (i : Fin 4) :
    let P := ((BlockPlanner.publish (.lit (base+i.val)) (.lit (values i))).worker.table.instantiate
      w (publishBank base values w i)).program
    runSegment P 7 (some 0) mem [[]] = some [published base values w i] := by
  intro P
  have he := (BlockPlanner.publish_native (.lit (base+i.val)) (.lit (values i))
    (publishBank base values w i) 0 mem).1
  change execute P 7 (P.start 0) mem [] = some ⟨_,some (0+1)⟩ at he
  simp only [runSegment,he,Option.map_some,List.cons.injEq,Option.some.injEq,and_true]
  simp only [zero_add]
  rfl

private theorem published_after (base : ℕ) (values : Fin 4 → ℕ) (mem : Memory w)
    (fit : base+4 ≤ 2^w) (addr : ℕ) :
    let final := after mem (eventLog (List.ofFn (published base values w)))
    (∀ i : Fin 4, addr = base+i.val → final addr = word (values i)) ∧
      (addr < base ∨ base+4 ≤ addr → final addr = mem addr) := by
  have val (i : Fin 4) : (word (w := w) (base+i.val)).val = base+i.val :=
    Nat.mod_eq_of_lt (by have := i.isLt; omega)
  let update (m : Memory w) (i : Fin 4) := writeMemory m (word (base+i.val)) (word (values i))
  change (∀ i : Fin 4, addr = base+i.val →
    update (update (update (update mem 0) 1) 2) 3 addr = _) ∧
    (addr < base ∨ base+4 ≤ addr → update (update (update (update mem 0) 1) 2) 3 addr = _)
  simp only [update,writeMemory]
  rw [val 3,val 2,val 1,val 0]
  simp only [Fin.val_zero, show (1 : Fin 4).val = 1 by rfl,
    show (2 : Fin 4).val = 2 by rfl, show (3 : Fin 4).val = 3 by rfl]
  constructor
  · rintro i rfl
    fin_cases i <;> simp +arith
  · intro ha
    repeat rw [ite_eq_right (by omega)]

/-- Public layout bit and destination table base for computing the endpoint roles of the four
edge types. -/
def roleBank (h : Heads) (l : Bool) (w : ℕ) : Fin 2 → Word w := ![word l.toNat,word h.role]

/-- Public lane count, tag count, and destination base for writing the cyclic tag successor of
every packed site. -/
def cyclicBank (s : Shape) (h : Heads) (w : ℕ) : Fin 3 → Word w := ![word s.lanes,word s.tags,word h.nextSite]

/-- Reports for the seven input preparation phases, covering four subdivision writes and three
subsequent scans. -/
structure Reports (w : ℕ) where
  /-- One native write report for each of the four subdivision counts. -/
  publish : Fin 4 → Report w
  /-- Reports that populate the eight endpoint role entries for the chosen layout. -/
  roles : List (Report w)
  /-- Reports that write the site reached by advancing the tag at each packed site. -/
  cyclic : List (Report w)
  /-- Reports that zero the append counters for the real endpoint owners and the reserved hole
  owners. -/
  clear : List (Report w)

/-- Preparation reports in order of execution, from the four subdivision writes through the
counter clear. -/
def Reports.all (r : Reports w) := List.ofFn r.publish ++ r.roles ++ r.cyclic ++ r.clear

/-- Memory after applying all input preparation reports in order. -/
def Reports.final (r : Reports w) (mem : Memory w) := after mem (eventLog r.all)

/-- All public banks, per-phase fuel and reset cursors, in the planner's visit order. -/
def Reports.Native (r : Reports w) (s : Shape) (h : Heads) (layout : Bool) (mem : Memory w) : Prop :=
  let ps := List.ofFn r.publish
  let m₁ := after mem (eventLog ps)
  let m₂ := after m₁ (eventLog r.roles)
  let m₃ := after m₂ (eventLog r.cyclic)
  (∀ i : Fin 4,
      let P := ((BlockPlanner.publish (.lit (h.subdivisions+i.val)) (.lit (s.subdivisions i))).worker.table.instantiate
        w (publishBank h.subdivisions s.subdivisions w i)).program
      runSegment P 7 (some 0) (after mem (eventLog (ps.take i.val))) [[]] = some [r.publish i]) ∧
    runSegment ((template Aux.roleCode 0).instantiate w (roleBank h layout w)).program 26 (some 0) m₁
      (List.replicate 8 []) = some r.roles ∧
    runSegment ((template Aux.nextCode 0).instantiate w (cyclicBank s h w)).program 19 (some 0) m₂
      (List.replicate (sites s) []) = some r.cyclic ∧
    runSegment ((template SliceRAM.clearOps 0).instantiate w (fun _ ↦ word (h.scratch+fields s))).program 8
      (some 0) m₃ (List.replicate (owners s+fields s) []) = some r.clear

/-- The four publishers return cursor one, and the role, successor, and clear scans return
their respective row counts. -/
def Reports.Cursors (r : Reports w) (s : Shape) : Prop :=
  (∀ i, endState (some 0) [r.publish i] = some 1) ∧
    endState (some 0) r.roles = some 8 ∧ endState (some 0) r.cyclic = some (word (sites s)) ∧
    endState (some 0) r.clear = some (word (owners s+fields s))

/-- Calls, calls plus external probes, total dispatched instructions, and the
per-call instruction bound for the entire seven-phase preparation program. -/
theorem Reports.Native.resources {r : Reports w} {s : Shape} {h : Heads} {layout : Bool}
    {mem : Memory w} (native : r.Native s h layout mem) :
    let n := owners s+fields s
    r.all.length = 12+sites s+n ∧
      RAMBuckets.cost Report.probes r.all = 24+2*sites s+2*n ∧
      (r.all.map (fun rep ↦ rep.events.length+1)).sum = 236+19*sites s+8*n ∧
      ∀ rep ∈ r.all, rep.events.length+1 ≤ 26 := by
  intro n
  obtain ⟨hpub,hr,hn,hc⟩ := native
  have same : r.publish = published h.subdivisions s.subdivisions w := by
    funext i
    have h := (hpub i).symm.trans (publish_run h.subdivisions s.subdivisions
      (after mem (eventLog ((List.ofFn r.publish).take i.val))) i)
    exact List.cons.inj (Option.some.inj h) |>.1
  have role := PhaseCosts.fixedScanCounts (probes := 1) (ticks := 25) _
    (Aux.role_native (roleBank h layout w)) (fun _ _ ↦ ⟨rfl,rfl⟩) hr
  have cyclic := PhaseCosts.fixedScanCounts (probes := 1) (ticks := 18) _
    (Aux.next_native (cyclicBank s h w)) (fun _ _ ↦ ⟨rfl,rfl⟩) hn
  have clear := PhaseCosts.fixedScanCounts (probes := 1) (ticks := 7) _
    (fun m i ↦ SliceRAM.clearVisit_native (word (h.scratch+fields s)) i m) (fun _ _ ↦ ⟨rfl,rfl⟩) hc
  let ps := List.ofFn (published h.subdivisions s.subdivisions w)
  have pl : ps.length = 4 := rfl
  change r.all.length = _ ∧ _ ∧ _ ∧ _
  rw [Reports.all,same]
  change (ps++r.roles++r.cyclic++r.clear).length = _ ∧ _ ∧ _ ∧ _
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.length_append,pl,role.1,cyclic.1,clear.1]; rfl
  · simp only [RAMBuckets.cost_append,role.2.1,cyclic.2.1,clear.2.1]; rfl
  · simp only [List.map_append,List.sum_append,role.2.2.1,cyclic.2.2.1,clear.2.2.1]; rfl
  · intro rep hx
    simp only [List.mem_append] at hx
    rcases hx with ((hp|hr)|hn)|hc
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
      exact (by decide : 6+1 ≤ 26)
    · rw [role.2.2.2 rep hr]
    · rw [cyclic.2.2.2 rep hn]; decide
    · rw [clear.2.2.2 rep hc]; decide

private theorem cost_one (rs : List (Report w)) (hp : ∀ r ∈ rs, r.probes = 1) :
    RAMBuckets.cost Report.probes rs = 2*rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [RAMBuckets.cost,hp r (by simp),ih (fun q hq ↦ hp q (by simp [hq])),List.length_cons,Nat.mul_succ]
    omega

variable {a b g : ℕ} (X : State a (packingLaneBits a g))

/-- Preservation of both previously materialized slot inputs under the
preparation program's frame, including every selected split-width cell. -/
theorem preserve_rows (h : Heads) (layout : Bool) (splitHead : ℕ)
    (width : X.packingData.Motif → Fin 4 → ℕ) (mem out : Memory w) :
    let s := levelShape (b := b) X
    let split := SlotWidthScan.SplitRows X.packingData s.subdivisions X.baseIndex
      (bitWordFinEquiv (Shrink.J a)) (bitWordFinEquiv g) width splitHead
    h.oldArc+4*DemandRAM.absoluteCount X ≤ h.role →
    splitHead+DemandRAM.absoluteCount X*4*(∑ t,s.subdivisions t) ≤ h.role →
    (∀ addr < h.role, out addr = mem addr) →
    DemandRAM.RoleColumns X layout h.oldArc mem → split mem →
    DemandRAM.RoleColumns X layout h.oldArc out ∧ split out := by
  intro s split oldRoom splitRoom frame cols widths
  refine ⟨⟨?_,?_⟩, SlotWidthScan.SplitRows.congr_below _ _ _ _ _ widths splitRoom frame⟩
  · intro e
    have he : (DemandRAM.absoluteIndex X e).val < DemandRAM.absoluteCount X := (DemandRAM.absoluteIndex X e).isLt
    rw [frame _ (by omega),cols.cd]
  · intro e u
    have he : (DemandRAM.absoluteIndex X e.val).val < DemandRAM.absoluteCount X := (DemandRAM.absoluteIndex X e.val).isLt
    have hu : roleOffset u < 3 := by cases u <;> decide
    rw [frame _ (by omega),cols.packed]

/-- The prepared memory supplies both owner workers and all zero append counters.
Every external cell before the role table or beyond the counters retains its
initial value. The older split-width rows can therefore use the same frame. -/
theorem run (h : Heads) (layout : Bool) (mem : Memory w) :
    let s := levelShape (b := b) X
    let tags := bitWordFinEquiv (Shrink.J a)
    let lanes := bitWordFinEquiv g
    DemandRAM.RoleColumns X layout h.oldArc mem →
    h.oldArc+4*DemandRAM.absoluteCount X ≤ h.role → h.role+8 ≤ h.nextSite →
    h.nextSite+sites s ≤ h.subdivisions → h.subdivisions+4 ≤ h.scratch → rowsHead s h < 2^w →
    s.lanes < 2^w → s.tags < 2^w → (∑ t,s.subdivisions t) < 2^w → s.newDegree < 2^w →
    ∃ r : Reports w, r.Native s h layout mem ∧ r.Cursors s ∧
      GenuineTables X.packingData s.subdivisions X.baseIndex tags lanes layout (bank s h w .genuineOwners) (r.final mem) ∧
      DummyTables X.baseIndex tags lanes (pad s) (bank s h w .dummyOwners) (r.final mem) ∧
      (∀ u : Word w, u.val < owners s+fields s → r.final mem (h.scratch+fields s+u.val) = 0) ∧
      (∀ addr, addr < h.role ∨ rowsHead s h ≤ addr → r.final mem addr = mem addr) ∧
      RAMBuckets.cost Report.probes r.all = 24+2*sites s+2*(owners s+fields s) := by
  intro s tags lanes cols oldRoom roleRoom nextRoom subRoom fit laneFit tagFit sumFit degreeFit
  let cnt := owners s+fields s
  let start := h.scratch+fields s
  have room : start+cnt < 2^w := fit
  let p := published h.subdivisions s.subdivisions w
  let m₁ := after mem (eventLog (List.ofFn p))
  let rb := roleBank h layout w
  let cb := cyclicBank s h w
  let gb := bank s h w .genuineOwners
  let db := bank s h w .dummyOwners
  have oldSize : DemandRAM.absoluteCount X = oldBaseArcCount s.bases s.tags s.oldDegree s.colors * s.lanes := rfl
  have lanePos : 0 < s.lanes := Nat.two_pow_pos _
  have baseLe := Nat.le_mul_of_pos_right (oldBaseArcCount s.bases s.tags s.oldDegree s.colors) lanePos
  rw [← oldSize] at baseLe
  have scratchLe : h.scratch ≤ start := Nat.le_add_right ..
  have roleVal : (rb 1).val = h.role := Nat.mod_eq_of_lt (by omega : h.role < 2^w)
  have nextVal : (cb 2).val = h.nextSite := Nat.mod_eq_of_lt (by omega : h.nextSite < 2^w)
  have subVal : (gb 5).val = h.subdivisions := Nat.mod_eq_of_lt (by omega : h.subdivisions < 2^w)
  have oldVal : (gb 3).val = h.oldArc := Nat.mod_eq_of_lt (by omega : h.oldArc < 2^w)
  have clrVal : (word (w := w) start).val = start := Nat.mod_eq_of_lt (by omega)
  obtain ⟨rs,roleRun,roleData⟩ := Aux.roles_run layout rb m₁ rfl (by rw [roleVal]; omega)
  let m₂ := after m₁ (eventLog rs)
  have padFit : pad s < 2^w := (Nat.sub_le ..).trans_lt degreeFit
  obtain ⟨ns,nextRun,nextData⟩ := Aux.next_run X.baseIndex tags lanes cb db m₂
    (Nat.mod_eq_of_lt laneFit) (Nat.mod_eq_of_lt tagFit) (pad s) (Nat.mod_eq_of_lt padFit)
    rfl (by omega) (by rw [nextVal]; change h.nextSite+sites s ≤ _; omega)
  let m₃ := after m₂ (eventLog ns)
  obtain ⟨cs,clearRun,clearData,clearFrame,clearCursor,clearLength,clearWork⟩ :=
    SliceRAM.clearPass_run (word start) cnt (by rw [clrVal]; omega) (by omega) m₃
  rw [clrVal] at clearData clearFrame
  let r : Reports w := ⟨p,rs,ns,cs⟩
  have final : r.final mem = after m₃ (eventLog cs) := by
    simp only [r,Reports.final,Reports.all,eventLog,List.flatMap_append,after,List.foldl_append,m₃,m₂,m₁]
  have roleFrame (x : ℕ) (hx : x < h.role ∨ h.role+8 ≤ x) : m₂ x = m₁ x :=
    roleRun.frame x (roleVal ▸ hx)
  have nextFrame (x : ℕ) (hx : x < h.nextSite ∨ h.nextSite+sites s ≤ x) : m₃ x = m₂ x :=
    nextRun.frame x (nextVal ▸ hx)
  have finalFrame (x : ℕ) (hx : x < h.role ∨ rowsHead s h ≤ x) : r.final mem x = mem x := by
    change x < h.role ∨ start+cnt ≤ x at hx
    rw [final,clearFrame x (by omega),nextFrame x (by omega),roleFrame x (by omega)]
    exact (published_after _ _ mem (by omega) x).2 (by omega)
  have roles : (gb 4).val = h.role := roleVal
  have dummyHead : (db 1).val = h.nextSite := nextVal
  refine ⟨r, ⟨fun i ↦ publish_run _ _ _ i,roleRun.executed,nextRun.executed,clearRun⟩,
    ⟨fun _ ↦ rfl,roleRun.cursor,nextRun.cursor,clearCursor⟩, ?_, ?_, ?_, finalFrame, ?_⟩
  · refine ⟨Nat.mod_eq_of_lt laneFit,Nat.mod_eq_of_lt sumFit,
      Nat.mod_eq_of_lt (show oldBaseArcCount s.bases s.tags s.oldDegree s.colors < 2^w by omega),
      Nat.mod_eq_of_lt (show owners s < 2^w by dsimp only [cnt] at room; omega),
      by rw [oldVal,← oldSize]; omega, by rw [roles]; omega, by rw [subVal]; omega, ?_, ?_, ?_, ?_⟩
    · intro t u
      have idx : 2*t.val+u.val < 8 := by have := t.isLt; have := u.isLt; omega
      rw [roles,final,clearFrame _ (by omega),nextFrame _ (by omega),← roleVal]
      exact roleData t u
    · intro t
      have ht := t.isLt
      rw [subVal,final,clearFrame _ (by omega),nextFrame _ (by omega),roleFrame _ (by omega)]
      have cell : m₁ (h.subdivisions+t.val) = word (s.subdivisions t) :=
        (published_after h.subdivisions s.subdivisions mem (by omega) _).1 t rfl
      rw [cell]
      exact Nat.mod_eq_of_lt ((Finset.single_le_sum (fun i _ ↦ Nat.zero_le (s.subdivisions i))
        (Finset.mem_univ t)).trans_lt sumFit)
    · intro e
      have he : (DemandRAM.absoluteIndex X e).val < DemandRAM.absoluteCount X := (DemandRAM.absoluteIndex X e).isLt
      rw [oldVal]
      change (r.final mem (h.oldArc+4*(DemandRAM.absoluteIndex X e).val+3)).val = _
      rw [finalFrame _ (.inl (by omega))]
      exact cols.cd e
    · intro e u
      have he : (DemandRAM.absoluteIndex X e.val).val < DemandRAM.absoluteCount X := (DemandRAM.absoluteIndex X e.val).isLt
      have hu : roleOffset u < 3 := by cases u <;> decide
      rw [oldVal]
      change (r.final mem (h.oldArc+4*(DemandRAM.absoluteIndex X e.val).val+roleOffset u)).val = _
      rw [finalFrame _ (.inl (by omega))]
      exact cols.packed e u
  · refine ⟨nextData.twoFits,nextData.padCount,nextData.nextFits,?_⟩
    intro i
    have hi : i.val < sites s := i.isLt
    rw [final,clearFrame _ (.inl (by rw [dummyHead]; omega))]
    exact nextData.nextSite i
  · intro u hu
    rw [final]
    exact clearData _ (by omega) (by change u.val < cnt at hu; omega)
  · have pc : RAMBuckets.cost Report.probes (List.ofFn p) = 8 := by
      rw [cost_one _ (by intro rep hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; rfl),List.length_ofFn]
    have cc := cost_one cs (fun rep hr ↦ (clearWork rep hr).1)
    rw [clearLength] at cc
    simp only [r,Reports.all,RAMBuckets.cost_append,pc,roleRun.cost,nextRun.cost,cc]
    rfl

end CompressorRecords.ShrinkSlots.Preparation

end VPVNP
end Computability
end OAI
