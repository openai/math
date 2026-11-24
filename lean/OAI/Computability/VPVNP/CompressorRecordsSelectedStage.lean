import OAI.Computability.VPVNP.CompressorRecordsSelectedArenaDemand
import OAI.Computability.VPVNP.CompressorRecordsSelectedScoreRun

/-!
# Chronological layout, position and demand-record passes

After the selected motif records have been written, compare their two layout
scores. Use the resulting memory word as the placement scan's operand, then use
the newly written positions and the original incidence table to materialize the
absolute A/B/D/CD directory. The three groups of calls occupy consecutive,
disjoint workspace intervals.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SelectedStage

open Compression BurstRAM BurstRAM.PrivateRAM PrimedStackRAM ShrinkMotif
open SelectedArena
open scoped Fin.CommRing Classical

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {a g w : ℕ} (X : State a (packingLaneBits a g))
variable (term stride selectors : Word w) (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w)

private theorem address_lt (base : Word w) {endAt n j : ℕ} (h : base.val+n ≤ endAt) (hj : j<n) :
    (base+ShrinkRAM.word w j).val < endAt := by
  rw [Fin.val_add]
  apply (Nat.mod_le ..).trans_lt
  have hmod : (ShrinkRAM.word w j).val ≤ j := Nat.mod_le ..
  omega

private theorem port_lt (v : X.Base) (i : Fin (2^a)) :
    Shrink.join a (X.baseIndex v).val i.val < Fintype.card X.Base*2^a := by
  have bound := Nat.mul_le_mul_right (2^a) (X.baseIndex v).isLt
  rw [Nat.succ_mul] at bound
  unfold Shrink.join
  have := i.isLt
  omega

private theorem carry_directory (b : Word w) {m m' : Memory w}
    (old : OldInputs X term stride p₀ T) (same : ∀ j, j<origin X term stride → m' j=m j)
    (dir : Shrink.Directory X.slots X.baseIndex (ShrinkRAM.column p₀ m 6) (ShrinkRAM.column p₀ m 7)
      (ShrinkRAM.column p₀ m 8) (ShrinkRAM.column p₀ m 9)) :
    let p := shrinkWords X term stride p₀ b
    Shrink.Directory X.slots X.baseIndex (ShrinkRAM.column p m' 6) (ShrinkRAM.column p m' 7)
      (ShrinkRAM.column p m' 8) (ShrinkRAM.column p m' 9) := by
  constructor
  · intro v
    change (m' (p₀ 6+ShrinkRAM.word w (X.baseIndex v).val).val).val = _
    rw [same _ (address_lt _ old.color (X.baseIndex v).isLt)]
    exact dir.color_at v
  · intro v
    change (m' (p₀ 7+ShrinkRAM.word w (X.baseIndex v).val).val).val = _
    rw [same _ (address_lt _ old.offset (X.baseIndex v).isLt)]
    exact dir.offset_at v
  · intro v i
    change (m' (p₀ 8+ShrinkRAM.word w (Shrink.join a (X.baseIndex v).val i.val)).val).val = _
    rw [same _ (address_lt _ old.mate (port_lt X v i))]
    exact dir.mate_at v i
  · intro v i
    change (m' (p₀ 9+ShrinkRAM.word w (Shrink.join a (X.baseIndex v).val i.val)).val).val = _
    rw [same _ (address_lt _ old.displacement (port_lt X v i))]
    exact dir.shift_at v i

private theorem carry_actual {m m' : Memory w} {bound : ℕ}
    (hO : T.actualOut.val+DemandRAM.oldCount X ≤ bound) (hI : T.actualIn.val+DemandRAM.oldCount X ≤ bound)
    (hW : T.width.val+DemandRAM.oldCount X ≤ bound)
    (same : ∀ j, j<bound → m' j=m j) (inc : T.ActualColumns X m) : T.ActualColumns X m' := by
  have addr (b : Word w) (hb : b.val+DemandRAM.oldCount X ≤ bound) (e) :
      (b+IncidenceDirectory.actualPort X e).val < bound := by
    rw [IncidenceDirectory.actualPort_number]
    exact address_lt b hb (IncidenceDirectory.actualOrder X e).isLt
  exact ⟨fun e => (same _ (addr _ hO e)).trans (inc.actualOut e),
    fun e => (same _ (addr _ hI e)).trans (inc.actualIn e),
    fun e => (same _ (addr _ hW e)).trans (inc.width e)⟩

/-- Report groups in actual execution order. -/
structure Passes (w : ℕ) where
  /-- The reports that accumulate the two layout scores and compare them to select a layout. -/
  scores : List (Report w)
  /-- The reports of placing old sites using the layout selected by the preceding score
  comparison. -/
  positions : List (Report w)
  /-- The reports that construct absolute A, B, D, and CD demand records from the selected
  placement and old incidence. -/
  roles : List (Report w)

/-- The memory containing the completed score accumulators and layout selection. -/
def Passes.afterScores (p : Passes w) (m : Memory w) := after m (eventLog p.scores)
/-- The memory handed to the role scan after writing the selected old-site placements. -/
def Passes.afterPositions (p : Passes w) (m : Memory w) := after (p.afterScores m) (eventLog p.positions)
/-- The memory after scoring, site placement, and absolute role construction in chronological
order. -/
def Passes.final (p : Passes w) (m : Memory w) := after (p.afterPositions m) (eventLog p.roles)
/-- Concatenate the score, position, and role reports in their execution order. -/
def Passes.all (p : Passes w) := (p.scores++p.positions)++p.roles

theorem Passes.all_after (p : Passes w) (m : Memory w) : after m (eventLog p.all) = p.final m := by
  simp only [Passes.all,Passes.final,Passes.afterPositions,Passes.afterScores,eventLog,List.flatMap_append,
    after,List.foldl_append]

/-- The score writes, old-position scan, and final old-arc scan all run in this same memory. -/
structure Execution (mem : Memory w) (p : Passes w) : Prop where
  scores : TermScores.run (scoreTables X term stride selectors) (motifs X)
      (List.ofFn SelectedScore.axes) mem = some p.scores
  positions : let pub := selectedWords X term stride p₀ (p.afterScores mem)
    let M := (template ShrinkRAM.visit 0).instantiate w pub
    runSegment M.program 65 (some 0) (p.afterScores mem) (List.replicate (SelectedArena.positions X) []) = some p.positions
  roles : let M := (template DemandRAM.visit 0).instantiate w (demandWords X term stride p₀ T)
    runSegment M.program 65 (some 0) (p.afterPositions mem) (List.replicate (DemandRAM.oldCount X) []) = some p.roles
  incidenceBeforeRoles : T.ActualColumns X (p.afterPositions mem)

/-- The workspace cells still available after constructing the old-arc record table. -/
structure Stored (s : SelectedScore.Selection B X) (mem : Memory w) (p : Passes w) : Prop where
  chosen : (p.final mem) (origin X term stride+2) =
    ((X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth s).toNat : Word w)
  placement : ShrinkRAM.PlacementColumns X.slots X.baseIndex
    (selectedWords X term stride p₀ (p.afterScores mem))
    (X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth s) (p.final mem)
  placementBeforeRoles : ShrinkRAM.PlacementColumns X.slots X.baseIndex
    (selectedWords X term stride p₀ (p.afterScores mem))
    (X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth s) (p.afterPositions mem)
  roles : DemandRAM.RoleColumns X (X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth s)
    (roleBase X term stride) (p.final mem)
  frame : ∀ j, j<origin X term stride ∨ endAddr X term stride ≤ j → p.final mem j = mem j

theorem run (s : SelectedScore.Selection B X) (m : Memory w)
    (terms : SelectedScore.Stored B X s (SelectedScore.headAt X (scoreTables X term stride selectors)) m)
    (dir : Shrink.Directory X.slots X.baseIndex (ShrinkRAM.column p₀ m 6) (ShrinkRAM.column p₀ m 7)
      (ShrinkRAM.column p₀ m 8) (ShrinkRAM.column p₀ m 9))
    (inc : T.ActualColumns X m) (old : OldInputs X term stride p₀ T)
    (hI : T.actualIn.val+DemandRAM.oldCount X ≤ origin X term stride)
    (hW : T.width.val+DemandRAM.oldCount X ≤ origin X term stride)
    {first : Bool} (hp : ShrinkRAM.Params p₀ a (Shrink.colors a) (Shrink.J a) g first)
    (wide : 10 ≤ stride.val) (fit : Fits X term stride)
    (hw : ∀ t, MotifAdmission.weight relativeMass t < 2^w) (hs : selectors.val=B.shrink.selectorBits)
    (scoreFit : ∀ l, layoutScore relativeMass (X.packingData.termWidths B.shrink X.shrinkNumber X.packingWidth s) l < 2^w) :
    ∃ p : Passes w, Execution X term stride selectors p₀ T m p ∧ Stored B X term stride p₀ s m p ∧
      p.scores.length = 8*motifs X+2 ∧ RAMBuckets.probeCount Report.probes p.scores = 32*motifs X+5 ∧
      RAMBuckets.cost Report.probes p.positions = 9*positions X ∧
      RAMBuckets.cost Report.probes p.roles = 11*DemandRAM.oldCount X := by
  let L := scoreTables X term stride selectors
  let b := X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth s
  have h₀ : origin X term stride+2 < placementBase X term stride := by unfold placementBase; omega
  have h₁ : placementBase X term stride ≤ roleBase X term stride := Nat.le_add_right ..
  have h₂ : roleBase X term stride ≤ endAddr X term stride := Nat.le_add_right ..
  have hend : endAddr X term stride < 2^w := fit
  have hword : 8 ≤ 2^w := by have := stride.isLt; omega
  obtain ⟨sr,hsrun,hcell,_,hsframe,sc,sp⟩ := SelectedScore.run_selected B X L m s terms wide
    (show origin X term stride ≤ 2^w by omega) hword hw hs (score_layout X term stride selectors wide fit) scoreFit
  let m₁ := after m (eventLog sr)
  have scFrame := score_frame X term stride selectors fit hsframe
  have cell : m₁ (origin X term stride+2) = (b.toNat : Word w) := by
    have hv : L.levelCell.val = origin X term stride+2 := Nat.mod_eq_of_lt (by omega)
    exact hv ▸ hcell
  let p := selectedWords X term stride p₀ m₁
  let bit := m₁ (origin X term stride+2)
  have hp' : ShrinkRAM.Params p a (Shrink.colors a) (Shrink.J a) g b :=
    shrink_params X term stride p₀ hp m₁ cell
  have d' := carry_directory X term stride p₀ T bit old (fun j hj => scFrame j (.inl hj)) dir
  have reg := shrink_regions X term stride p₀ T bit hp' old fit
  have ho : DemandRAM.oldCount X ≤ 2^w := by
    rw [DemandRAM.count_eq X]
    change roleBase X term stride + 4*DemandRAM.absoluteCount X < 2^w at hend
    omega
  have hslot : Fintype.card X.Base*(2^(Shrink.J a)*2^g)*2^a ≤ 2^w := by
    apply le_trans _ ho
    apply Nat.mul_le_mul_right
    rw [← pow_add]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right (by decide)
    unfold packingLaneBits Shrink.J
    omega
  obtain ⟨pr,hprun,hpscan,hplace⟩ := ShrinkRAM.placement_run X.slots X.baseIndex p b m₁ hp' d' reg hslot
  let m₂ := after m₁ (eventLog pr)
  have posFrame := shrink_frame X term stride p₀ bit fit hpscan
  have inc' := carry_actual X T old.actualOut hI hW
    (m' := m₂) (fun j hj => (posFrame j (.inl (by omega))).trans (scFrame j (.inl hj))) inc
  obtain ⟨rr,hrrun,hrole,roFrame,_,_,rc⟩ :=
    SelectedArena.run_roles X term stride p₀ T bit m₂ b hp inc' hplace old fit
  let passes : Passes w := ⟨sr,pr,rr⟩
  refine ⟨passes,⟨hsrun,hprun,hrrun,inc'⟩,⟨?_,?_,hplace,hrole,?_⟩,sc,sp,hpscan.cost,rc⟩
  · exact (roFrame _ (.inl (by omega))).trans ((posFrame _ (.inl h₀)).trans cell)
  · constructor
    intro x
    let i := ShrinkRAM.word w (Shrink.oldNumber X.baseIndex x)
    have iv : i.val < positions X := by
      have le : i.val ≤ Shrink.oldNumber X.baseIndex x := Nat.mod_le ..
      rw [← Shrink.oldIndex_val] at le
      exact le.trans_lt (Shrink.oldIndex X.baseIndex x).isLt
    have f (t : Fin 4) : passes.final m (ShrinkRAM.outAddr p t i) = m₂ (ShrinkRAM.outAddr p t i) := by
      apply roFrame _ ∘ Or.inl
      have hc := output_column X term stride p₀ bit fit t
      have ht := Nat.mul_le_mul_right (positions X) t.isLt
      rw [Nat.succ_mul] at ht
      change ((p (t.natAdd 10)).val+i.val) % (2^w) < roleBase X term stride
      change (p (t.natAdd 10)).val = _ at hc
      unfold roleBase
      rw [hc]
      exact (Nat.mod_le ..).trans_lt (by omega)
    change ((passes.final m (ShrinkRAM.outAddr p 0 i)).val,(passes.final m (ShrinkRAM.outAddr p 1 i)).val,
      (passes.final m (ShrinkRAM.outAddr p 2 i)).val,(passes.final m (ShrinkRAM.outAddr p 3 i)).val) = _
    rw [f 0,f 1,f 2,f 3]; exact hplace.atSite x
  · intro j hj
    rcases hj with h | h
    · exact (roFrame j (.inl (by omega))).trans ((posFrame j (.inl (by omega))).trans (scFrame j (.inl h)))
    · exact (roFrame j (.inr h)).trans ((posFrame j (.inr (by omega))).trans (scFrame j (.inr (by omega))))

end CompressorRecords.SelectedStage

end VPVNP
end Computability
end OAI
