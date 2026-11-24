import OAI.Computability.VPVNP.CompressorResidentNativeWalk
import OAI.Computability.VPVNP.CompressorShrinkResidentFinal
import OAI.Computability.VPVNP.CompressorShrinkSelectedReadback
import OAI.Computability.VPVNP.CompressorShrinkSlotPacketGroup
import OAI.Computability.VPVNP.CompressorShrinkSlotOperandTransport
import OAI.Computability.VPVNP.CompressorWindowPackets
import OAI.Computability.VPVNP.CompressorBlockHeadReads
import OAI.Computability.VPVNP.CompressorSourceScanned

/-! # Launching the resident directory group in the repeated block

The planner rereads its size, address and layout inputs before every native
stage. The current group writes only the fresh table and the six designated
header cells. The inputs therefore keep their physical values through all
twelve stages, even though each stage sees the preceding report log.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkResidentPackets

open Compression BurstRAM BlockPlanner PhaseRecipe SourceTransport SourceOnline DescriptorSpace
open ShrinkResidentRun ShrinkResidentLayout
open scoped Classical Fin.CommRing

private theorem map_walk {J K : Type*} {w : ℕ} {source : J → Memory w → List (Report w) → Prop}
    {dest : K → Memory w → List (Report w) → Prop} (f : J → K)
    (convert : ∀ j m rs, source j m rs → dest (f j) m rs) {js : List J} {m : Memory w} {rs : List (Report w)}
    (walk : SourceWalk source js m rs) : SourceWalk dest (js.map f) m rs := by
  induction walk with
  | done => exact .done _
  | next head _ ih => exact .next (convert _ _ _ head) ih

theorem raw_walk {w : ℕ} {P : Plan} (D : Values w) {A : Script} (L : DescriptorSpace.Layout)
    (base : Word w) (t : ℕ) (m : Memory w) (rs : List (Report w))
    (values : OperandValues P D (Workspace.ports (Schedule.arity A.catalog) base).data (levelStart L (A.levelsPerBlock*t)) m)
    (roots : OperandReads P (fun x => Window.operandRegion A L base x ∧ ¬ Mutable D x)
      (Workspace.ports (Schedule.arity A.catalog) base).data (levelStart L (A.levelsPerBlock*t)) m)
    (lowArena : levelStart L 0 ≤ D.layout.first) (lowHeader : levelStart L 0 ≤ D.level)
    (walk : SourceWalk (Native P D (levelStart L 0)) order m rs) :
    SourceWalk (Window.Raw («A» := A) L base t 40) P.visits m rs := by
  let region := Window.operandRegion A L base
  let keep := fun x => region x ∧ ¬ Mutable D x
  let pub := (Workspace.ports (Schedule.arity A.catalog) base).data
  let state : Word w := levelStart L (A.levelsPerBlock*t)
  have stay (j : Stage) (mem : Memory w) (logs : List (Report w)) (native : Native P D (levelStart L 0) j mem logs)
      (same : Agree keep m mem) : Agree keep m (after mem (eventLog logs)) :=
    fun x hx => (same x hx).trans (after_outside mem native.write hx.2).symm
  have h := (walk.with_invariant (I := Agree keep m) (fun _ _ => rfl) stay).1
  rw [← P.ordered]
  apply map_walk (Stage.visit P) _ h
  intro j mem logs info
  obtain ⟨native,same⟩ := info
  let v := j.visit P
  have support := roots.supported j
  obtain ⟨first,stop,bank⟩ := values.words j
  have start : v.initial.eval pub state mem = 0 := (v.initial.eval_eq_of_reads support.initial same).symm.trans first
  have limit : v.stop.eval pub state mem = (j.limit D : Word w) := (v.stop.eval_eq_of_reads support.stop same).symm.trans stop
  have args : (fun k => (v.params k).eval pub state mem) = j.bank P D :=
    funext fun k => ((v.params k).eval_eq_of_reads (support.params k) same).symm.trans (congrFun bank k)
  refine ⟨j.fuel,List.replicate (j.limit D) [],j.clock.2,?_,?_⟩
  · refine ⟨j.clock.1,?_,?_,native.read,?_⟩
    · change runSegment ((v.worker.table.instantiate w (fun k => (v.params k).eval pub state mem)).program)
        j.fuel (some (v.initial.eval pub state mem)) mem _ = _
      rw [args,start]; exact native.run
    · change Progress (v.stop.eval pub state mem) (v.initial.eval pub state mem) logs
      rw [limit,start]; exact native.progress
    · intro a y hv
      rcases native.write a y hv with hit | hit
      · exact lowArena.trans hit.1
      · exact lowHeader.trans ((Nat.le_add_right ..).trans hit.1)
  · have widen : ∀ x, keep x → region x := fun _ hx => hx.1
    exact ⟨v.initial.reads_transport support.initial same widen,v.stop.reads_transport support.stop same widen,
      fun j => (v.params j).reads_transport (support.params j) same widen⟩

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  {g w : ℕ} (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
variable (base : Word w) (positions blocks t : ℕ)
local notation "A" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "H" => levelStart L 0
local notation "W" => window B i
local notation "pt" => Workspace.ports (Schedule.arity (BlockPlanner.Script.catalog (BlockProgram.script B))) base
local notation "pub" => Schedule.Ports.data pt
local notation "blockFirst" => BlockPlanner.Script.levelsPerBlock (BlockProgram.script B)*t
local notation "st" => (levelStart L blockFirst : Word w)
local notation "stepLevel" => blockFirst+i.val
local notation "oldHead" => levelStart L stepLevel
local notation "first" => tableBase L stepLevel (5 : Fin 6)
local notation "P" => plan B i

/-- Uniform clock bound for resident packet scans obtained from the block script with worker
fuel 40. -/
def clock := scanCap (BlockProgram.script B) 40

/-- The physical read bank survives the publications at offsets 30–35 and
all resident-array writes. Only the genuine selected score is loaded from
an address outside the immutable header words. -/
theorem root_reads (m : Memory w) (absolute role : Word w) (side : Bool)
    (entry : LevelFields.Entry L blockFirst pub st m) (levelFit : oldHead+66 ≤ 2^w)
    (pitchLow : ((pt).directory-1).val < H)
    (scoreLo : oldHead+36 ≤ ((SelectedPlan.layoutCell (P).chosen).eval pub st m).val)
    (scoreHi : ((SelectedPlan.layoutCell (P).chosen).eval pub st m).val < first) :
    OperandReads P (fun x => Window.operandRegion A L base x ∧ ¬ Mutable (values P X first oldHead absolute role side) x)
      pub st m := by
  let D := values P X first oldHead absolute role side
  let R := fun x => Window.operandRegion A L base x ∧ ¬ Mutable D x
  have oldLow : H ≤ oldHead := levelStart_mono L (Nat.zero_le stepLevel)
  have dataAfter : oldHead+66 ≤ first := by
    change oldHead+66 ≤ ((oldHead+66)+6*slotCapacity L)+5*tableWords L
    omega
  have outside (x : ℕ) (below : x<first) (header : x<oldHead+30 ∨ oldHead+36≤x) : ¬ Mutable D x := by
    rintro (h|h)
    · exact (not_le_of_gt below) h.1
    · change oldHead+30 ≤ x ∧ x < oldHead+36 at h; omega
  have pitch : R (pub 1-1).val := ⟨Or.inr (Or.inl rfl),outside _ (by change ((pt).directory-1).val < first; omega)
      (Or.inl (by change ((pt).directory-1).val < oldHead+30; omega))⟩
  have scalar (j : Fin 4) : R (oldHead+j.val) :=
    ⟨.inr (.inr (oldLow.trans (Nat.le_add_right ..))),outside _ (by have := j.isLt; omega) (.inl (by have := j.isLt; omega))⟩
  have table (j : Fin 6) : R (oldHead+(60+j.val)) :=
    ⟨.inr (.inr (oldLow.trans (Nat.le_add_right ..))),outside _ (by have := j.isLt; omega) (.inr (by omega))⟩
  have score : R ((SelectedPlan.layoutCell (P).chosen).eval pub st m).val :=
    ⟨.inr (.inr (oldLow.trans ((Nat.le_add_right ..).trans scoreLo))),outside _ scoreHi (.inr scoreLo)⟩
  obtain ⟨sites,motifs,arena,role,layout,abs,level⟩ :=
    BlockHeadReads.resident_operands_of B i R entry levelFit pitch scalar table score
  exact ⟨sites,motifs,arena,role,layout,abs,level⟩

/-- Assemble the native worker bank from the selected score and the original
ranked bundle's absolute-CD directory. Table five contains the resident arena. -/
theorem operand_values (m : Memory w) (term : Word w) (pre : Fin 14 → Word w) (inc : IncidenceDirectory w)
    (start : ℕ) (side : Bool)
    (entry : LevelFields.Entry L blockFirst pub st m) (room : oldHead+66 ≤ 2^w)
    (head : m (tableHead L stepLevel (5 : Fin 6)) = (first : Word w))
    (selected : SelectedPlan.Reads (P).chosen X pre inc term pub st m)
    (bundle : ShrinkBundlePlan.HeadValues X i.val (BlockProgram.arena B i.val 0) pub st m start)
    (chosen : m (((SelectedPlan.layoutCell (P).chosen).eval pub st m).val) = (side.toNat : Word w)) :
    let Z := ShrinkInput.plan X start
    let absolute : Word w := ((Z.gathered + Z.B*Z.Q : ℕ) : Word w)
    let role : Word w := SelectedArena.roleBase X term ((P).chosen.termStride : Word w)
    OperandValues P (values P X first oldHead absolute role side) pub st m := by
  intro Z absolute role
  have table : (BlockProgram.arena B i.val 5).eval pub st m = (first : Word w) :=
    (LevelFields.eval_table entry i.val (5 : Fin 6) (by change oldHead+54+6+5 < 2^w; omega)).trans head
  refine ⟨⟨selected.nextSites,selected.motifs,table⟩,LevelFields.eval_atLevel entry i.val,?_,
    SelectedPlan.roles_head (P).chosen X pre inc term pub st m selected,chosen⟩
  exact bundle.absoluteCD

/-- The selected and ranked operands come from the existing physical level
header and its term layout. -/
theorem header_values (m : Memory w) (inc : IncidenceDirectory w) (start : ℕ) (side : Bool)
    (entry : LevelFields.Entry L blockFirst pub st m) (room : oldHead+66 ≤ 2^w)
    (fields : ShrinkHeaderReads.Header i X inc start L blockFirst m)
    (termFit : ShrinkInput.termEnd X start 10 < 2^w) (wordFit : 10 < 2^w)
    (head : m (tableHead L stepLevel (5 : Fin 6)) = (first : Word w))
    (chosen : m (((SelectedPlan.layoutCell (P).chosen).eval pub st m).val) = (side.toNat : Word w)) :
    let Z := ShrinkInput.plan X start
    let absolute : Word w := ((Z.gathered + Z.B*Z.Q : ℕ) : Word w)
    let role : Word w := SelectedArena.roleBase X (ShrinkInput.termHead (w := w) X start) (10 : Word w)
    OperandValues P (values P X first oldHead absolute role side) pub st m := by
  intro Z absolute role
  have selected := (SelectedTailPackets.header_values B i X inc start pub st m fields entry termFit wordFit
    (fun _ => True) trivial (fun _ _ => trivial)).1
  have bundle := ShrinkBundlePlan.head_values X (fields.reads B entry)
  exact operand_values B i X base positions blocks t m _ _ inc start side entry room head selected bundle chosen

/-- Native, consecutive checked and prepared rows from the actual header
and selected role data. The width and the prior choice enter through RAM. -/
theorem group (m : Memory w) (absolute role : Word w) (side : Bool)
    (space : Areas X first absolute role) (dir : ShrinkResidentDirectory.Absolute X absolute m)
    (roles : DemandRAM.RoleColumns X side role.val m) (absLow : H ≤ absolute.val) (roleLow : H ≤ role.val)
    (vals : OperandValues P (values P X first oldHead absolute role side) pub st m)
    (scoreLo : oldHead+36 ≤ ((SelectedPlan.layoutCell (P).chosen).eval pub st m).val)
    (scoreHi : ((SelectedPlan.layoutCell (P).chosen).eval pub st m).val < first)
    (rows : m (pt).rows.val = (directoryRows L : Word w)) (pitch : m ((pt).directory-1).val = (levelWords L : Word w))
    (ht : t < blocks) (cap : ℕ) (clockFits : clock B ≤ cap) :
    ∃ h r : Passes w, ∃ ps : List (SourceOnline.Packet A w),
      Built X first absolute role side false m h ∧ Built X first absolute role side true (h.final m) r ∧
      Group A L base cap ((A).initial.length+t*(A).block.length+(BlockIndex.earlier B i).length+36)
        (directoryRows L) m ps ∧ ps.map (fun p => p.stage.phase) = (W).indices ∧
      ps.flatMap SourceWalk.Packet.reports = (h.all++r.all)++List.ofFn (ShrinkResidentsPlan.headerReport oldHead (layout X first) w) ∧
      (∀ j : Fin 6, post m ps (oldHead+(30+j.val)) = (ShrinkResidentsPlan.headValues (layout X first) j : Word w)) ∧
      (∀ x, x < oldHead+30 ∨ oldHead+36 ≤ x → post m ps x = r.final (h.final m) x) ∧
      (∀ maps : Bool, ShrinkHistoryRows.Directory (ShrinkResidentDirectory.oldOrder X maps) (ShrinkHistoryRows.packedOrder X)
        (ShrinkResidentDirectory.place X maps side) (outputBank X first maps) (post m ps)) ∧
      RAMBuckets.cost Report.probes (ps.flatMap SourceWalk.Packet.reports) = (layout X first).charge := by
  let D := values P X first oldHead absolute role side
  have headerLow := levelStart_mono L (Nat.zero_le stepLevel)
  have dataAfter : oldHead+66 ≤ first := by
    change oldHead+66 ≤ ((oldHead+66)+6*slotCapacity L)+5*tableWords L
    omega
  have arenaFit : first < 2^w := by
    have ranges := (layout X first).ranges false
    have bound := space.fit
    obtain ⟨a,b,c,d⟩ := ranges
    change first ≤ (layout X first).owner false at a
    omega
  have floor : H ≤ first := headerLow.trans ((Nat.le_add_right ..).trans dataAfter)
  have hfit := floor.trans_lt arenaFit
  have entry : LevelFields.Entry L blockFirst pub st m := ⟨rfl,pitch⟩
  have arity := (BlockProgram.layout_arity B base.val positions blocks).symm
  have low := Window.lowCells («A» := A) L base arity rfl hfit
  have roots := root_reads B i X base positions blocks t m absolute role side entry (by omega) low.2 scoreLo scoreHi
  obtain ⟨h,r,hh,hr,walk⟩ := native_walk P X first oldHead absolute role side space m dir roles H floor
    absLow roleLow (by omega)
  have raw := raw_walk D L base t m _ vals roots floor headerLow walk
  have live (j : Fin (P).visits.length) : Window.ordinal («A» := A) t ((W).index j) < directoryRows L := by
    rw [(W).ordinal_index,BlockProgram.directory_rows,(A).calendar_total]
    have pos := ((W).position j).isLt
    have before := Nat.mul_le_mul_right (A).block.length ht
    rw [Nat.succ_mul] at before
    omega
  let recTime (j : Fin (A).size) := ((A).plan.recipes j).2.code.length+1+2*Schedule.Online.N (A).size (A).size+5
  have rc (j : Fin (A).size) (_ : j ∈ (W).indices) : recTime j ≤ cap :=
    (Finset.le_sup (f := recTime) (Finset.mem_univ j)).trans ((le_max_left ..).trans clockFits)
  have dc (j : Fin (A).size) (_ : j ∈ (W).indices) :
      40+3+4*(((A).catalog j).params+1)+2*Schedule.Online.N (A).size (A).size+5 ≤ cap := by
    have h := Schedule.params_le_arity (A).catalog j
    have bound : 40+3+4*(Schedule.arity (A).catalog+1)+2*Schedule.Online.N (A).size (A).size+5 ≤ cap :=
      (le_max_right ..).trans clockFits
    omega
  obtain ⟨ps,cert,stages,logs⟩ := (W).group L base t arity rfl hfit cap 40 m _ raw rows pitch live rc dc
  rw [window_offset] at cert
  have effect : post m ps = after (r.final (h.final m)) (eventLog (List.ofFn (ShrinkResidentsPlan.headerReport oldHead (layout X first) w))) := by
    unfold post
    rw [logs,SourceWalk.after_append,SourceWalk.after_append,h.after_all,r.after_all]
    rfl
  have headerData := ShrinkResidentsPlan.published oldHead (layout X first) (w := w) (by omega) (r.final (h.final m))
  have finalHeads := effect.symm ▸ headerData
  refine ⟨h,r,ps,hh,hr,by simpa only [Nat.add_assoc] using cert,stages,logs,finalHeads.1,finalHeads.2,?_,?_⟩
  · intro maps
    apply transfer X first side maps (m := r.final (h.final m)) _ space.fit
      (fun x hx _ => finalHeads.2 x (.inr (by omega)))
    cases maps
    · exact retained_hidden X first absolute role side hh hr space.fit
    · exact hr.directory
  · rw [logs,RAMBuckets.cost_append,RAMBuckets.cost_append,hh.charge,hr.charge]
    change 9*((layout X first).motifs*4)+2*(layout X first).sites+
      (9*((layout X first).motifs*6)+2*(layout X first).sites)+12 =
      90*(layout X first).motifs+4*(layout X first).sites+12
    omega

end CompressorRecords.ShrinkResidentPackets

end

end VPVNP
end Computability
end OAI
