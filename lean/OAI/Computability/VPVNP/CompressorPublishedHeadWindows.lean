import OAI.Computability.VPVNP.CompressorPublishedHeadPackets
import OAI.Computability.VPVNP.CompressorBlockGroups
import OAI.Computability.VPVNP.CompressorWindowPackets
import OAI.Computability.VPVNP.CompressorSourceScanned

/-! # Installing consecutive header writes at their block ordinals

The emitted source reports determine both the frame at every intermediate
visit and the physical branch tapes. The global fixed catalog supplies a
uniform clock for the six-instruction publishers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PublishedHeads

open BurstRAM DescriptorSpace BlockPlanner PhaseRecipe SourceTransport Schedule
open scoped Fin.CommRing


variable {w N : ℕ}

/-- One publication visit per consecutive header field, using the corresponding right-hand-side
expression. -/
def fieldVisits (step offset : ℕ) (rhs : Fin N → Expr) : List Visit :=
  List.ofFn fun j ↦ publish (LevelFields.address step (offset+j.val)) (rhs j)

/-- Reports writing consecutive fields from the supplied base, with each right-hand side
evaluated in the entry memory. -/
def fieldReports (base : ℕ) (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) (rhs : Fin N → Expr) :=
  List.ofFn fun j ↦ report ((base+j.val : ℕ) : Word w) ((rhs j).eval pub st m)

private theorem reports_write (base : ℕ) (pub : Fin 5 → Word w) (st : Word w) (m : Memory w)
    (rhs : Fin N → Expr) (fit : base+N ≤ 2^w) :
    Writes (fun a ↦ ¬ Outside base N a) (eventLog (fieldReports base pub st m rhs)) := by
  intro a v hav
  obtain ⟨r,hr,hev⟩ := List.mem_flatMap.mp hav
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
  have address : ((base+j.val : ℕ) : Word w).val = base+j.val := Nat.mod_eq_of_lt (by have := j.isLt; omega)
  simp only [report,List.mem_cons,List.not_mem_nil,or_false,reduceCtorEq,false_or,or_self] at hev
  rw [(Event.write.inj hev).1,address]
  unfold Outside
  have := j.isLt
  omega

/-- Strengthen each actual visit along a chronological walk. The common
frame is propagated using the write footprint of the complete report list. -/
private theorem framedWalk {J : Type*} {run more : J → Memory w → List (Report w) → Prop}
    {js : List J} {m original : Memory w} {rs : List (Report w)} {keep : ℕ → Prop}
    (walk : SourceWalk run js m rs) (write : Writes (fun a ↦ ¬ keep a) (eventLog rs))
    (frame : Agree keep m original)
    (lift : ∀ j ∈ js, ∀ mem log, Agree keep mem original → run j mem log → more j mem log) :
    SourceWalk more js m rs := by
  induction walk with
  | done => exact .done _
  | @next j js mem head tail step _ ih =>
    have wr (a v) (h : Event.write a v ∈ eventLog head ++ eventLog tail) : ¬ keep a.val :=
      write a v (by simpa only [eventLog,List.flatMap_append] using h)
    refine .next (lift j (List.mem_cons_self ..) mem head frame step) (ih ?_ ?_ ?_)
    · exact fun a v h ↦ wr a v (List.mem_append_right _ h)
    · intro a ha
      exact (after_outside (data := fun a ↦ ¬ keep a) mem (fun x y h ↦ wr x y (List.mem_append_left _ h)) (not_not_intro ha)).trans (frame a ha)
    · exact fun q h ↦ lift q (List.mem_cons_of_mem j h)

theorem chronological_tapes {A : Script} (m : Memory w)
    (ps : List (SourceWalk.Packet (SourceOnline.Visit A w) w)) (chron : SourceWalk.Chronological SourceOnline.Visit.Runs m ps) :
    ps.flatMap (fun p ↦ p.stage.choices) = branchPaths (ps.flatMap SourceWalk.Packet.reports) := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨rfl,run,tail⟩ := chron
    rw [List.flatMap_cons,List.flatMap_cons,branchPaths,List.map_append,ih _ tail]
    exact congrArg (· ++ _) ((runSegment_iff ..).mp run).2.2.symm

variable {k : Type*} [_root_.Field k] {S : Compression.BlockSchedule k} (B : S.Templates)
variable (base : Word w) (positions blocks t step offset : ℕ) (rhs : Fin N → Expr)
local notation "prog" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog prog)) base
local notation "pub" => Schedule.Ports.data pt
local notation "first" => Script.levelsPerBlock prog * t
local notation "st" => (levelStart L (first) : Word w)
local notation "head" => levelStart L (first+step)
local notation "D" => Window.operandRegion prog L base
local notation "stages" => fieldVisits step offset rhs
local notation "Pkt" => SourceWalk.Packet (SourceOnline.Visit prog w) w

/-- The exact source image and its verified occurrence in the fixed online
program. All packets have the ordinal at which their planner will run. -/
structure Installed (W : Window prog stages) (cap : ℕ) (m : Memory w) : Prop where
  source : Published L pub st m (head+offset) (fun j ↦ LevelFields.address step (offset+j.val)) rhs
  online : ∃ ps : List Pkt, SourceOnline.Group prog L base cap ((prog).initial.length+t*(prog).block.length+W.before.length) (directoryRows L) m ps ∧
    ps.map (fun p ↦ p.stage.phase) = W.indices ∧
    ps.flatMap SourceWalk.Packet.reports = fieldReports (head+offset) pub st m rhs ∧
    ps.flatMap (fun p ↦ p.stage.choices) = List.replicate N []

theorem level_room (ltBlock : t < blocks) (substep : step ≤ S.steps) (fit : endAddress L < 2^w) :
    head+66 ≤ 2^w := by
  have idx : first+step < (L).levels := by
    have hb := Nat.mul_le_mul_left (S.steps+1) ltBlock
    change (S.steps+1)*t+step < 1+(S.steps+1)*blocks
    rw [Nat.mul_succ] at hb
    omega
  have h := DescriptorSpace.level_room L fit ⟨first+step,idx⟩
  change levelStart L (first+step+1) < 2^w at h
  have nh : levelHeaderWords L = 66 := rfl
  simp only [levelStart,Nat.succ_mul,levelWords,nh] at *
  omega

theorem windowLive {visits : List Visit} (W : Window prog visits) (ltBlock : t < blocks) (j : Fin visits.length) :
    Window.ordinal (A:=prog) t (W.index j) < directoryRows L := by
  rw [W.ordinal_index,BlockProgram.directory_rows,(prog).calendar_total]
  have hp := (W.position j).isLt
  have hb := Nat.mul_le_mul_right (prog).block.length ltBlock
  rw [Nat.succ_mul] at hb
  omega

/-- Install one of the actual publication groups. Each source load has a
specified read address, and preceding writes in the group preserve it. -/
theorem install (W : Window prog stages) (cap : ℕ) (m : Memory w) (ltBlock : t < blocks)
    (fit : endAddress L < 2^w) (substep : step ≤ S.steps) (high : offset+N ≤ 54)
    (rows : m (pt).rows.val = (directoryRows L : Word w)) (pitch : m (pub 1-1).val = (levelWords L : Word w))
    (clock : SourceOnline.scanCap prog 7 ≤ cap)
    (stable : ∀ mem, Agree (Outside (head+offset) N) mem m → ∀ j,
      (rhs j).eval pub st mem = (rhs j).eval pub st m)
    (support : ∀ mem, Agree (Outside (head+offset) N) mem m → ∀ j,
      (rhs j).ReadsFrom D pub st mem) : Installed B base positions blocks t step offset rhs W cap m := by
  have room := level_room B base positions blocks t step ltBlock substep fit
  have fits : levelStart L 0 < 2^w := (levelStart_mono L (Nat.zero_le _)).trans_lt fit
  have controls := Window.lowCells (A:=prog) L base rfl rfl fits
  have pp : Outside (head+offset) N (pub 1-1).val := .inl (controls.2.trans_le
    ((levelStart_mono L (Nat.zero_le _)).trans (Nat.le_add_right ..)))
  have extent : head+offset+N ≤ 2^w := by omega
  have entry : LevelFields.Entry L (first) pub st m := ⟨rfl,pitch⟩
  have published := run_fields L (first) step offset pub st m rhs entry (by omega) extent pp stable
  refine ⟨published,?_⟩
  let reports := fieldReports (head+offset) pub st m rhs
  have raw : SourceWalk (Window.Raw (A:=prog) L base t 7) stages m reports := by
    apply framedWalk published.walk (reports_write _ pub st m rhs extent) (fun _ _ ↦ rfl)
    intro v hv mem log frame run
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
    refine ⟨7,[[]],le_rfl,run,⟨trivial,trivial,?_⟩⟩
    intro l
    fin_cases l
    · exact ⟨⟨trivial,trivial,⟨trivial,trivial⟩,Or.inr (.inl rfl)⟩,trivial⟩
    · exact support mem frame j
  have bounds (j : Fin (prog).size) :
      ((prog).plan.recipes j).2.code.length+1+2*Online.N (prog).size (prog).size+5 ≤ cap ∧
      7+3+4*(((prog).catalog j).params+1)+2*Online.N (prog).size (prog).size+5 ≤ cap := by
    let p : SourceOnline.Visit prog w := HeaderPacket.attach prog j pub st m 7 [[]]
    exact SourceOnline.scanCap_clocks (p := ⟨p,m,[]⟩) 7 (by rfl) clock
  obtain ⟨ps,hp,ph,rs⟩ := W.group L base t rfl rfl fits cap 7 m reports raw rows pitch
    (windowLive B base positions blocks t W ltBlock) (fun j _ ↦ (bounds j).1) (fun j _ ↦ (bounds j).2)
  refine ⟨ps,hp,ph,rs,?_⟩
  rw [chronological_tapes m ps hp.chronological,rs]
  change branchPaths (List.ofFn _) = _
  rw [branchPaths,List.map_ofFn]
  change List.ofFn (fun _ : Fin N ↦ ([] : List Bool)) = _
  simp

end CompressorRecords.PublishedHeads

end VPVNP
end Computability
end OAI
