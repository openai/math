import OAI.Computability.VPVNP.LiveProgramPairStages

/-! # Path and cap at a terminal ordinary stage of the live table -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group
open BurstRAM BurstRAM.PrivateRAM LiveStageLink
open scoped Classical

variable {G : Group} {s : Stage} {m : Memory G.w}

/-- Relocation into the shared register and operand banks preserves every native report. -/
theorem component_segment (G : Group) (s : Stage) (f : ℕ) (st : Option (Word G.w))
    (m : Memory G.w) (bs : List (List Bool)) :
    runSegment (sourceProgram G.T G.pub s) f st m bs =
      runSegment (Pieces.component G.components s G.g G.lit) f st m bs := by
  induction bs generalizing st m with
  | nil => rfl
  | cons b bs ih =>
    cases st with
    | none => rfl
    | some st =>
      simp only [runSegment,Pieces.component_eq]
      cases execute (Pieces.component G.components s G.g G.lit) f
          ((Pieces.component G.components s G.g G.lit).start st) m b with
      | none => rfl
      | some r => exact congrArg (Option.map (r :: ·)) (ih r.result (after m r.events))

private theorem run_room {C : Type*} {P : BurstRAM.Program G.w C} {fuel : ℕ} {st : Option (Word G.w)}
    {mem : Memory G.w} {bs : List (List Bool)} {rs : List (Report G.w)}
    (h : runSegment P fuel st mem bs = some rs) : ∀ rep ∈ rs, rep.events.length < fuel := by
  induction bs generalizing st mem rs with
  | nil => simp only [runSegment,Option.some.injEq] at h; subst rs; simp
  | cons b bs ih =>
    cases st with
    | none => contradiction
    | some st =>
      cases he : execute P fuel (P.start st) mem b with
      | none => simp [runSegment,he] at h
      | some rep =>
        simp only [runSegment,he,Option.map_eq_some_iff] at h
        obtain ⟨rest,hr,rfl⟩ := h
        exact List.forall_mem_cons.mpr ⟨(execute_spec he).1.length_lt,ih hr⟩

private theorem exit_eq (G : Group) (s : Stage) (h : G.nextStage s = none) (r : Report G.w) :
    exitReport G.nextStage G.addr s r = r := by
  cases r with
  | mk ev res => cases res <;> simp [exitReport,h]

/-- The dispatcher adds its own read at every terminal-stage call. The
final report halts without transferring, so no further choices are allowed. -/
noncomputable def terminalEquiv (A : Entry G s m) (hnext : G.nextStage s = none)
    (cap : List (Report G.w) → Prop) :
    ActualPaths (Pieces.component G.components s G.g G.lit) (G.clockAt s) 0 m
      (fun rs => cap (rs.map (linkedReport G.nextStage G.addr s))) ≃
      ActualPaths G.P G.clock 0 m cap := by
  let toOrd (a : ActualPaths (Pieces.component G.components s G.g G.lit) (G.clockAt s) 0 m
      (fun rs => cap (rs.map (linkedReport G.nextStage G.addr s)))) : G.StagePaths s m := ⟨a.val, by
    obtain ⟨rs,hr,hh,_⟩ := a.property
    refine ⟨rs,(component_segment ..).trans hr,hh,?_⟩
    intro rep hrep
    change (exitReport G.nextStage G.addr s rep).events.length < G.clockAt s
    rw [exit_eq G s hnext]; exact run_room hr rep hrep⟩
  let add (a : ActualPaths (Pieces.component G.components s G.g G.lit) (G.clockAt s) 0 m
      (fun rs => cap (rs.map (linkedReport G.nextStage G.addr s)))) :
      Σ p : G.StagePaths s m, Remainder cap p := ⟨toOrd a,⟨[],[],rfl,by simp [transferState,hnext,endState],by
        obtain ⟨rs,hr,_,hc⟩ := a.property
        have he := (ordinaryRun (toOrd a)).symm.trans ((component_segment ..).trans hr)
        simpa only [← Option.some.inj he,List.append_nil] using hc⟩⟩
  let e := ordinaryEquiv (next := G.nextStage) (cap := cap) G.tagFit A.frame A.ready A.tag
  apply Equiv.trans (Equiv.ofBijective add ?_)
  · simpa only [G.clock_add s] using e
  constructor
  · intro a b h
    exact Subtype.ext (congrArg (fun x => x.1.val) h)
  · rintro ⟨p,rest⟩
    obtain ⟨bs,rs,hr,_,hc⟩ := rest
    have ht : transferState (w := G.w) G.nextStage s = none := by simp [transferState,hnext]
    rw [ht] at hr
    cases bs with
    | cons _ _ => contradiction
    | nil =>
      simp only [runSegment,Option.some.injEq] at hr
      subst rs
      refine ⟨⟨p.val,ordinaryReports p,(component_segment ..).symm.trans (ordinaryRun p),
        p.property.choose_spec.2.1,by simpa only [List.append_nil] using hc⟩,?_⟩
      rfl

end LiveProgram.PairStages.Group

end VPVNP
end Computability
end OAI
