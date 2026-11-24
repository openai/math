import OAI.Computability.VPVNP.LiveHeaderPrefixRun
import OAI.Computability.VPVNP.LiveHeaderPrefixCancel
import OAI.Computability.VPVNP.LiveStageLinkInversion

/-! # Rejection at a reached stage excludes all accepting live-header paths -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule

variable {w : ℕ} {s : Sizes} {base cap : ℕ}
variable {fromId : Option StageId} {failed : StageId} {m atStage : Memory w} {xs : List (StageTrace w)}

/-- The single native header stage instantiated with its own row of public operands. -/
abbrev nativeStage (w : ℕ) (s : Sizes) (base : ℕ) (i : StageId) :=
  ((stageTemplate (stage i)).2.instantiate w (rowData w s base (stage i))).program

/-- The complete linked header program instantiated at the given word width and workspace base. -/
abbrev nativeHeader (w : ℕ) (s : Sizes) (base : ℕ) := (program.instantiate w (publicData w s base)).program

/-- For a deterministic successful prefix, an accepted path would have to
continue from its verified postmemory, persistent word zero, and actual tag. -/
private theorem StagePrefix.suffix_of_accepted (p : StagePrefix s base fromId m xs (some failed) atStage)
    (good : ∀ x ∈ xs, x.Good s) (hfits : stages.length ≤ 2^w) (hcap : 40+2*stages.length+5 ≤ cap)
    (htag : ∀ i, fromId = some i → m (Fin.ofNat (2^w) base).val = LiveStageLink.tagWord w i)
    {bs : List (List Bool)} {outs : List (Report w)}
    (hr : runSegment (nativeHeader w s base) cap (fromId.map (fun _ => 0)) m bs = some outs)
    (he : endState (fromId.map (fun _ => (0 : Word w))) outs = none) :
    atStage (Fin.ofNat (2^w) base).val = LiveStageLink.tagWord w failed ∧
    ∃ bits rs, runSegment (nativeHeader w s base) cap (some 0) atStage bits = some rs ∧
      endState (some 0) rs = none := by
  have room (x : StageTrace w) (hx : x ∈ xs) : x.fuel+2*stages.length+5 ≤ cap := by
    have := (good x hx).1; omega
  obtain ⟨hpre,hstate,hmem,ht⟩ := p.run hfits room htag
  have hempty : xs.flatMap StageTrace.paths = List.replicate (xs.flatMap StageTrace.paths).length [] := by
    apply List.eq_replicate_length.mpr
    intro b hb
    obtain ⟨x,hx,hb⟩ := List.mem_flatMap.mp hb
    rw [(good x hx).2.1] at hb
    exact (List.mem_replicate.mp hb).2
  rw [hempty] at hpre
  obtain ⟨bt,rt,_,_,hr',he'⟩ := accepted_suffix_of_empty_prefix hpre hstate hr he
  rw [hmem] at hr'
  exact ⟨ht failed rfl,bt,rt,hr',he'⟩

/-- If the reached component has no accepting source segment, its native
linker cannot advance beyond that stage or accept. Continuing source calls
only need to preserve the one reserved stage-tag word. -/
theorem StagePrefix.rejects (p : StagePrefix s base fromId m xs (some failed) atStage)
    (good : ∀ x ∈ xs, x.Good s) (hfits : stages.length ≤ 2^w) (hcap : 40+2*stages.length+5 ≤ cap)
    (htag : ∀ i, fromId = some i → m (Fin.ofNat (2^w) base).val = LiveStageLink.tagWord w i)
    (hbad : ∀ fuel bs rs, runSegment (nativeStage w s base failed) fuel (some 0) atStage bs = some rs →
      endState (some 0) rs ≠ none)
    (hframe : ∀ fuel (st : Word w) mem b rep,
      execute (nativeStage w s base failed) fuel ((nativeStage w s base failed).start st) mem b = some rep →
      rep.result.isSome → after mem rep.events (Fin.ofNat (2^w) base).val = mem (Fin.ofNat (2^w) base).val) :
    ¬∃ bs outs, runSegment (nativeHeader w s base) cap (fromId.map (fun _ => 0)) m bs = some outs ∧
      endState (fromId.map (fun _ => (0 : Word w))) outs = none := by
  rintro ⟨bs,outs,hr,he⟩
  obtain ⟨ht,bits,rs,hs,hstop⟩ := p.suffix_of_accepted good hfits hcap htag hr he
  let addr : Word w := Fin.ofNat _ base
  obtain ⟨before,_,source,_,hr',ha'⟩ := LiveStageLink.recover_accepting_stage component next (bank w s base) addr failed
    hfits (by omega : 2*stages.length+2 ≤ cap) 0 atStage bits rs ht (by
      intro st mem b rep h success
      rw [component_start] at h
      exact hframe _ st mem b rep h success) hs hstop
  rw [run_component] at hr'
  exact hbad _ before source hr' ha'

/-- Immediate rejection at a mode check needs no assumptions on that
component's behavior at other memories. -/
theorem StagePrefix.rejects_entry (p : StagePrefix s base fromId m xs (some failed) atStage)
    (good : ∀ x ∈ xs, x.Good s) (hfits : stages.length ≤ 2^w) (hcap : 40+2*stages.length+5 ≤ cap)
    (htag : ∀ i, fromId = some i → m (Fin.ofNat (2^w) base).val = LiveStageLink.tagWord w i)
    (hbad : ∀ fuel bits, execute (nativeStage w s base failed) fuel ((nativeStage w s base failed).start 0) atStage bits = none) :
    ¬∃ bs outs, runSegment (nativeHeader w s base) cap (fromId.map (fun _ => 0)) m bs = some outs ∧
      endState (fromId.map (fun _ => (0 : Word w))) outs = none := by
  rintro ⟨bs,outs,hr,he⟩
  obtain ⟨ht,bits,rs,hs,hstop⟩ := p.suffix_of_accepted good hfits hcap htag hr he
  cases bits with
  | nil => simp [runSegment] at hs; subst rs; contradiction
  | cons b bits =>
    simp only [runSegment] at hs
    cases hcall : execute (nativeHeader w s base) cap ((nativeHeader w s base).start 0) atStage b with
    | none => simp [hcall] at hs
    | some r =>
      obtain ⟨rep, hsrc, _⟩ := LiveStageLink.recover_call component next (bank w s base) (Fin.ofNat _ base) failed
        hfits (by omega : 2*stages.length+2 ≤ cap) 0 atStage b r ht hcall
      rw [component_start] at hsrc
      change execute (nativeStage w s base failed) _ ((nativeStage w s base failed).start 0) atStage b = _ at hsrc
      rw [hbad] at hsrc
      contradiction

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
