import OAI.Computability.VPVNP.LiveCompressedPairReportCaps

/-! # The three resource fields of the native compressed-pair execution -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM CompressorRecords PairSimulation

variable {w : ℕ} (pub : Fin 11 → Word w)

private theorem innerBounds (s : Stage) (r : Report w) :
    (report pub s r).probes ≤ r.probes+2 ∧ (report pub s r).events.length ≤ r.events.length+30 := by
  obtain ⟨_,hp,ht,_⟩ := report_effect pub s r (fun _ => 0)
  exact ⟨by split at hp <;> omega,ht⟩

private theorem framedCost (base : Word w) (m : Memory w) (rs : List (Report w)) :
    RAMBuckets.cost Report.probes ((OnlineWorkspace.framed base m rs).map (report pub Stage.online)) ≤
      9*RAMBuckets.cost Report.probes rs := by
  induction rs generalizing m with
  | nil => rfl
  | cons a rs ih =>
    have frame := (Workspace.report_effect base m a).2.1
    have link := (innerBounds pub .online (Workspace.report base m a)).1
    have rest := ih (after m a.events)
    change 1+(report pub Stage.online (Workspace.report base m a)).probes+
      RAMBuckets.cost _ ((OnlineWorkspace.framed base (after m a.events) rs).map _) ≤
      9*(1+a.probes+RAMBuckets.cost _ rs)
    omega

private theorem frameRows (base : Word w) (m : Memory w) (rs : List (Report w)) {a : Report w}
    (h : a ∈ (OnlineWorkspace.framed base m rs).map (report pub Stage.online)) :
    ∃ r ∈ rs, a.probes ≤ r.probes+8 ∧ a.events.length ≤ r.events.length+54 := by
  induction rs generalizing m with
  | nil => contradiction
  | cons r rs ih =>
    change a ∈ report pub Stage.online (Workspace.report base m r) ::
      (OnlineWorkspace.framed base (after m r.events) rs).map _ at h
    rcases List.mem_cons.mp h with rfl | h
    · obtain ⟨_,hp,ht,_,_⟩ := Workspace.report_effect base m r
      have ⟨p,t⟩ := innerBounds pub .online (Workspace.report base m r)
      exact ⟨r,by simp,by omega,by omega⟩
    · obtain ⟨j,hj,p,t⟩ := ih (after m r.events) h
      exact ⟨j,List.mem_cons_of_mem _ hj,p,t⟩

private theorem termCost (addr : Word w) (ls : List (TerminalLink.Entry w × Report w)) :
    RAMBuckets.cost Report.probes ((terminalWorkers addr ls).map (report pub Stage.terminal)) ≤
      9*RAMBuckets.cost Report.probes (ls.map Prod.snd) := by
  induction ls with
  | nil => rfl
  | cons p ls ih =>
    have a := TerminalLink.report_probes_le addr p.1 p.2
    have b := (innerBounds pub .terminal (TerminalLink.report addr p.1 p.2)).1
    change 1+(report pub Stage.terminal (TerminalLink.report addr p.1 p.2)).probes+
      RAMBuckets.cost _ ((terminalWorkers addr ls).map _) ≤ 9*(1+p.2.probes+RAMBuckets.cost _ _)
    omega

private theorem initialCost (s : List (Stage × Report w)) (H : ℕ) (small : ∀ p ∈ s, p.2.probes+5 ≤ H) :
    RAMBuckets.cost Report.probes (s.map (fun p => report pub p.1 p.2)) ≤ s.length*H := by
  induction s with
  | nil => simp [RAMBuckets.cost]
  | cons p s ih =>
    have h := (innerBounds pub p.1 p.2).1
    have cap := small p List.mem_cons_self
    have rest := ih (fun x hx => small x (List.mem_cons_of_mem _ hx))
    change 1+(report pub p.1 p.2).probes+RAMBuckets.cost _ (s.map _) ≤ (s.length+1)*H
    rw [Nat.succ_mul]
    omega

/-- Work, total charged accesses, and maximal burst for
`CompressedPaths.Execution`, before the live group adds its tag. -/
theorem cursor_execution_caps (addr : Word w) (b : Bootstrap) (B n base : ℕ) (startMem : Memory w)
    (initial phases d : ℕ) (onlineBase : Word w) (onlineMem : Memory w)
    (online : List (Report w)) (terminal : List (TerminalLink.Entry w × Report w))
    (S H fuel : ℕ) (hS : 128 ≤ S)
    (hs : ∀ p ∈ cursorStartupSources b pub B n base startMem initial phases d,
      ∃ i : Fin 8, p.2.probes < sourceFuel b initial phases n i ∧ p.2.events.length < sourceFuel b initial phases n i)
    (hb : ∀ i, sourceFuel b initial phases n i+5 ≤ H)
    (hf : ∀ i, sourceFuel b initial phases n i+77 ≤ fuel)
    (ho : ∀ r ∈ online, r.probes+11 ≤ H ∧ r.events.length+101 ≤ fuel)
    (ht : ∀ r ∈ terminal.map Prod.snd, r.probes+9 ≤ H ∧ r.events.length+107 ≤ fuel)
    (oc : 64*RAMBuckets.cost Report.probes online ≤ S*H)
    (tc : 320*RAMBuckets.cost Report.probes (terminal.map Prod.snd) ≤ S*H) :
    let rs := cursorStartupLogs b pub B n base startMem initial phases d ++
      ((OnlineWorkspace.framed onlineBase onlineMem online).map (report pub Stage.online) ++
        (terminalWorkers addr terminal).map (report pub Stage.terminal))
    (∀ r ∈ rs, r.events.length+4 ≤ fuel) ∧ 4*RAMBuckets.cost Report.probes rs ≤ S*H ∧
      ∀ r ∈ rs, 3+r.probes ≤ H := by
  intro rs
  let src := cursorStartupSources b pub B n base startMem initial phases d
  have initialRows := startup_rows_le b initial phases n H fuel src hs hb hf
  have rows (r : Report w) (hr : r ∈ rs) : r.events.length+4 ≤ fuel ∧ 3+r.probes ≤ H := by
    simp only [rs,List.mem_append,cursorStartupLogs_eq] at hr
    rcases hr with hr | hr | hr
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
      have ⟨h₁,h₂⟩ := initialRows p hp
      have ⟨a,c⟩ := innerBounds pub p.1 p.2
      exact ⟨by omega,by omega⟩
    · obtain ⟨a,ha,h₁,h₂⟩ := frameRows pub onlineBase onlineMem online hr
      have ⟨p,t⟩ := ho a ha
      exact ⟨by omega,by omega⟩
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hr
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
      have ⟨h₁,h₂⟩ := ht p.2 (List.mem_map_of_mem hp)
      have c₁ := TerminalLink.report_probes_le addr p.1 p.2
      have c₂ := TerminalLink.report_length_le addr p.1 p.2
      have ⟨p',t'⟩ := innerBounds pub .terminal (TerminalLink.report addr p.1 p.2)
      exact ⟨by omega,by omega⟩
  refine ⟨fun r hr => (rows r hr).1,?_,fun r hr => (rows r hr).2⟩
  have init := initialCost pub src H (fun p hp => (initialRows p hp).1)
  rw [show src.length=8 from List.length_ofFn] at init
  have onlineBound := framedCost pub onlineBase onlineMem online
  have terminalBound := termCost pub addr terminal
  have size := Nat.mul_le_mul_right H hS
  change RAMBuckets.cost Report.probes ((cursorStartupSources b pub B n base startMem initial phases d).map _) ≤ 8*H at init
  simp only [rs,RAMBuckets.cost_append,cursorStartupLogs_eq]
  omega

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
