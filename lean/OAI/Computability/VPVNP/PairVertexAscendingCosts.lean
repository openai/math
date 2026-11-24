import OAI.Computability.VPVNP.PairVertexOrdinalPhase

/-! # Occurrence-specific bounds on the physical ordinal report sequence -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM CompressorRecords TerminalLink NetworkKernel LocalHistory
open scoped Fin.CommRing
open private closedRun closedRun_cons from OAI.Computability.VPVNP.PairVertexAscendingPaths

variable {w n g fuel base grammar : ℕ} {D : IndexedSites n g} {C : Type*} {P : BurstRAM.Program w C}
    {pub : Fin 11 → Word w} {Frame : ℕ → Memory w → Prop}

private theorem checked_suffix (H : ActiveCalls D P fuel base grammar Frame) (close : Closes P fuel n pub Frame)
    (ok : (i : Fin n) → D.Choice i → Report w → Prop)
    (check : ∀ i m, Frame i.val m → ∀ x r,
      execute P fuel (P.start (i.val : Word w)) m (D.encode i x) = some r → ok i x r)
    {k start : ℕ} (site : Fin k → Fin n) (aligned : ∀ i, (site i).val=start+i.val) (ending : start+k=n)
    (m : Memory w) (hm : Frame start m) (x : ∀ i, D.Choice (site i)) :
    let last := Counters.visit base grammar id (List.ofFn fun i => D.powers (site i) (x i)) m
    ∃ reps : Fin k → Report w, (∀ i, ok (site i) (x i) (reps i)) ∧
      closedRun P fuel start m ((List.ofFn fun i => D.encode (site i) (x i)) ++ [[]])
        (List.ofFn reps ++ [closingReport pub last]) last := by
  induction k generalizing start m with
  | zero =>
    simp only [Nat.add_zero] at ending
    subst start
    have call := close m hm []
    simp only [ite_true] at call
    refine ⟨Fin.elim0,fun i => Fin.elim0 i,?_⟩
    simp [closedRun,runSegment,call,endState,eventLog,Counters.visit,closingReport_after]
    rfl
  | succ k ih =>
    have hz : (site 0).val = start := by simpa using aligned 0
    obtain ⟨head,call,next,mem⟩ := H.emit (site 0) m (hz ▸ hm) (x 0)
    have good := check (site 0) m (hz ▸ hm) (x 0) head call
    have keep := H.preserve (site 0) m (hz ▸ hm) (x 0)
    rw [hz,←mem] at keep
    rw [hz] at call next
    obtain ⟨tail,ht,run⟩ := ih (fun i => site i.succ)
      (fun i => by rw [aligned,Fin.val_succ]; omega) (by omega) (after m head.events) keep (fun i => x i.succ)
    refine ⟨Fin.cons head tail,Fin.cases good (fun j => ht j),?_⟩
    simp only [List.ofFn_succ,List.cons_append,Fin.cons_zero,Fin.cons_succ,Counters.visit,List.foldl_cons,id_eq]
    rw [←mem]
    exact closedRun_cons call next run

/-- The exact emitted list can be indexed by its natural ordinal, so the
cost certificate for each report can depend on that very site's occurrence. -/
theorem ascending_checked (H : ActiveCalls D P fuel base grammar Frame) (close : Closes P fuel n pub Frame)
    (ok : (i : Fin n) → D.Choice i → Report w → Prop)
    (check : ∀ i m, Frame i.val m → ∀ x r,
      execute P fuel (P.start (i.val : Word w)) m (D.encode i x) = some r → ok i x r)
    (m : Memory w) (hm : Frame 0 m) (x : ∀ i, D.Choice i) :
    ∃ reps : Fin n → Report w, (∀ i, ok i (x i) (reps i)) ∧ runSegment P fuel (some 0) m (D.calls x) =
      some (List.ofFn reps ++ [closingReport pub (D.finalMemory base grammar m x)]) := by
  obtain ⟨reps,h,run⟩ := checked_suffix H close ok check id (fun _ => by simp) (Nat.zero_add n) m hm x
  exact ⟨reps,h,by simpa only [Nat.cast_zero,id_eq,IndexedSites.calls,IndexedSites.finalMemory] using run.1⟩

variable {R : Type*} [CommRing R] {Label : Type} [Fintype Label] {κ : Label → R} {N : Network}
    (parsers : SiteParsers κ N) (order : Fin n ≃ N.Site) (names : Fin g ≃ Label) (half : ∀ v, N.Half v)
    (F : DescriptorSpace.Shape) (limit : ℕ) {geometry rootFields leaf shrink refresh : Segment}
    (src phy : Memory w)
local notation "site" => siteOrdinals parsers order names half
local notation "body" => segments geometry rootFields leaf shrink refresh
local notation "worker" => Machine.program (Template.instantiate (template body) w pub)

/-- The completed physical vertex block contains exactly the same reports
as the ordinal-indexed source workers, plus their terminal guard. -/
theorem physicalSite_rows (native : ActiveCalls site worker fuel base grammar Frame) (clock : 15 ≤ fuel)
    (ready : Frame 0 src) (stored : ∀ m, Frame n m → m (TerminalSiteStart.headerWord pub+7).val = (n : Word w))
    (transport : WorkerFrame (TerminalProgram.workers F limit body) pub fuel (.resume Stage.vertices 0) src phy)
    (x : ∀ v, (parsers.witnesses v (half v)).Choice)
    (ok : N.Site → Report w → Prop)
    (check : ∀ i m, Frame i.val m → ∀ (c : (site).Choice i) r,
      execute worker fuel ((worker).start (i.val : Word w)) m ((site).encode i c) = some r → ok (order i) r) :
    let block := sitePhysical parsers order names half F limit src phy native clock ready stored transport x
    ∃ reps : N.Site → Report w, (∀ v, ok v (reps v)) ∧ block.val.logs.map Prod.snd =
      (List.ofFn fun i => reps (order i)) ++ [closingReport pub ((site).finalMemory base grammar src (fun i => x (order i)))] := by
  intro block
  let p := sitePathsEquiv parsers order names half native clock stored src ready x
  obtain ⟨reps,checked,run⟩ := ascending_checked native (template_closes clock stored)
    (fun i _ r => ok (order i) r) check src ready (fun i => x (order i))
  have eqn := Option.some.inj (p.property.choose_spec.1.symm.trans run)
  refine ⟨fun v => reps (order.symm v),fun v => by simpa only [Equiv.apply_symm_apply] using checked (order.symm v),?_⟩
  change (stageLogs (.resume Stage.vertices 0) p.property.choose).map Prod.snd = _
  exact (stageLogs_raw _ _).trans (eqn.trans (by simp only [Equiv.symm_apply_apply]))

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
