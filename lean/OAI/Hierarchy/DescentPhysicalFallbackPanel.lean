import OAI.Hierarchy.DescentIssuedFallbackPanel
import OAI.Hierarchy.DescentPrivateTreeRoutes
import OAI.Hierarchy.DescentWholeGrain
import OAI.Hierarchy.DescentCommonBlockAddress

namespace OAI
/-! # The bounded local fallback panel at the genuine flattened old stage -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments StarKeys
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)

def selectedRoot (t : Z.Fallback) : Block T.commonDepth :=
  ⟨coarseName T.commonDepth (T.code t),
    coarse_lt (n:=Z.n) T.commonDepth (T.code t) (T.codeLegal t).1 (T.codeLegal t).2.2⟩

def falls (s : Bool) (t : Z.Fallback) (e : Grain A) := Z.placement.owner s (Z.placement.contact e)=.inr t

theorem falls_home {s : Bool} {t : Z.Fallback} {e : Grain A} (live : falls A S ready Z s t e) :
    T.home (DescentIssuedFallbackPanel.endSite (W:=W) A s e)=t := by
  have atOld : DescentResetAttachments.ends
      (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)).graph s e =
      DescentIssuedFallbackPanel.endSite (W:=W) A s e := by cases s <;> rfl
  refine (congrArg T.home atOld).symm.trans ((T.attach s e).trans ?_)
  by_cases paid : DescentChosenRouter.useRotor Z.placement.b Z.placement.depth Z.placement.L
      Z.placement.keys Z.placement.hub Z.placement.old e
  · simp [falls,Placement.owner,Placement.contact,DescentChosenRouter.contact,DescentChosenRouter.owner,paid] at live
  · cases s <;> simpa [falls,Placement.owner,Placement.contact,DescentChosenRouter.contact,
      DescentChosenRouter.owner,paid,DescentChosenRouter.pair] using live

theorem falls_parameters {s : Bool} {t : Z.Fallback} {e : Grain A} (live : falls A S ready Z s t e) :
    (A.pos (DescentIssuedFallbackPanel.endSite (W:=W) A s e)).2=frame.host.symm (T.code t).1 ∧
      group T.commonDepth (rearrange frame.basis (oldBlock digits (home A (DescentIssuedFallbackPanel.endSite (W:=W) A s e)))) =
        (selectedRoot A S ready Z T t).val := by
  have same:=falls_home A S ready Z T live
  rw [←same]
  constructor
  · apply frame.host.injective
    rw [Equiv.apply_symm_apply]
    exact (frame.homeHost _).symm
  · exact (frame.homeHigh _).symm

def fallbackPanel (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (digits : Block m ≃ J × Block k) (native : W.graph.Edge ↪ ℕ)
    (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht)
    (T : ResetInput.Terminals (F:=F) Z)
    (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
      (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
    (s : Bool) (t : Z.Fallback) :
    Fin (2^(m-T.commonDepth)) × Fin (2*A.cap) → Option (Grain A) :=
  DescentIssuedFallbackPanel.panel A native S ready digits frame.basis (frame.enough.trans (Nat.sub_le m g)) s
    (frame.host.symm (T.code t).1)
    (selectedRoot A S ready Z T t) (falls A S ready Z s t)

theorem fallbackPanel_at (s : Bool) (t : Z.Fallback) (e : Grain A) (live : falls A S ready Z s t e) :
    fallbackPanel A S ready digits native Z T frame s t
      (localAddress (c:=T.commonDepth) A native S ready digits frame.basis s e)=some e :=
  DescentIssuedFallbackPanel.panel_at A native S ready digits frame.basis (frame.enough.trans (Nat.sub_le m g)) s
    (frame.host.symm (T.code t).1) (selectedRoot A S ready Z T t) (falls A S ready Z s t)
    (fun _ ok=>falls_parameters A S ready digits Z T frame ok) e live

theorem fallbackPanel_sound {s : Bool} {t : Z.Fallback} {j} {e : Grain A}
    (hit : fallbackPanel A S ready digits native Z T frame s t j=some e) :
    falls A S ready Z s t e ∧ j=localAddress (c:=T.commonDepth) A native S ready digits frame.basis s e :=
  DescentIssuedFallbackPanel.panel_sound A native S ready digits frame.basis (frame.enough.trans (Nat.sub_le m g)) s
    (frame.host.symm (T.code t).1) (selectedRoot A S ready Z T t) (falls A S ready Z s t) hit

set_option maxHeartbeats 1000000 in
theorem fallbackPanel_count (s : Bool) (t : Z.Fallback) (test : Grain A→Bool) :
    (Finset.univ.filter (fun j=>(fallbackPanel A S ready digits native Z T frame s t j).any test)).card=
      (Finset.univ.filter (fun e=>falls A S ready Z s t e ∧ test e)).card :=
  DescentIssuedFallbackPanel.count A native S ready digits frame.basis (frame.enough.trans (Nat.sub_le m g)) s
    (frame.host.symm (T.code t).1) (selectedRoot A S ready Z T t) (falls A S ready Z s t)
    (fun _ ok=>falls_parameters A S ready digits Z T frame ok) test

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
