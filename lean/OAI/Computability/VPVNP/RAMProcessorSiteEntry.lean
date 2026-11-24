import OAI.Computability.VPVNP.RAMProcessorSiteLoop

/-! # Native bucket entry and physical execution up to the final checks -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM RAMSerialization

variable {w p r k : ℕ}

private theorem LoopRun.weaken {T : Template p r k} {ready valid : BoundaryInvariant w p r k}
    {l next s records t native} (h : LoopRun T ready l next s records t native)
    (hgood : ∀ u ys, ready u ys → valid u ys) : LoopRun T valid l next s records t native := by
  cases native with
  | none => exact h
  | some z =>
    obtain ⟨rs,tail⟩ := z
    obtain ⟨u, ys, hready, progress, run⟩ := h
    exact ⟨u, ys, hgood u ys hready, progress, run⟩

private theorem iteration_of_entry (s : SiteTests.Snapshot w) (hd : SiteTests.entry.eval s = .dispatch) :
    SiteTests.iteration.eval s = .dispatch := by
  rw [SiteTests.entry_eval] at hd
  rw [SiteTests.iteration_eval]
  split at hd <;> rename_i h
  · split at hd <;> rename_i hstate
    · simp [h.1, hstate, (h.2 hstate).2]
    · contradiction
  · contradiction

/-- Stack-step bound from the site entry check to the final check, accounting for startup,
bounded charged calls and intervening iteration tests. -/
def siteWork (w H work : ℕ) : ℕ := 60*w+41+work+(2*H-1)*(work+(40*w+30))

theorem checkEntry_loop {T : Template p r k} {ready : Bool → BoundaryInvariant w p r k}
    {valid : BoundaryInvariant w p r k} {work : ℕ} (call : StartRuns T ready work)
    (hgood : ∀ first u ys, ready first u ys → valid u ys)
    (s : Snapshot w p r k) (records : List (WordRecord w)) (hs : ready true s records) (S v : ℕ)
    (hl : s.lower.val = v*s.publicH) (hb : s.boundary.val = (v+1)*s.publicH)
    (hc : s.cap.val = S*s.publicH) (hleft : s.siteLeft = 2*s.publicH-1) :
    ∃ t ≤ siteWork w s.publicH work, LoopRun T valid .checkEntry .finalCheck s records t
      (runSite (T.instantiate w s.pub).program s.publicFuel S s.publicH v s.tests.cut s.choices) := by
  obtain ⟨a, ha, run⟩ := checkEntry_run T s
  have hmodel := SiteTests.runSite_at_exit (T.instantiate w s.pub).program s.publicFuel S s.publicH v s.tests hl hb hc
  change runSite (T.instantiate w s.pub).program s.publicFuel S s.publicH v s.tests.cut s.choices = _ at hmodel
  rw [hmodel]
  cases hd : SiteTests.entry.eval s.tests with
  | reject =>
    rw [hd] at run
    exact ⟨_, by unfold siteWork; omega, _, _, run, reject_row T⟩
  | finish =>
    rw [hd] at run
    exact ⟨_, by unfold siteWork; omega, s, records, hgood true s records hs, Progress.nil s records, run⟩
  | dispatch =>
    rw [hd] at run
    obtain ⟨b, hbnd, hloop⟩ := first_loop call (2*s.publicH-1) s records hs hleft.le (iteration_of_entry _ hd)
    have hfull := (hloop.weaken (hgood false)).prepend run
    unfold nativeLoop at hfull
    rw [hb, hc, hleft] at hfull
    exact ⟨_, by unfold siteWork; omega, hfull⟩

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
