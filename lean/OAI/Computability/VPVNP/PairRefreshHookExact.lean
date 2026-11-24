import OAI.Computability.VPVNP.PairRefreshHookPath
import OAI.Computability.VPVNP.PairRefreshTraversalQuiet

/-!
# Exact hook at a selected native refresh row

The popped node identifies the resident row. Its typed newer half is already
in private memory. The role consumes exactly the bits of its independent older
half, then executes the selected diagonal and motif. A short half rejects in
the field loader. An incompatible complete pair rejects in the map body, even
with additional choices available to the continuation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.Site

open BurstRAM PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh CompressorRecords CompressorRecords.PortRefresh
open NodeArguments NodeArguments.ChildScan VertexImage DFS
open CompressorRecords.PortRefresh.NewSlots

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {bits n hist t pcs regs : ℕ}
  (R : Site B n hist bits) (ties : Fin t ≃ Tie (2^S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
  (loc : Fin (RefreshVertex.refreshSegment B ties stride order).count → Fin pcs)
  (dfs : Fin 9 ↪ Fin regs) (saved : Saved ↪ Fin regs)
  (reg : Fin (RefreshVertex.refreshSegment B ties stride order).privateRegs ↪ Fin regs) (done : Fin pcs)
  (M : Machine bits pcs regs 11) (m : Memory bits)

local notation "segment" => RefreshVertex.refreshSegment B ties stride order
local notation "act" => R.action ties stride order M.publicData m
local notation "read" => R.read ties stride order M.publicData m

/-- The fields used by the refresh row at entry to the DFS role. -/
def At (node : BurstRAM.Word bits) (c : Config bits pcs regs) : Prop :=
  c.pc = loc (segment).entry ∧ c.reg (dfs 7) = node ∧ c.reg (dfs 6) = word n ∧ R.Prepared node (scratch n c.privateMem)

private theorem quiet (x z s es next) (h : act x z s = some (es,next)) : choiceBits es = [] :=
  TraversalPlan.canonicalAction_noChoices B ties stride order R.state R.choice R.port R.degree n R.rowEnd
    R.oldNode R.parent R.room x z m (TraversalControllerInputs.levelHead M.publicData m R.level).val
    (TraversalControllerInputs.levelHead M.publicData m (R.level+1)).val R.geometry h

variable (installed : ∀ i, M.code (loc i) = ((RefreshVertex.refreshSegment B ties stride order).row loc dfs saved reg done i).resize bits)
  (apartD : ∀ i j, reg i ≠ dfs j) (apartS : ∀ i j, reg i ≠ saved j)
  (facts : R.Published ties stride M.publicData m)

include installed apartD apartS facts in
set_option maxHeartbeats 1500000 in
theorem site_realizes :
    ShrinkRole.Realizes read M m dfs (R.At ties stride order loc dfs) (fun _ _ out => out.pc = done) := by
  apply RefreshHook.realizes R.state R.olderSite R.nextState R.newerSite R.arena R.oldNode R.parent
    (R.front M.publicData m) act (R.front_choices M.publicData m) (R.quiet ties stride order M m)
    M m dfs (R.At ties stride order loc dfs) done
  · intro node c hc
    obtain ⟨new,stored⟩ := hc.2.2.2.2.2
    have pos : 0 < bits := by
      have hw := facts.wide
      have positive := Nat.two_pow_pos S.portExponent
      by_contra! hn
      have hz : bits=0 := by omega
      rw [hz,pow_zero] at hw
      omega
    exact ⟨new,RefreshHalfDecoder.parent_eq R.nextState R.newerSite R.arena R.parent _ new stored pos⟩
  · intro node c bs hc hs
    exact R.short_path ties stride order loc dfs saved reg done M m installed facts c hc.1
      ((congrArg Fin.val hc.2.1).trans hc.2.2.2.1) bs hs
  · intro node c x z tail hc hp ha
    have path := R.action_path ties stride order loc dfs saved reg done M m installed apartD apartS facts
      node c hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 x z hp
    dsimp only at path
    rw [ha] at path
    exact path tail
  · intro node c x z es next hc hp ha
    have path := R.action_path ties stride order loc dfs saved reg done M m installed apartD apartS facts
      node c hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 x z hp
    dsimp only at path
    rw [ha] at path
    obtain ⟨out,hpc,frame,upper,pathToExit,_⟩ := path
    exact ⟨out,hpc,frame,upper,pathToExit⟩

include installed apartD apartS facts in
/-- The actual instruction table realizes the local parser for every
private tape on the selected refresh row, including failure on short and
incompatible inputs. A successful parse returns its untouched suffix. -/
theorem site_exact :
    (R.hook ties stride order M.publicData m).ExactOn R.Prepared M (loc (segment).entry) done dfs m := by
  apply (R.site_realizes ties stride order loc dfs saved reg done M m installed apartD apartS facts).exactOn
  · intro node s bs out rest _ parsed
    exact RefreshHook.splits R.state R.olderSite R.nextState R.newerSite R.arena R.oldNode R.parent
      (R.front M.publicData m) act (R.front_choices M.publicData m) (R.quiet ties stride order M m)
      node s bs out rest parsed
  · intro node c top pending dom entry
    exact ⟨entry.pc,entry.nodeWord,entry.endWord,dom⟩

end PairSimulation.RefreshHook.Site

end VPVNP
end Computability
end OAI
