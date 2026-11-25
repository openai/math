import OAI.Computability.BorderVNP.CubeLabelISABins
import OAI.Computability.BorderVNP.CubeLabelISAPass

/-! # Running the bin-directory pass with the actual incident-chain scanner -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open VPVNP.BurstRAM

/-- Cache coordinates and per-bin changes for the candidate at the current cell. -/
def Frame.bins (p : Frame) (c v : ℕ) (m : ℕ → ℕ) (es : List Incident) : PassBins where
  addr := p.cacheAddr
  before i := (p.incident c v i m es).1
  after i := (p.incident c v i m es).2

/-- Neither pass changes the fixed parameters, cell, candidate or incumbent. -/
theorem framePass_keeps (commit : Bool) :
    ∀ k ∈ params ++ [1,2,17,18], (pass commit binContrib).keeps k = true := by
  cases commit <;> decide

/-- All scored and committed bins follow a deterministic instruction sequence. -/
theorem framePass_deterministic (commit : Bool) :
    (pass commit binContrib).deterministic = true := by cases commit <;> decide

/-- The native scanner and cache updater process the ordered cable and delivery bins
using a bounded number of passes over the incidence list of this cell. -/
theorem framePass_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (commit : Bool) (p : Frame) (c v : ℕ) (s : Bank w) (m : Memory w) (es : List Incident)
    (loaded : p.loaded (.ofWords s m)) (cell : (s 1).val = c) (cand : (s 2).val = v)
    (room : ∀ i < p.Z^2+p.Z, p.room w c v i
      ((p.bins c v (readings m) es).memory commit (readings m) i) es)
    (agrees : ∀ i < p.Z^2+p.Z, p.incident c v i
      ((p.bins c v (readings m) es).memory commit (readings m) i) es = p.incident c v i (readings m) es)
    (fit : ∀ i < p.Z^2+p.Z, (p.bins c v (readings m) es).fits commit w (readings m) (s 16).val i) :
    let b := p.bins c v (readings m) es
    let G := p.Z^2+p.Z
    ∃ tr t mt, Runs pub macros (pass commit binContrib) s m tr t mt ∧
      traceCost tr ≤ G*(24*es.length+18)+2 ∧ (t 37).val = G ∧
      (t 16).val = b.total commit (readings m) (s 16).val G ∧
      readings mt = b.memory commit (readings m) G := by
  let b := p.bins c v (readings m) es
  apply pass_run pub macros commit binContrib b s m (p.Z^2+p.Z) (24*es.length+12)
    (loaded 39 (by decide)) (loaded 20 (by decide)) (by decide) _ fit
  intro i hi t mt kept idx memory
  have ready : p.ready c v i (.ofWords t mt) := by
    refine ⟨fun k hk => (congrArg Fin.val (kept k (framePass_keeps commit k
      (List.mem_append_left _ hk)))).trans (loaded k hk),?_,?_,idx⟩
    · exact (congrArg Fin.val (kept 1 (framePass_keeps commit 1 (by decide)))).trans cell
    · exact (congrArg Fin.val (kept 2 (framePass_keeps commit 2 (by decide)))).trans cand
  obtain ⟨tr,u,ru,cost,addr,old,new⟩ := binContrib_run pub macros p c v i t mt es ready
    (memory ▸ room i hi)
  rw [memory, agrees i hi] at old new
  exact ⟨tr,u,ru,cost,old,new,addr⟩

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
