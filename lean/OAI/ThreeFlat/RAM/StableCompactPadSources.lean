import Batteries.Tactic.OpenPrivate
import OAI.ThreeFlat.RAM.StableCompactPadProgram
import OAI.ThreeFlat.RAM.ContractionMemory
import OAI.ThreeFlat.Routing.StableCompactionPadRows

namespace OAI
/-! # Physical addresses of pin-restricted compaction cells -/

namespace ThreeFlat.RAM.StableCompactPadSources

open BitLayout BitNetwork Routing.StableCompaction StableCompactPadProgram
open private mapSource from OAI.ThreeFlat.BitNetwork.PinMap
open private paddingPins shortRow from OAI.ThreeFlat.Routing.StableCompactionPadRows

/-- Shortening the three boundary banks changes every cell source by precisely
the same address computation as the compiled metadata term. -/
theorem sourceAddress_restrictRows {F : Type*} {N : ℕ} (B : BitNetwork F (N+(N+N)))
    (n : ℕ) (hn : n ≤ N) (i : Fin B.cells) (j : Fin 3) :
    sourceAddress ((restrictRows B n).source i j) = remap N n (sourceAddress (B.source i j)) := by
  simp only [restrictRows,BitNetwork.restrictPins]
  cases h : B.source i j with
  | constant b =>
    exact (remap_constant N n b.toNat (by cases b <;> decide)).symm
  | hidden v =>
    simpa only [mapSource,sourceAddress,hiddenBase,show N+(N+N)=3*N by omega,
      show n+(n+n)=3*n by omega] using (remap_hidden N n v.val hn).symm
  | pin x =>
    refine Fin.addCases (fun v => ?_) (Fin.addCases (fun v => ?_) (fun v => ?_)) x
    all_goals
      by_cases hv : v.val < n <;>
        simp only [mapSource,paddingPins,Fin.append_left,Fin.append_right,shortRow,hv,↓reduceDIte,
          Option.map_some,Option.map_none,sourceAddress,Fin.val_castAdd,Fin.val_natAdd,Bool.toNat_false]
      all_goals first
        | simpa [hv,add_assoc] using (remap_pin N n 0 v hn).symm
        | simpa [hv,add_assoc] using (remap_pin N n 1 v hn).symm
        | simpa [hv,two_mul,add_assoc] using (remap_pin N n 2 v hn).symm

end ThreeFlat.RAM.StableCompactPadSources

end OAI
