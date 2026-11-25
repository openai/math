import OAI.Computability.BorderVNP.FiniteEvaluatorCubeGroupLow
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleBoot

/-! # Original geometry through the complete native field traversal

Every actual private role trace preserves the packed words below its subtotal.
The complete owned-group program writes the physical vertex count at frame
slot 46. The preceding fixed deck installer writes above the entire input.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeTriple

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.TeamRows BorderVNP.Cube.Padding.Banks
open BorderVNP.Cube.TeamRowSources BorderVNP.Cube.Tally VPVNP.BurstRAM RoutingISA
open DiagonalTallyPacketEmit (Frame)
open private low_banks from OAI.Computability.BorderVNP.FiniteEvaluatorCubeGroupLow
open private setup_transfer from OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleBoot
open private detOfUnsigned from OAI.Computability.BorderVNP.CubeISALocalRowFrame

variable {w n blocks b h K s : ℕ} {l : TeamRowPrepare.Layout} {A : Data n l.d blocks b h K s}
variable {owner : Fin l.d → ℕ} {power base stop actual claimed : ℕ} {rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ}
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {original mt : Memory w} {r t : Bank w} {es : List (TeamRAM.Event w)}
variable (P : PhysicalSetup A owner power base stop actual claimed rows pub original)

include P in
/-- Every returning traversal retains all original geometry below its local
subtotal, except the genuine final store of the vertex count. -/
theorem native_return_low (run : Runs pub mac (ownedGroups n b h K s) r original es t mt) :
    ∀ a < actual, a ≠ l.frame+46 → mt a=original a := by
  let J (mem : Memory w) := ∀ a < actual, mem a=original a
  obtain ⟨H,_,_,before,finish⟩ := native_return_induction P J (fun _ _ => rfl)
    (fun v _ _ _ _ _ own same cur prep role old a low => (role_low P v own same cur prep role a low).trans (old a low)) run
  intro a low distinct
  rw [finish]
  exact (publishVertexCount_other _ _ _ _ distinct).trans (before a low)

variable {F : Type*} [Fintype F] (table : TableEntry n b h K s → F) (f : Frame) (fresh : ℕ)
local notation "ptr" => CubeConstants.idBase fresh n b h K s

include P in
/-- The original geometric word is unchanged through both the fixed table
initializer and the entire variable-length private traversal on every return. -/
theorem install_groups_low
    (place : deckStart l power n stop ≤ fresh)
    (address : CubeConstants.arenaEnd fresh (CubeDeck.entry table)<2^w)
    (wide : CubeDeck.minimumWidth F n b h K s ≤ w)
    (fields : CubeConstants.Fields (CubeConstants.inArena f fresh n b h K s) (pub 0).val ptr (readings original))
    (run : Runs pub mac (installGroups table) r original es t mt) :
    ∀ a < actual, a ≠ l.frame+46 → mt a=original a := by
  obtain ⟨_,_,u,start,_,_,installed,⟨groups⟩,_,same⟩ := install_groups_sound P table f fresh place address wide fields run
  have across := native_return_low (setup_transfer P same) groups.runs
  obtain ⟨low,pack,single⟩ := low_banks P
  have stopLe : stop ≤ fresh := (le_max_left ..).trans place
  have baseLe : base ≤ stop := (Nat.le_add_right ..).trans P.capacity
  have room : (pub 0).val+112 ≤ fresh := by
    change readings pub 0+112 ≤ fresh
    rw [P.seed.frame]
    exact P.allocation.frame.trans (pack.trans (single.trans (baseLe.trans stopLe)))
  obtain ⟨_,_,_,boot,_,_,keep,_⟩ := CubeDeck.install_run table f fresh pub mac r original room address wide fields
  obtain ⟨_,_,rfl⟩ := installed.unique_of_deterministic (detOfUnsigned _ (CubeConstants.install_unsigned _).1) boot
  intro a ha ne
  exact (across a ha ne).trans (keep a (ha.trans_le (low.trans (pack.trans (single.trans (baseLe.trans stopLe))))))

end FiniteEvaluator.CubeTriple

end BorderVNP
end Computability
end OAI
