import OAI.Computability.BorderVNP.PackedFrozenTapeSave
import OAI.Computability.BorderVNP.PackedFrozenTapeRound
import OAI.Computability.BorderVNP.PackedInheritedWorkNames

/-! # Executable child history carry on the physical saved site rectangle

The public circuit is chosen before the child states and histogram. Its
only input wires are aliases for the immutable child tapes. The selected
histogram determines the actual receiving site's directory address.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open VPVNP.VerifierNetwork
open scoped Classical

variable {σ R B : Type*} [Fintype σ] [Fintype R] [Fintype B] {k s d w : ℕ}
    (oldRoom : s ≤ 2^d) (newRoom : k*s ≤ 2^w) (childPin : Fin k × Pins R B d → σ)

/-- Public gate sequence for rekeying and preserving all child tapes in one
common input array. The aliasing step has no Boolean gates. -/
noncomputable def carryFrame : Frame σ (Pins (Fin k × R) (Fin k × B) w) :=
  parallelFramePins ((exists_carry (Row := R) (Payload := B) (Fin.castLEEmb oldRoom)
    (Fin.castLEEmb newRoom)).choose.subst (Frame.initial childPin))

/-- Each child pays only its owner-key lookup. Reindexing the pins introduces
no additional gates, even when the common input also carries geometry. -/
theorem carryFrame_size :
    (carryFrame oldRoom newRoom childPin).size ≤ 1+k*lookupCost s (Fintype.card R) d w := by
  simpa only [carryFrame,parallelFramePins,Frame.select_size,Frame.subst_size,
    Frame.initial_size,Nat.zero_add] using
    (exists_carry (Row := R) (Payload := B) (Fin.castLEEmb oldRoom) (Fin.castLEEmb newRoom)).choose_spec.1

end Packing.Inherited.FrozenTape

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicParallel Shortening.StaticRows
open Epoch Epoch.Round Shortening.CombiningStep Packing Packing.Inherited Inherited.FrozenTape
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2200000

variable {D m b k last high w d : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} {path : SourcePath b e h H ν} {V E cap : ℕ → ℕ}
    {Extra : ℕ → Type*} {keep : ∀ j,path.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
    {nodes : ∀ i : Fin b,path.Node last high V E w k i} (r : path.NamedRun last high V E w cap keep hk nodes)
    (i : Fin b) (c : Fin k → NamedState.Admissible (path.NamedGood last high V E w cap keep) i.val)
    (q : (r.program.stage i c).Index e)
    {σ R B : Type*} [Fintype σ] [Fintype R] [Fintype B] (S : Schema R B)
    (oldRoom : V i.val ≤ 2^d)
    (physicalFit : siteCapacity e (k*V i.val) (Fintype.card (Shortening.PublicDenseReceipt.Seed
      (path.pattern i).bins (path.asPath.depth last high (i.val+1)))) ≤ 2^w)
    (childPin : Fin k × Pins R B d → σ) (x : σ → Bool)
    (old : ∀ j,Site.Programs (c j).val.placed.pack.layout)

local notation3 "st" => r.program.stage i c
local notation3 "seed" => (r.directorySeed i).toEmbedding
local notation3 "site₁" => siteRows e (st).input (parallelName fun j => (c j).val.names.sites) seed

include q in
set_option backward.isDefEq.respectTransparency false in
/-- Every carried row is the row of the genuine old child at the address of
the saved physical directory. The fresh sites receive empty carried sections.
The circuit and its size bound are uniform in both child choices and histogram. -/
theorem carried_tape
    (image : ∀ j : Fin k, S.Image (fun pin => x (childPin (j,pin))) ((c j).val.names.sites.trans Fin.valEmbedding)
      (fun v => (old j v).program)) :
    let newRoom := (Nat.le_add_right _ _).trans physicalFit
    (S.parallel k).Section ((carryFrame oldRoom newRoom childPin).eval x)
      ((site₁).trans ((Fin.castLEEmb physicalFit).trans Fin.valEmbedding))
      (carriedRows e (st).input (fun z => (old z.1 z.2).program)) := by
  intro newRoom
  let pass := exists_carry (Row := R) (Payload := B) (Fin.castLEEmb oldRoom) (Fin.castLEEmb newRoom)
  let frame := pass.choose
  have h := carried_section r i c q S oldRoom newRoom frame pass.choose_spec.2 (x ∘ childPin)
    (fun j v => (old j v).program) image
  have bitsEq : (carryFrame oldRoom newRoom childPin).eval x = (frame.eval (x ∘ childPin)) ∘ parallelPin := by
    funext z
    simp only [carryFrame,parallelFramePins,Frame.select_eval,Frame.subst_eval,Function.comp_apply]
    exact congrArg (fun y => frame.eval y (parallelPin z)) (funext fun _ => Frame.initial_eval _ _ _)
  have keyEq : ((r.directory i c q).sites.trans Fin.valEmbedding) =
      ((site₁).trans ((Fin.castLEEmb physicalFit).trans Fin.valEmbedding)) := by
    apply DFunLike.ext
    exact (r.directorySeed_spec i c q).1
  rw [bitsEq,← keyEq]
  exact h

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
