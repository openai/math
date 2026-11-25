import OAI.Computability.BorderVNP.PackedFrozenSelectedSchemas
import OAI.Computability.BorderVNP.PackedInheritedWorkWrapped

/-! # Returning the complete frozen root tape through a physical epoch

The selected minimizing frame already returns the geometry and the two
site-width columns. Aliasing the full root tape adds no gates and forwards
its row flags, sparse site IDs, and immutable public field bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.ProgramSchemas

open VPVNP.VerifierNetwork

variable {k : ℕ} {X Y Z OldTape RootTape : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype OldTape] [Fintype RootTape] (post : Frame ((Fin k × X) ⊕ Y) Z)

/-- Apply the existing return on its geometric and width pins and forward the root's frozen tape. -/
noncomputable def forwardRoot :
    Frame ((Fin k × (X ⊕ OldTape)) ⊕ (Y ⊕ RootTape)) (Z ⊕ RootTape) :=
  let select := Sum.map (fun a : Fin k × X => (a.1,.inl a.2)) (Sum.inl : Y → Y ⊕ RootTape)
  (post.subst (Frame.initial select)).withInput.select (Sum.elim Sum.inr (fun t => .inl (.inr (.inr t))))

/-- The complete tape is forwarded by wiring from the already computed root state. -/
theorem forwardRoot_size : (forwardRoot (OldTape:=OldTape) (RootTape:=RootTape) post).size = post.size := by
  simp [forwardRoot]

variable (x : Fin k × (X ⊕ OldTape) → Bool) (y : Y ⊕ RootTape → Bool)

/-- The computed geometry and widths use the original return's input fields. -/
theorem forwardRoot_post (z : Z) : (forwardRoot post).eval (Sum.elim x y) (.inl z) =
    post.eval (Sum.elim (fun i => x (i.1,.inl i.2)) (y ∘ Sum.inl)) z := by
  have eqn : (Frame.initial (Sum.map (fun a : Fin k × X => (a.1,.inl a.2)) (Sum.inl : Y → Y ⊕ RootTape))).eval
      (Sum.elim x y) = Sum.elim (fun i => x (i.1,.inl i.2)) (y ∘ Sum.inl) := by
    funext a; cases a <;> simp
  simp [forwardRoot,eqn]

/-- Every owner, enable, and scalar pin is read from the attained root with the very same index. -/
theorem forwardRoot_tape (j : RootTape) : (forwardRoot post).eval (Sum.elim x y) (.inr j) = y (.inr j) := by
  simp [forwardRoot]

end Packing.Inherited.FrozenTape.ProgramSchemas

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity Packing Inherited FrozenTape
open ProgramSchemas EnrichedOuter VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {start T w : ℕ}
    {deep : S.floor+1+S.drop*T ≤ start} {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ}
    (C : Compiled bits deep budget cap w) (base : FrozenTape.Format) (t : ℕ) (ht : t<T)
local notation3 "outer" => ProgramSchemas.outerPins S start w base
local notation3 "stage" => ProgramSchemas.stagePins S start w base t
local notation3 "counts" => Count S start t (fun _ => w)

/-- The actual selected post-frame, preserving the cumulative root schema through the outer return. -/
noncomputable def tapePost : Frame ((Fin (fan S) × outer t) ⊕ stage S.rounds) (outer (t+1)) :=
  forwardRoot (C.atLevel t ht).widthPost

/-- The cost of the complete terminal return is just the existing minimizing geometry pass. -/
theorem tapePost_size : (tapePost C base t ht).size = (C.atLevel t ht).post.size :=
  (forwardRoot_size _).trans (C.atLevel t ht).widthPost_size

variable (pre : Frame (Fin (fan S) × ProgramSchemas.outerPins S start w base t)
      (Fin (fan S) × ProgramSchemas.stagePins S start w base t 0))
    (nodes : Steps S.fanIn S.rounds (ProgramSchemas.stagePins S start w base t) (Count S start t (fun _ => w)))

/-- The batched preparation on all real outer children and the complete inner tree run on the
same histogram. The return then keeps the root tape of this actual epoch. -/
noncomputable def tapeStep : Frame ((Fin (fan S) × outer t) ⊕ Slot S.fanIn counts S.rounds) (Result (outer (t+1))) :=
  wrappedEpoch (k := S.fanIn) (b := S.rounds) (X := Fin (fan S) × outer t) (V := outer (t+1))
    (W := ProgramSchemas.stagePins S start w base t) (G := counts) pre nodes (tapePost C base t ht)

/-- The actual gate lists of the three passes, with zero overhead for passing immutable records. -/
theorem tapeStep_size :
    (tapeStep C base t ht pre nodes).size = pre.size + (flatEpoch nodes).size + (C.atLevel t ht).post.size :=
  (wrappedEpoch_size (k := S.fanIn) (b := S.rounds) (X := Fin (fan S) × outer t) (V := outer (t+1))
    (W := ProgramSchemas.stagePins S start w base t) (G := counts) pre nodes (tapePost C base t ht)).trans (congrArg (_+·) (tapePost_size C base t ht))

variable (x : Fin (fan S) × ProgramSchemas.outerPins S start w base t → Bool)
    (guess : Slot S.fanIn (Count S start t (fun _ => w)) S.rounds → Bool)

/-- Every public tape pin of the saved boundary is the same pin of the chosen inner root. -/
theorem tapeStep_read (i : FrozenTape.Pins (ProgramSchemas.epoch S start w base (t+1)).Rows
    (ProgramSchemas.epoch S start w base (t+1)).Payload w) :
    (tapeStep C base t ht pre nodes).eval (Sum.elim x guess) (.inl (.inr i)) =
      (flatEpoch nodes).eval (Sum.elim (pre.eval x) guess) (.inl (.inr i)) := by
  have read := congrFun (wrappedEpoch_state (k := S.fanIn) (b := S.rounds) (X := Fin (fan S) × outer t)
    (V := outer (t+1)) (W := ProgramSchemas.stagePins S start w base t) (G := counts)
    pre nodes (tapePost C base t ht) x guess) (.inr i)
  exact read.trans (forwardRoot_tape _ _ _ _)

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
