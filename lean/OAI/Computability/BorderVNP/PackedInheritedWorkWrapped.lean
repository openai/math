import OAI.Computability.BorderVNP.PackedInheritedWorkCompilationReturn

/-! # Width readback on the wrapped physical epoch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.Inherited.WorkWords
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {shape : ℕ → Shape}
    {start T t w : ℕ} {budget V E cap : ℕ → ℕ}
    {deep : S.floor+1+S.drop*T ≤ start} {ht : t<T} {endShape : shape (t+1) = ⟨V S.rounds,E S.rounds⟩}
    {nodes : ∀ i : Fin S.rounds, S.source.Node S.last (S.high (offset S start t)) V E w S.fanIn i}

/-- The assigned physical boundary pins, including the two per-site widths. -/
noncomputable abbrev OuterWidthPins (S : SiteSchedule e) (start : ℕ) (shape : ℕ → Shape) (w t : ℕ) :=
  WithWidths (Pins S start shape w t) (shape t).sites w

/-- The assigned physical pins of one source stage, including the two per-site widths. -/
noncomputable abbrev InnerWidthPins (S : SiteSchedule e) (start t : ℕ) (V E : ℕ → ℕ) (w j : ℕ) :=
  WithWidths (S.source.StatePins S.last (S.high (offset S start t)) V E w j) (V j) w

local notation "outer" => Pins S start shape w
local notation "child" => WithWidths (outer t) (Shape.sites (shape t)) w
local notation "next" => WithWidths (outer (t+1)) (Shape.sites (shape (t+1))) w
local notation "stagePins" => S.source.StatePins S.last (S.high (offset S start t)) V E w
local notation "stages" => (fun j => WithWidths (stagePins j) (V j) w)
local notation "counts" => Count S start t (fun _ => w)
local notation "admitted" => Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget)

/-- Full geometric words, live work and extent, and zeros in all vacant width slots of the
actual physical boundary state. -/
structure WidthReads (a : State S start P bits shape outer t) (programs : Site.Programs a.pack.layout)
    (z : child → Bool) : Prop where
  geometry : z ∘ Sum.inl = a.words
  covers : ∀ b, WorkWords.Covers a.rows.site
    (fun v => if b then (programs v).program.size else (programs v).program.work) (assignedColumn b) z

namespace Compilation

variable (A : Compilation (bits := bits) deep ht budget V E cap w endShape nodes)
    (preFrame : Frame (Fin (fan S) × OuterWidthPins S start shape w t) (Fin (fan S) × InnerWidthPins S start t V E w 0))
    (step : Steps S.fanIn S.rounds (InnerWidthPins S start t V E w) (Count S start t (fun _ => w)))

/-- One augmented physical step, wrapping its actual width subdivision, shared inner nodes,
and geometric return with the two retained root width columns. -/
noncomputable def widthStep : Frame ((Fin (fan S) × child) ⊕ Slot S.fanIn counts S.rounds) (Result next) :=
  wrappedEpoch (W := stages) (G := counts) preFrame step A.widthPost

/-- Exactly the subdivision gates, the inner history gates, and the original terminal placement. -/
theorem widthStep_size : (A.widthStep preFrame step).size = preFrame.size + (flatEpoch step).size + A.post.size :=
  (wrappedEpoch_size preFrame step A.widthPost).trans (congrArg (_+·) A.widthPost_size)

variable (rows : A.epoch.F.SiteRows) (number : e.Entry → ℕ)
    (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t) (old : ∀ i, Site.Programs (c i).val.pack.layout)
    (q : A.epoch.F.Hist (A.epoch.run c).flat) (x : Fin (fan S) × OuterWidthPins S start shape w t → Bool)

/-- The augmented root assignment reached by the real histogram in this wrapped step. -/
noncomputable def widthRoot : stages S.rounds → Bool := fun j => (flatEpoch (k := S.fanIn) (b := S.rounds) (W := stages) (G := counts) step).eval (Sum.elim (preFrame.eval x)
    ((A.epoch.run c).word A.epoch.room q)) (.inl j)

/-- The last inner traversal has read the whole assigned root and its true replayed programs. -/
structure RootWidthReads (y : stages S.rounds → Bool) : Prop where
  geometry : y ∘ Sum.inl = ((A.returned c).run.root q).val.words
  covers : ∀ b, WorkWords.Covers (((A.returned c).run.root q).val.names.sites)
    (fun v => let p := (A.rootPrivate rows c old number q v).program
              if b then p.size else p.work) (assignedColumn b) y

/-- The wrapped circuit on the canonical count words returns the complete boundary assignment
and both width columns on this actual physical successor. -/
theorem widthStep_read (childRead : ∀ i, WidthReads (c i).val (old i) (fun j => x (i,j)))
    (rootRead : A.RootWidthReads rows number c old q (A.widthRoot preFrame step c q x)) :
    WidthReads (A.epoch.term c q).val (A.epoch.privatePrograms rows c old number q)
      (fun j => (A.widthStep preFrame step).eval (Sum.elim x ((A.epoch.run c).word A.epoch.room q)) (.inl j)) := by
  let y := A.widthRoot preFrame step c q x
  rw [widthStep,wrappedEpoch_state]
  constructor
  · funext j
    have oldWords : (fun a : Fin (fan S) × outer t => x (a.1,.inl a.2)) = childWords c :=
      funext fun a => congrFun (childRead a.1).geometry a.2
    change A.widthPost.eval (Sum.elim x y) (.inl j) = A.post.eval
      (Sum.elim (childWords c) ((A.returned c).run.root q).val.words) j
    rw [A.widthPost_geo,oldWords,rootRead.geometry]
  · exact fun b => A.widthPost_covers rows c old number q x y b (rootRead.covers b)

end Compilation
end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
