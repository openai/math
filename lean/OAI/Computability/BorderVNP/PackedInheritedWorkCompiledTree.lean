import OAI.Computability.BorderVNP.PackedInheritedWorkWrapped
import OAI.Computability.BorderVNP.PackedInheritedWorkOuter
import OAI.Computability.BorderVNP.PackedHistoryNormalizedProcessor

/-! # The complete width-augmented tree on the selected machine's native histories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.Inherited.WorkWords EnrichedOuter
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2500000
set_option maxRecDepth 3000

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {start T w : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ}

local notation "bounds" => boundaryShape S start
local notation "outer" => Boundary.Pins S start bounds w
local notation "aug" => (fun t => WithWidths (outer t) (Shape.sites (bounds t)) w)
local notation "sites" => (fun t j => Shape.sites (before S start t j))
local notation "edges" => (fun t j => Shape.edges (before S start t j))
local notation "inner" => (fun t j => WithWidths
  (S.source.StatePins S.last (S.high (offset S start t)) (sites t) (edges t) w j) (sites t j) w)
local notation "guesses" => Machine.Guess S start (fun _ _ => w)
local notation "admitted" => Admissible (Boundary.Good (S := S) (start := start) (bits := bits) (shape := bounds) (w := w) budget)

variable (C : Compiled bits deep budget cap w)

/-- The fixed batched subdivision and width-augmented source nodes on every active processor
rectangle. The outer return uses the minimizing frame of the same compilation. -/
structure WidthFrames (C : Compiled bits deep budget cap w) where
  /-- Subdivision frame that converts the width-augmented outer children to the inner leaf inputs. -/
  pre : ∀ t, t<T → Frame (Fin (fan S) × aug t) (Fin (fan S) × inner t 0)
  /-- Crossing-round circuits on the width-augmented inner states and their count pins. -/
  innerStep : ∀ t, t<T → Steps S.fanIn S.rounds (inner t) (Count S start t (fun _ => w))

variable {C} (frames : WidthFrames C)

/-- The native width-bearing outer circuit steps. Each step is one wrapped physical epoch. -/
noncomputable def WidthFrames.steps : Steps (fan S) T aug guesses :=
  fun t ht => (C.atLevel t ht).widthStep (frames.pre t ht) (frames.innerStep t ht)

variable (rows : ∀ t ht, (C.machine t ht).F.SiteRows) (number : e.Entry → ℕ)
    (invariant : ∀ t (a : Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
      (shape := boundaryShape S start) (w := w) budget) t), Site.Programs a.val.pack.layout → Prop)

/-- Local inner readback on the actual canonical word, and the numerical or placement
invariants needed by the succeeding subdivision. -/
def WidthFrames.InnerReads : Prop :=
  ∀ t (ht : t<T) (c : Fin (fan S) → admitted t) (old : ∀ i, Site.Programs (c i).val.pack.layout)
    (y : Fin (fan S) → aug t → Bool),
    (∀ i, invariant t (c i) (old i) ∧ Boundary.WidthReads (c i).val (old i) (y i)) →
    ∀ q : (C.machine t ht).F.Hist ((C.machine t ht).run c).flat,
    let A := C.atLevel t ht
    let x := fun z : Fin (fan S) × aug t => y z.1 z.2
    invariant (t+1) (A.epoch.term c q) (A.epoch.privatePrograms (rows t ht) c old number q) ∧
    A.RootWidthReads (rows t ht) number c old q (A.widthRoot (frames.pre t ht) (frames.innerStep t ht) c q x)

private theorem transferChoice {α I : Type*} (program : α → Type*) (test : ∀ a : α, program a → I → Prop)
    {a b : ProfileSum α} (h : a=b) (p : ∀ q : b.Index, program (b.term q)) (z : b.Index → I)
    (ok : ∀ q, test (b.term q) (p q) (z q)) :
    ∀ q : a.Index, test (a.term q)
      ((Eq.mpr (congrArg (fun r : ProfileSum α => ∀ q : r.Index, program (r.term q)) h) p) q)
      (z (Equiv.cast (congrArg ProfileSum.Index h) q)) := by
  subst b; exact ok

variable {σ : Type} [Fintype σ] (base : Frame σ (Boundary.OuterWidthPins S start (boundaryShape S start) w 0)) (x : σ → Bool)
    (seed : Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
      (shape := boundaryShape S start) (w := w) budget) 0) (old : Site.Programs seed.val.pack.layout)

/-- The output of the complete augmented circuit on each native packed histogram has
exact geometry and both named widths of its actual recursively installed programs. -/
theorem WidthFrames.pack_read (startRead : invariant 0 seed old ∧ Boundary.WidthReads seed.val old (base.eval x))
    (ok : frames.InnerReads rows number invariant) (n : ℕ) (hn : n ≤ T)
    (q : (packHistory seed C.machine.epoch n).Index) :
    Boundary.WidthReads ((packHistory seed C.machine.epoch n).term q).val
      (C.machine.historyPrivatePrograms rows number seed old n hn q)
      (output frames.steps n hn (repeatLeaf (fan S) base n) x (C.machine.packBits seed n hn q)) := by
  let read t (a : admitted t) (p : Site.Programs a.val.pack.layout) (y : aug t → Bool) :=
    invariant t a p ∧ Boundary.WidthReads a.val p y
  apply (C.machine.private_pack_output seed frames.steps rows number read base x old startRead ?_ n hn q).2
  intro t ht c programs y childRead
  let E := C.machine t ht
  let test (a : admitted (t+1)) (p : Site.Programs a.val.pack.layout) (g : guesses t → Bool) :=
    read (t+1) a p (fun j => (frames.steps t ht).eval (Sum.elim (fun z => y z.1 z.2) g) (.inl j))
  have hlocal (j : E.F.Hist (E.run c).flat) :
      test (E.term c j) (E.privatePrograms (rows t ht) c programs number j) ((E.run c).word E.room j) := by
    obtain ⟨inv,root⟩ := ok t ht c programs y childRead j
    exact ⟨inv,(C.atLevel t ht).widthStep_read (frames.pre t ht) (frames.innerStep t ht) (rows t ht) number c
      programs j (fun z => y z.1 z.2) (fun i => (childRead i).2) root⟩
  have he : C.machine.epoch t c = E.choice c := dite_eq_left ht
  exact transferChoice (fun a : admitted (t+1) => Site.Programs a.val.pack.layout) test he
    (E.privatePrograms (rows t ht) c programs number) ((E.run c).word E.room) hlocal

/-- In the flattened terminal network the same site directory indexes the work and complete
extent of the true terminal program at each host, and every vacant word is zero. -/
theorem WidthFrames.terminal_read
    (startRead : invariant 0 seed old ∧ Boundary.WidthReads seed.val old (base.eval x))
    (ok : frames.InnerReads rows number invariant) (q : (packHistory seed C.machine.epoch T).Index) :
    let a := ((packHistory seed C.machine.epoch T).term q).val
    let y := output frames.steps T le_rfl (repeatLeaf (fan S) base T) x (C.machine.packBits seed T le_rfl q)
    y ∘ Sum.inl = a.words ∧ ∀ b, WorkWords.Covers a.rows.flatten.site
      (fun v => let p := (C.machine.terminalPrivatePrograms rows number seed old q v).program
                if b then p.size else p.work) (assignedColumn b) y := by
  let h := frames.pack_read rows number invariant base x seed old startRead ok T le_rfl q
  exact ⟨h.geometry,h.covers⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
