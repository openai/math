import OAI.Computability.BorderVNP.PackedInheritedWorkInner
import OAI.Computability.BorderVNP.PackedInheritedWorkSelectedFrames
import OAI.Computability.BorderVNP.PackedInheritedWorkOuterPorts

/-! # The physical width compiler for the entire selected processor schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.Inherited.WorkWords Packing.PhysicalEpochs EnrichedOuter
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500

variable {D m np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {start T w : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ}
variable (C : Compiled bits deep budget cap w) (p : WorkWords.Ports np) (port : P ↪ Fin np)
variable (ranges : WidthRanges S start T w)
variable (seeds : ∀ t, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S start t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
variable (number : e.Entry → ℕ) (B : ℕ)

/-- The static exterior header and the true expanded budget on a state reached by the
outer recursion. -/
def WidthInvariant (t : ℕ)
    (a : Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
      (shape := boundaryShape S start) (w := w) budget) t) (pr : Site.Programs a.val.pack.layout) : Prop :=
  (p.outer S start t).Reads a.val.pack.layout a.val.rows.site (privatePorts S port t) ∧
    SiteCap a.val.route pr.bankFields true (S.publicProgramFactor^t*B)

/-- Every wrapped selected node has the required root readback and propagates the outer
invariant. A single word bound at the full horizon pays for all internal depth budgets. -/
theorem widthFrames_innerReads (small : (PortTable.mk np port p).Widths bits w)
    (room : 2*(S.publicProgramFactor^T*B) < 2^w) :
    (C.widthFrames p ranges).InnerReads (C.privateSiteRows port seeds) number
      (WidthInvariant (S := S) (bits := bits) (budget := budget) (start := start) (w := w) p port B) := by
  intro t ht c old y child q
  let A := C.atLevel t ht
  let childB := S.publicProgramFactor^t*B
  let stageB := widthBudget S childB
  have childCaps (i) : SiteCap (c i).val.route (old i).bankFields true childB := (child i).1.2
  have childPort (i) : (p.outer S start t).Reads (c i).val.pack.layout (c i).val.rows.site
      (privatePorts S port t) := (child i).1.1
  have hB : 0 < childB :=
    (Nat.add_pos_left (by decide : 0<1) _).trans_le (childCaps ⟨0,pow_pos S.positiveFanIn _⟩ 1)
  have fits (j) (hj : j ≤ S.rounds) : 2*stageB j < 2^w :=
    (Nat.mul_le_mul_left 2 (widthBudget_horizon S B ht hj)).trans_lt room
  have leafFits : 1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) ×
      Fin (hopCount S.budget S.radius)))*childB < 2^w := by
    have h := fits 0 (Nat.zero_le _)
    simp only [stageB,widthBudget,pow_zero,one_mul] at h
    omega
  have leafBound : 1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) ×
      Fin (hopCount S.budget S.radius)))*childB ≤ stageB 0 := by
    simp only [stageB,widthBudget,pow_zero,one_mul,le_refl]
  have read := A.widthInner_read (header := p.outer S start t) (port := privatePorts S port t)
    (seedNum := seeds t) (number := number) (hv := rfl) (fit0 := ranges.initial t ht)
    (rect := width_rectangle S deep ht) (fits := ranges.successor t ht) (c := c) (old := old) (y := y)
    (bound := stageB) (B := childB) (p.outer_widths port S start small t) (fun i => (child i).2)
    childPort childCaps leafBound leafFits (fun i => widthBudget_pos S hB i.val)
    (widthBudget_step S childB) (fun i => fits _ i.isLt) q
  refine ⟨⟨?_,?_⟩,⟨read.geometry,read.widths⟩⟩
  · exact A.widthReturn_ports c q _ _ read.ports
  · have bound := A.epoch.privatePrograms_bankCap (C.privateSiteRows port seeds t ht)
      number c old true childB childCaps q
    simpa only [childB,pow_succ',Nat.mul_assoc] using bound

variable {σ : Type} [Fintype σ]
    (base : Frame σ (Boundary.OuterWidthPins S start (boundaryShape S start) w 0)) (x : σ → Bool)
    (seed : Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
      (shape := boundaryShape S start) (w := w) budget) 0) (old : Site.Programs seed.val.pack.layout)

/-- Evaluating the literal width-bearing selected tree computes the geometry and the
work or complete extent of every actual terminal site program, with zero in every hole. -/
theorem terminal_widths (small : (PortTable.mk np port p).Widths bits w)
    (room : 2*(S.publicProgramFactor^T*B) < 2^w)
    (basePorts : p.Reads seed.val.pack.layout seed.val.rows.site port)
    (baseCap : SiteCap seed.val.route old.bankFields true B)
    (baseRead : Boundary.WidthReads seed.val old (base.eval x))
    (q : (packHistory seed C.machine.epoch T).Index) :
    let a := ((packHistory seed C.machine.epoch T).term q).val
    let y := output (C.widthFrames p ranges).steps T le_rfl (repeatLeaf (fan S) base T) x
      (C.machine.packBits seed T le_rfl q)
    y ∘ Sum.inl = a.words ∧ ∀ b, WorkWords.Covers a.rows.flatten.site
      (fun v => let pr := (C.machine.terminalPrivatePrograms (C.privateSiteRows port seeds) number seed old q v).program
                if b then pr.size else pr.work) (assignedColumn b) y := by
  let inv := WidthInvariant (S := S) (bits := bits) (budget := budget) (start := start) (w := w) p port B
  have first : inv 0 seed old ∧ Boundary.WidthReads seed.val old (base.eval x) :=
    ⟨⟨basePorts,by simpa only [pow_zero,one_mul] using baseCap⟩,baseRead⟩
  exact (C.widthFrames p ranges).terminal_read (C.privateSiteRows port seeds) number inv base x seed old first
    (C.widthFrames_innerReads p port ranges seeds number B small room) q

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
