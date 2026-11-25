import OAI.Computability.BorderVNP.PackedTerminalSelection
import OAI.Computability.BorderVNP.ShortenDenseExecution

/-!
# Executable terminal rounding on a calibrated dense epoch

The schedule supplies the finite terminal catalog, motions and level drop.
The same Boolean frame works on every terminal histogram. Its selected
motion realizes the calibrated site expansion and its returned sparse rows
are exactly the input format of the next epoch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SiteSchedule

open Shortening Shortening.Adaptive Epoch Cover Crossing Terminal Shortening.PublicSegments
open VPVNP.VerifierNetwork (Frame)
open scoped Classical
attribute [local instance] BorderVNP.Epoch.Round.portFintype

variable {D m q : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}
  (S : SiteSchedule e) (enum : Fin q ≃ Cube D)

/-- All columns of a public terminal pass are certified on every occupied
input assignment of the schedule's last catalog. -/
def TerminalFrame {Data : Type} [Fintype Data] (d V E w : ℕ)
    (field : FieldBit (↥(S.source.catalog S.rounds)) (Cube D) (S.level d S.rounds+1) → Data)
    (f : Frame (Terminal.Input Data V E w) (Selected D S.motions ↥(allowedMoves (Cube D) S.budget) q (d+2) V E w)) : Prop :=
  ∀ {P : Type} {bits : P → ℕ} {p : PlacedPack D P bits K (Cube D) (S.level d S.rounds)}
    (dir : Directory p V E) (x : Terminal.Input Data V E w → Bool), dir.Reads (S.source.catalog S.rounds) field x →
    ∃ σ, S.Minimizes p σ ∧ (∀ τ, f.eval x (.inl τ) = decide (τ=σ)) ∧
      CandidateRows enum (S.finish_level d) (fun i => S.clears (σ i)) dir S.budget (f.eval x ∘ Sum.inr)

/-- A single nearly linear gate bound covers all terminal packs in all epochs
of the fixed schedule, including the full occupied and move rows. -/
theorem terminal_frames : ∃ G k : ℕ, ∀ {Data : Type} [Fintype Data] (d V E w : ℕ)
    (field : FieldBit (↥(S.source.catalog S.rounds)) (Cube D) (S.level d S.rounds+1) → Data), V ≤ 2^w →
    ∃ f, S.TerminalFrame enum d V E w field f ∧ f.size ≤ (V+E+1)*G*(d+w+Nat.clog 2 (V+2*E+1)+3)^k := by
  obtain ⟨Cs,ks,Cm,km,h⟩ := selected_frames enum (S.source.catalog S.rounds) S.budget S.clears S.hasMotion
  obtain ⟨G,k,hbound⟩ := TerminalArgmin.whole_cost_le ↥(allowedMoves (Cube D) S.budget)
    (Fintype.card (Cube D → Fin S.motions)) q Cs ks Cm km
  refine ⟨G,k,?_⟩
  intro Data _ d V E w field fit
  obtain ⟨f,hf,hr⟩ := h d (S.level d S.rounds) (S.finish_level d) field V E w fit
  exact ⟨f,fun dir x hx => hr dir x hx,hf.trans (hbound d V E w)⟩

variable {S enum} {d V E w : ℕ} {Data : Type} [Fintype Data]
  {field : FieldBit (↥(S.source.catalog S.rounds)) (Cube D) (S.level d S.rounds+1) → Data}
  {f : Frame (Terminal.Input Data V E w) (Selected D S.motions ↥(allowedMoves (Cube D) S.budget) q (d+2) V E w)}
  {P : Type} [Fintype P] {bits : P → ℕ} {M : SiteMachine S d P bits}

/-- The selected rows on the actual enumerated output, after flattening its
external port labels, satisfy the complete next-epoch input contract. -/
theorem TerminalFrame.returnedRows (cert : S.TerminalFrame enum d V E w field f)
    {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
    {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget} (run : SiteExecution S M input route)
    (j : Fin run.expansion.terms) (dir : Directory (M.F.terminal run.flat (run.enum j)) V E)
    (x : Terminal.Input Data V E w → Bool) (reads : dir.Reads (S.source.catalog S.rounds) field x)
    (selected : f.eval x (.inl (run.selected (run.enum j))) = true) :
    RouteRows.Ready enum (run.expansion.pack j) (run.expansion.routes j)
      (boundaryRows dir).flatten dir.dummy (f.eval x ∘ Sum.inr) := by
  obtain ⟨σ,_,flags,rows⟩ := cert dir x reads
  have heq : run.selected (run.enum j) = σ := of_decide_eq_true ((flags _).symm.trans selected)
  subst σ
  apply RouteRows.Ready.flatten
  exact rows.ready (run.out (run.enum j)).routes (run.origins (run.enum j))
    (run.charges (run.enum j)) (run.first (run.enum j))

end PackedHistoryCircuit.Normalized.SiteSchedule

end BorderVNP
end Computability
end OAI
