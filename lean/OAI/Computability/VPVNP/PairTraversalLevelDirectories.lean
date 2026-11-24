import OAI.Computability.VPVNP.PairTraversalDirectories

/-!
# Transferring physical preimage directories to the selected term chain

The shrink and refresh scanners retain their level number in the public table
layout. A directory for each selected level therefore gives the directories
of the selected chain, with the same physical old- and new-site numbering.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open CompressorRecords NetworkKernel LocalHistory Compression BurstRAM

variable {w : ℕ} {k A : Type*} [Field k] [CommRing A] {S : BlockSchedule k}
variable {B : S.Templates} {f : B.Entry → A} {hf : B.IsSolution f}

/-- The completed placement scan attached to one concrete compressor level. -/
abbrev LevelDirectory (v : SelectedLevel B f hf) (raw : Memory w) (limit : ℕ) :=
  Directory (v.pass.step.term v.term) (siteOrder v.input)
    ((v.pass.output_eq v.term).symm ▸ siteOrder (v.pass.next v.term)) raw limit

open private castOrders from OAI.Computability.VPVNP.PairTraversalSelectedOrder
open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels

omit [CommRing A] in
private def castDirectories {N M Y : Network} (h : N = M) (c : TermChain A M Y)
    (ord : ChainOrders c) (old : Order M.Site) (raw : Memory w) (limit : ℕ)
    (dirs : Directories raw limit c ord old) :
    Directories raw limit (h.symm ▸ c : TermChain A N Y) (castOrders h c ord) (h.symm ▸ old) := by
  cases h
  exact dirs

private noncomputable def collectDirectories {a g b n : ℕ} {X : State a g}
    (E : StateExecution A b n X) (W : E.MapWitnesses f) (r : ExecutionReaders E W)
    (o : PassOrigins B f hf E) (data : E.Records) (z : E.Choices) (raw : Memory w) (limit : ℕ)
    (ds : let vs := collectLevels B f hf E W r o z
      (i : Fin vs.length) → LevelDirectory vs[i] raw limit) :
    Directories raw limit (E.termChain data z) (branchOrders E data z) (siteOrder X) := by
  induction E with
  | done => exact PUnit.unit
  | more p tail ih =>
    let E' := tail z.1
    let data' := data.2 z.1
    let vs := collectLevels B f hf E' (W.2 z.1) (r.2 z.1) (o.2 z.1) z.2
    let old' := siteOrder (p.next z.1)
    let c := E'.termChain data' z.2
    let ords := branchOrders E' data' z.2
    have rest (i : Fin vs.length) : LevelDirectory vs[i] raw limit := ds i.succ
    exact ⟨ds ⟨0, Nat.zero_lt_succ _⟩, castDirectories (p.output_eq z.1) c ords old' raw limit
      (ih z.1 (W.2 z.1) (r.2 z.1) (o.2 z.1) data' z.2 rest)⟩

variable (B f hf) {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
variable (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)

/-- Transfer every indexed scan output to the corresponding DFS row worker.
Using the actual list index also covers repeated, equal level records at
different physical addresses. -/
noncomputable def selectedDirectories (raw : Memory w) (limit : ℕ)
    (ds : let vs := executeLevels B f hf T hT X z
      (i : Fin vs.length) → LevelDirectory vs[i] raw limit) :
    let E := B.execute f hf T hT X
    let data := B.records f hf T hT X
    Directories raw limit (E.termChain data z) (branchOrders E data z) (siteOrder X) :=
  collectDirectories _ _ _ _ _ _ raw limit ds

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
