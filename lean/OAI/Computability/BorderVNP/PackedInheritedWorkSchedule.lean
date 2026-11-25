import OAI.Computability.BorderVNP.PackedInheritedWorkJointImage

/-! # The work kernel on the scheduled successor rectangle -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Shortening.StaticRows Shortening.PublicParallel Shortening.PublicEndpoints
open Epoch Epoch.Round Cover PackedHistoryCircuit PackedHistoryCircuit.Normalized InheritedBank
open VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

variable {D m k V V' E n np w : ℕ} [NeZero D] {K : Type} [Field K]
variable (e : PaidIdentity K D m) {A B Old : Type} [Fintype A] [Fintype B] [Fintype Old]
variable (seed : A ↪ Fin n) (p : Ports np) (eq : V' = siteCapacity e (k*V) n) (fit : V' ≤ 2^w)
variable (geom : Frame ((Fin k × Old) ⊕ (A × Fin e.count × Fin w)) (SavedPins B V' E w ⊕ Unit))

/-- Compile the literal selected stage on its prescribed source-path
rectangle, retaining both site-width words in its output. -/
noncomputable def jointAt : Frame (WidthInput Old A k V e.count w) (WithWidths (SavedPins B V' E w) V' w ⊕ Unit) := by
  subst V'
  exact jointNode (k := k) (V := V) (E := E) (w := w) (B := B) (Old := Old) e seed (p.parallel k V).host (p.parallel k V).width fit geom

variable {d lev : ℕ} {Bin P : Type} [Fintype Bin] [Fintype P] {bits : P → ℕ}
variable {child : Fin k → PlacedPack D P bits K (Cube D) d}
variable (s : Stage m Bin lev child) (q : s.Index e) (old : ∀ i, Site.Programs (child i).pack.layout)
variable (names : ∀ i, (child i).pack.layout.Site ↪ Fin V) (pdir : Directory (s.result e q) V' E)
local notation3 "Seeds" => ((Cube D → Deck (lev+1)) × Bin)
variable (code : ((Cube D → Deck (lev+1)) × Bin) ↪ Fin n) (port : P ↪ Fin np)
variable (binName : ((Cube D → Deck (lev+1)) × Bin) → ℕ) (position : e.Entry → ℕ)
local notation3 "next" => s.privatePrograms e q old pdir.sites pdir.cables (Parallel.portRows k port) binName position
local notation3 "saved" => ((s.result e q).dense pdir.cables).pack.layout
variable (kernel : Frame ((Fin k × Old) ⊕ (((Cube D → Deck (lev+1)) × Bin) × Fin e.count × Fin w)) (SavedPins B V' E w ⊕ Unit))
variable (y : Fin k → WithWidths Old V w → Bool) (room : ∀ t, s.matched t < 2^w)
local notation3 (prettyPrint := false) "guess" => NamedReceipt.word s room q
local notation3 (prettyPrint := false) "x" => Sum.elim (fun z : Fin k × WithWidths Old V w => y z.1 z.2) guess
local notation3 (prettyPrint := false) "prior" => Sum.elim (fun z : Fin k × Old => y z.1 (.inl z.2)) guess
local notation3 (prettyPrint := false) "f" => jointAt (k := k) (V := V) (V' := V') (w := w) (E := E) (B := B) (Old := Old) e code p eq fit kernel

/-- The actual branch in the scheduler's rectangle has the evaluated
geometry and exact numeric fields of its complete installed programs. -/
theorem jointAt_image (site : pdir.sites.trans (finCongr eq).toEmbedding = siteRows e s.input (parallelName names) code)
    (input : ∀ i, Covers (names i) (fun v => (old i v).program.size) (assignedColumn true) (y i))
    (ready : PublicEndpoints.Represents saved pdir.dense.sites pdir.dense.cables pdir.dummy
      (fun z => kernel.eval prior (.inl (.inr (.inr z)))))
    (ports : ∀ i, p.Reads (child i).pack.layout (names i) port)
    (width : ∀ i, p.width i < 2^w) (holes : ∀ i ∉ Set.range port, p.width i = 0)
    (data : ∀ i, RecordData (child i).pack.layout) {C T : ℕ} (hT : 0<T) (cert : s.RecordFactor e C)
    (cap : ∀ i, RecordsWithin (child i) (data i) true T)
    (charge : ∀ i v, (old i v).program.publicNodes ≤ (data i).prior v ∧ (old i v).program.expandedLoad ≤ (data i).payload v)
    (word : 2*(loadMultiplier e*C*k*T) < 2^w) :
    ((fun z => (f).eval x (.inl (.inl z))) = kernel.eval prior ∘ Sum.inl) ∧
      ∀ b, Covers pdir.dense.sites (fun v => if b then (next v).program.size else (next v).program.work)
        (assignedColumn b) ((f).eval x ∘ Sum.inl) := by
  subst V'
  exact joint_image e s q old names pdir code p port binName position fit kernel y room site input ready ports width holes
    data hT cert cap charge word

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
