import OAI.Computability.BorderVNP.PackedInheritedWorkNames

/-! # Saved endpoint provenance on the named node's literal input histogram -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Crossing Shortening Epoch Epoch.Round Cover PackedHistoryCircuit.Normalized
open Shortening.PublicRelative Shortening.PublicSegments Shortening.PublicEndpoints NamedKernel Physical
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
universe u
variable {D m b k : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {h H ν : ℝ} {src : SourcePath b e h H ν} {last high : ℕ}
variable {V E : ℕ → ℕ} {w : ℕ} {cap : ℕ → ℕ} {Extra : ℕ → Type u}
variable {keep : ∀ j, src.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
variable {nodes : ∀ i : Fin b, src.Node last high V E w k i}
variable (r : src.NamedRun last high V E w cap keep hk nodes) (i : Fin b)
variable (c : Fin k → NamedState.Admissible (src.NamedGood last high V E w cap keep) i.val)
variable (q : (r.program.stage i c).Index e)

local notation3 "child" => fun z : Fin k × src.StatePins last high V E w i.val => (c z.1).val.words z.2
local notation3 "st" => r.program.stage i c
local notation3 "actual" => NamedReceipt.word st (r.fits i c) q
local notation3 "geom" => (nodes i).eval (Sum.elim child actual) ∘ Sum.inl

/-- The raw physical node and the normalized named machine give the same
saved bits when each is run on its actual encoding of this histogram. -/
theorem geometry_words : geom = (r.program.advance i c q).val.words := by
  let g := (r.program.codec r.fits).word i.val i.isLt c q
  let pin := pinEquiv (I := Cube D) (B := fun i => (src.pattern i).bins.Bin)
    (depth := src.asPath.depth last high) (e := e) (fun _ => w) i
  have hword : g ∘ pin = actual := word_at_pin (B := fun i => (src.pattern i).bins.Bin)
    (lev := src.asPath.depth last high) (w := fun _ => w) i st (r.fits i c) q
  have heval := scheduled_eval (nodes i) pin id child g
  rw [hword] at heval
  have h := r.correct.next i.val i.isLt c (fun j => (c j).val.words) g q (fun _ => rfl) rfl
  change ((scheduled (nodes i) pin id).eval (Sum.elim child g) ∘ Sum.inl) = _ at h
  exact (funext fun z => (congrFun heval (.inl z)).symm).trans h

omit [NeZero D] [Field K] in
private theorem reads_saved {Q B : Type} {bs : Q → ℕ} {lev s t : ℕ}
    (p saved : PlacedPack D Q bs K (Cube D) lev) (dir : Directory p s t) (ns : Directory saved s t)
    (eq : saved = p.dense dir.cables) (ids : HEq ns dir.dense) {x : Inputs B s t w w → Bool}
    (ready : PublicEndpoints.Represents saved.pack.layout ns.sites ns.cables ns.dummy x) :
    PublicEndpoints.Represents (p.dense dir.cables).pack.layout dir.dense.sites dir.dense.cables dir.dummy x := by
  subst saved
  cases eq_of_heq ids
  exact ready

/-- The saved endpoint bits consumed by the work scan satisfy the real
padded directory on this very selected physical node output. -/
theorem geometry_endpoints :
    let dir := r.directory i c q
    PublicEndpoints.Represents (((st).result e q).dense dir.cables).pack.layout dir.dense.sites dir.dense.cables dir.dummy
      ((geom ∘ Sum.inr) ∘ Sum.inr) := by
  intro dir
  rw [r.geometry_words i c q]
  let result := r.program.advance i c q
  exact reads_saved ((st).result e q) result.val.placed dir result.val.names (r.stored i c q) (r.saved_names i c q)
    result.property.reads.geometry.names

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
