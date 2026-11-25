import OAI.Computability.BorderVNP.PackedHistorySiteModelRows
import OAI.Computability.BorderVNP.ShortenEnrichedNamedProgram

/-! # The physical named run supplies the row coherence of private-site replay

A named receipt sorts exactly the parallel child cable rectangle and stores
the emitted dense directory on its successor. Exterior port rectangles are
constructed recursively from the original leaf's public injection. These are
the row equalities consumed by the actual sparse model induction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Parallel

open Shortening.Adaptive

/-- Capacity of the nested copy-and-port rectangle. -/
def nestedCapacity (k cap : ℕ) : ℕ → ℕ
  | 0 => cap
  | n+1 => k*nestedCapacity k cap n

/-- One public row per nested free port, using the same stride as each parallel step. -/
def nestedPorts {P : Type} {np : ℕ} (k : ℕ) (port : P ↪ Fin np) :
    (n : ℕ) → Port k P n ↪ Fin (nestedCapacity k np n)
  | 0 => port
  | n+1 => portRows k (nestedPorts k port n)

end Packing.Inherited.Parallel

namespace PackedHistoryCircuit.Normalized.SourcePath

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicParallel Packing Packing.Inherited
open Epoch Epoch.Round
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m b k last high w np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} {p : SourcePath b e h H ν}
    {V E cap : ℕ → ℕ} {Extra : ℕ → Type*}
    {keep : ∀ j, p.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0 < k}
    {nodes : ∀ i : Fin b, p.Node last high V E w k i}
    (r : p.NamedRun last high V E w cap keep hk nodes) (port : P ↪ Fin np)
    (seeds : ∀ i : Fin b, ((Cube D → Deck (p.asPath.depth last high (i.val+1)+1)) × (p.pattern i).bins.Bin) → ℕ)

/-- The real serializer's site rows, the nested exterior rows, and the public seed numbering. -/
noncomputable def NamedRun.privateSiteRows : r.program.SiteRows where
  nSite i _ _ := V (i.val+1)
  sites i c q := (r.directory i c q).sites
  nPort := Parallel.nestedCapacity k np
  ports := Parallel.nestedPorts k port
  seeds := seeds

private theorem directory_cable_heq {D lev V E : ℕ} {P K : Type} {bits : P → ℕ}
    {x y : PlacedPack D P bits K (Cube D) lev} (dx : Directory x V E) (dy : Directory y V E)
    (h : x = y) (hd : HEq dx dy) : HEq dx.cables dy.cables := by
  subst y
  obtain rfl := eq_of_heq hd
  rfl

/-- A concrete named run supplies every cable, capacity and port coherence
witness required for the field semantics of the private-program history. -/
noncomputable def NamedRun.modelRows :
    r.program.SiteModelRows r.saveNames (r.privateSiteRows port seeds) where
  capacity := E
  edges _ x := x.val.names.cables
  inputCap i c := (r.installed i c).capacity
  inputRows i c := (r.installed i c).slots
  savedCap _ _ _ := rfl
  savedRows i c q := directory_cable_heq (r.program.advance i c q).val.names (r.directory i c q).dense
    (r.stored i c q) (r.saved_names i c q)
  portCap _ := rfl
  portRows _ _ := rfl

end PackedHistoryCircuit.Normalized.SourcePath

end BorderVNP
end Computability
end OAI
