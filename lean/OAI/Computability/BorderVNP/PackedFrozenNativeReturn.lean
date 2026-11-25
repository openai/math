import OAI.Computability.BorderVNP.PackedFrozenNativeInputs
import OAI.Computability.BorderVNP.PackedNamedResultPresence
import OAI.Computability.BorderVNP.PackedInheritedWorkReceipt

/-! # Returning the physical endpoint and occupancy columns from a named shortening step -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicParallel Shortening.PublicDenseReceipt
open Shortening.StaticRows Epoch Epoch.Round Packing Packing.DirectoryCircuit Packing.CellAddressCircuit
open Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1600000

variable {D m b k last high w np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} {path : SourcePath b e h H ν} {V E cap : ℕ → ℕ}
    {Extra : ℕ → Type*} {keep : ∀ j,path.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
    {nodes : ∀ i : Fin b,path.Node last high V E w k i} (r : path.NamedRun last high V E w cap keep hk nodes)
    (i : Fin b) (S : Format) (header : WorkWords.Ports np) (leaf : P ↪ Fin np)
local notation3 (prettyPrint := false) "A" i => Shortening.PublicDenseReceipt.Seed (path.pattern i).bins
  (path.asPath.depth last high (Fin.val i+1))
local notation3 (prettyPrint := false) "geo" j => path.StatePins last high V E w j
local notation3 (prettyPrint := false) "ww" j => WithWidths (geo j) (V j) w
local notation3 (prettyPrint := false) "child" => S.Output (geo i.val) (V i.val) w w
local notation3 (prettyPrint := false) "input" => ((Fin k × child) ⊕ Words (A i) e.count w)
local notation3 (prettyPrint := false) "O" => r.operands i
local notation3 (prettyPrint := false) "ctx" => Shared.Context input (O).Pin (ww (i.val+1)) (k*E i.val) w
local notation3 (prettyPrint := false) "oldHeader" => header.nested k V i.val
local notation3 (prettyPrint := false) "nextHeader" => (oldHeader).parallel k (V i.val)
variable (rect : ∀ j : Fin b,V (j.val+1)=siteCapacity e (k*V j.val)
    (Fintype.card (ProgramSchemas.Seeds path last high j)))
variable (edgeRect : ∀ j : Fin b,E (j.val+1)=edgeCapacity e (k*E j.val)
    (Fintype.card (ProgramSchemas.Seeds path last high j)))
variable (fits : ∀ j : Fin b,V (j.val+1) ≤ 2^w) (hm : 0 < m)
variable (c : Fin k → NamedState.Admissible (path.NamedGood last high V E w cap keep) i.val)
    (q : (r.program.stage i c).Index e) (old : ∀ j,Site.Programs (c j).val.placed.pack.layout)
    (y : Fin k → S.Output (path.StatePins last high V E w i.val) (V i.val) w w → Bool)
    (next : Frame ((Fin k × S.Output (path.StatePins last high V E w i.val) (V i.val) w w) ⊕
      Words (ProgramSchemas.Seeds path last high i) e.count w)
      (WithWidths (path.StatePins last high V E w (i.val+1)) (V (i.val+1)) w ⊕ Unit))
    (names : ∀ j : Fin b, ProgramSchemas.Seeds path last high j → ℕ) (position : e.Entry → ℕ)
    (bound : ℕ → ℕ) (previous : ∀ j, Read header leaf bound i.val S (c j) (old j) (y j))
local notation3 (prettyPrint := false) "st" => r.program.stage i c
local notation3 (prettyPrint := false) "p" => raw (fun j => (c j).val.placed)
local notation3 (prettyPrint := false) "site" => parallelName (fun j => (c j).val.names.sites)
local notation3 (prettyPrint := false) "slot" => (st).slot.trans (finCongr (r.installed i c).capacity).toEmbedding
local notation3 (prettyPrint := false) "port" => Parallel.nestedPorts k leaf (i.val+1)
local notation3 (prettyPrint := false) "words" => (fun z : Fin k × geo i.val => (c z.1).val.words z.2)
local notation3 (prettyPrint := false) "basePin" => geoPin (path := path) (last := last) (high := high)
  (V := V) (E := E) (w := w) (k := k) i S

local notation3 (prettyPrint := false) "a₀" => assignment r i S c q y
local notation3 (prettyPrint := false) "x" => (sourceWith r i S next).eval a₀
local notation3 (prettyPrint := false) "current" => r.program.advance i c q
local notation3 (prettyPrint := false) "pr" => r.program.savePrivatePrograms r.saveNames (r.privateSiteRows leaf names)
  position i c q old
local notation3 (prettyPrint := false) "sID" => siteRows e (st).input site (r.directorySeed i).toEmbedding
local notation3 (prettyPrint := false) "geom" => (nodes i).eval (Sum.elim words (NamedReceipt.word (st) (r.fits i c) q)) ∘ Sum.inl
/-- The successor's checked routed fields and the two constant references
are exactly the corresponding pins in the shared gate list. -/
theorem returned_wires (returned : WidthRead header leaf bound (i.val+1) current pr (next.eval a₀ ∘ Sum.inl)) :
    x ∘ resultPin r i S = (Diagonal.ExternalSew.FieldExport.constants _).eval geom := by
  funext z
  rcases z with z|z
  · rw [Diagonal.ExternalSew.FieldExport.constants_eval]
    exact (Shared.source_widths (O) basePin next a₀ (.inl z)).trans
      ((congrFun returned.geometry z).trans (congrFun (r.geometry_words i c q).symm z))
  · rw [Diagonal.ExternalSew.FieldExport.constants_eval]
    exact Shared.source_literal (O) basePin next a₀ z

include previous in
/-- Every live cable and external port of the returned stage has its true
endpoint and width in the chosen source. Empty cable and port slots read zero. -/
theorem new_endpoints (base : (PortTable.mk np leaf header).Widths bits w)
    (returned : WidthRead header leaf bound (i.val+1) current pr (next.eval a₀ ∘ Sum.inl)) :
    Views.EndpointData ((st).result e q).pack.layout (newFields r i S header rect edgeRect fits)
      sID (r.resultCableRows i c q) port x := by
  have wires := returned_wires r i S header leaf c q old y next names position bound returned
  have small := header.nested_widths leaf k V base i.val
  exact r.sharedResultEndpoints i c q oldHeader (Parallel.nestedPorts k leaf i.val)
    (fun j => (previous j).widths.ports) small (fits i) (rect i) (edgeRect i) (resultPin r i S) x wires

/-- An enabled slot is exactly one of the physical output cables before
the second dense save of the selected stage. -/
theorem new_occupied (returned : WidthRead header leaf bound (i.val+1) current pr (next.eval a₀ ∘ Sum.inl))
    (a : Fin (edgeCapacity e (k*E i.val) (Fintype.card (A i)))) :
    x (newOccupied r i S edgeRect a) = true ↔ a ∈ Set.range (r.resultCableRows i c q) :=
  r.sharedResultOccupied i c q (edgeRect i) (resultPin r i S) x
    (returned_wires r i S header leaf c q old y next names position bound returned) a

/-- The actual returned owner code uses the site's scheduled numeric row. -/
theorem site_keys :
    (sID).trans ((newFields r i S header rect edgeRect fits).sites.trans Fin.valEmbedding) =
      (sID).trans Fin.valEmbedding := by
  apply DFunLike.ext
  intro v
  exact Ports.sharedResultSite ..

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

end BorderVNP
end Computability
end OAI
