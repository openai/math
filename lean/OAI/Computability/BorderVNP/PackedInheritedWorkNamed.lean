import OAI.Computability.BorderVNP.PackedInheritedWorkNamedKernel
import OAI.Computability.BorderVNP.PackedInheritedWorkReceipt
import OAI.Computability.BorderVNP.PackedInheritedWorkSave

/-! # The true width and port image of the fixed named node -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.StaticRows Shortening.PublicParallel
open Shortening.PublicEndpoints Packing Packing.Inherited Packing.Inherited.WorkWords InheritedBank NamedKernel Physical
open VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

universe u
variable {D m b k np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {h H ν : ℝ} {src : SourcePath b e h H ν} {last high : ℕ}
variable {V E : ℕ → ℕ} {w : ℕ} {cap : ℕ → ℕ} {Extra : ℕ → Type u}
variable {keep : ∀ j, src.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
variable {nodes : ∀ i : Fin b, src.Node last high V E w k i}
variable (r : src.NamedRun last high V E w cap keep hk nodes)

local notation3 (prettyPrint := false) "Seeds" i => Shortening.PublicDenseReceipt.Seed (src.pattern i).bins (src.asPath.depth last high (Fin.val i+1))
local notation3 (prettyPrint := false) "Words" j => WithWidths (src.StatePins last high V E w j) (V j) w
local notation3 (prettyPrint := false) "Pins" => Pin (Cube D) (fun i => (src.pattern i).bins.Bin) (src.asPath.depth last high) e.count (fun _ => w)
local notation3 (prettyPrint := false) "At" j => NamedState.Admissible (src.NamedGood last high V E w cap keep) j
variable (header : WorkWords.Ports np) (leaf : P ↪ Fin np)
variable (rect : ∀ i : Fin b, V (i.val+1)=siteCapacity e (k*V i.val) (Fintype.card (Shortening.PublicDenseReceipt.Seed (src.pattern i).bins (src.asPath.depth last high (i.val+1)))))
variable (fits : ∀ i : Fin b, V (i.val+1) ≤ 2^w)

variable (seeds : ∀ i : Fin b, (Shortening.PublicDenseReceipt.Seed (src.pattern i).bins (src.asPath.depth last high (i.val+1))) → ℕ) (number : e.Entry → ℕ) (bound : ℕ → ℕ)
variable (base : (PortTable.mk np leaf header).Widths bits w) (positive : ∀ i : Fin b, 0 < bound i.val)
variable (growth : ∀ i : Fin b, loadMultiplier e*(src.pattern i).record*k*bound i.val ≤ bound (i.val+1))
variable (word : ∀ i : Fin b, 2*bound (i.val+1) < 2^w)
variable (i : Fin b) (c : Fin k → NamedState.Admissible (src.NamedGood last high V E w cap keep) i.val)
variable (q : (r.program.stage i c).Index e)
variable (old : ∀ j, Site.Programs (c j).val.placed.pack.layout) (y : Fin k → WithWidths (src.StatePins last high V E w i.val) (V i.val) w → Bool)
local notation3 (prettyPrint := false) "st" => r.program.stage i c
local notation3 (prettyPrint := false) "dir" => r.directory i c q
local notation3 (prettyPrint := false) "g" => (r.program.codec r.fits).word i.val i.isLt c q
local notation3 (prettyPrint := false) "native" => NamedReceipt.word st (r.fits i c) q
local notation3 (prettyPrint := false) "port" => Parallel.nestedPorts k leaf i.val
local notation3 (prettyPrint := false) "ids" => Parallel.portRows k port
local notation3 (prettyPrint := false) "tape" => (st).privatePrograms e q old (dir).sites (dir).cables ids (seeds i) number
local notation3 (prettyPrint := false) "result" => r.program.advance i c q
local notation3 (prettyPrint := false) "assign" => Sum.elim (fun z : Fin k × Words i.val => y z.1 z.2)
local notation3 (prettyPrint := false) "out" => ((r.widthSteps header rect fits i.val i.isLt).eval (assign g)) ∘ Sum.inl

include base positive growth word in
/-- The raw work node on the true histogram word computes both fields at the
actual second dense save, for the very same private programs as the named geometry. -/
theorem widthNode_read (previous : ∀ j, WidthRead header leaf bound i.val (c j) (old j) (y j)) :
    WidthRead header leaf bound (i.val+1) result
      (r.program.savePrivatePrograms r.saveNames (r.privateSiteRows leaf seeds) number i c q old)
      ((r.widthNode header rect fits i).eval (assign native) ∘ Sum.inl) := by
  have oldGeo : (fun z : Fin k × src.StatePins last high V E w i.val => y z.1 (.inl z.2)) =
      fun z => (c z.1).val.words z.2 := funext fun z => congrFun (previous z.1).geometry z.2
  have hrows := (r.directorySeed_spec i c q).1
  have hs : (dir).sites.trans (finCongr (rect i)).toEmbedding =
      siteRows e (st).input (parallelName fun j => (c j).val.names.sites) (r.widthSeed i).toEmbedding :=
    DFunLike.ext _ _ fun v => Fin.ext (hrows v)
  have ep := r.geometry_endpoints i c q
  let T := loadMultiplier e*(src.pattern i).record*k*bound i.val
  have capT : 2*T < 2^w := (Nat.mul_le_mul_left 2 (growth i)).trans_lt (word i)
  let data := fun j => (old j).bankFields
  let fields := header.nested k V i.val
  have fieldOK := header.nested_widths leaf k V base i.val
  have prevOK := fun j => (previous j).ports
  have branch := jointAt_image (Old := src.StatePins last high V E w i.val)
    (B := Cover.AddressCircuit.ProductSlots (Fintype.card (Cube D)) (src.asPath.depth last high (i.val+1)+1) ⊕ ↥(src.catalog (i.val+1)))
    e fields (rect i) (fits i) st q old (fun j => (c j).val.names.sites) dir
    (r.widthSeed i).toEmbedding port (seeds i) number (nodes i) y (r.fits i c) hs
    (fun j => (previous j).widths true) (by rw [oldGeo]; exact ep)
    prevOK fieldOK.fit fieldOK.holes data (positive i) (r.installed i c).records
    (fun j => (previous j).capacity) (fun _ _ => ⟨le_rfl,le_rfl⟩) capT
  constructor
  · have geom := branch.1
    rw [oldGeo] at geom
    exact geom.trans (r.geometry_words i c q)
  · intro b
    let measure (s : Site) := if b then s.size else s.work
    exact Covers.stored dir (result).val.names (r.stored i c q) (r.saved_names i c q) tape
      (assignedColumn b) _ measure (branch.2 b)
  · let p := (st).result e q
    have hp : (fields.parallel k (V i.val)).Reads p.pack.layout (dir).sites ids := by
      constructor
      · rintro ⟨j,a⟩
        have he := finProdFinEquiv.symm_apply_apply (j,port a)
        change (finProdFinEquiv.symm (finProdFinEquiv (j,port a))).1.val*V i.val +
          fields.host (finProdFinEquiv.symm (finProdFinEquiv (j,port a))).2 = _
        rw [he,(prevOK j).attach a,hrows]
        change j.val*V i.val+_ = _+V i.val*j.val
        ac_rfl
      · exact (header.nested_widths leaf k V base (i.val+1)).live
      · exact (header.nested_widths leaf k V base (i.val+1)).holes
    exact Ports.Reads.stored p (result).val.placed dir (result).val.names (r.stored i c q)
      _ _ (r.saved_names i c q) hp
  · have ht := (st).privatePrograms_bankWithin e q old (dir).sites (dir).cables ids (seeds i) number data
      (r.installed i c).records true (positive i) (fun j => (previous j).capacity) (fun _ _ => ⟨le_rfl,le_rfl⟩)
    have stored := bankWithin_stored (fin' := portFintype (P := P) (k := k) (b := i.val+1)) ((st).result e q) (result).val.placed dir (r.stored i c q)
      tape true T ht
    exact fun t => (stored t).trans (growth i)

include base positive growth word in
/-- Reindexing the node's guess wires gives the same readback on the normalized
inner compiler's public history encoding. -/
theorem widthSteps_read (previous : ∀ j, WidthRead header leaf bound i.val (c j) (old j) (y j)) :
    WidthRead header leaf bound (i.val+1) result
      (r.program.savePrivatePrograms r.saveNames (r.privateSiteRows leaf seeds) number i c q old) out := by
  let localGuess := pinEquiv (I := Cube D) (B := fun i => (src.pattern i).bins.Bin) (depth := src.asPath.depth last high)
    (e := e) (fun _ => w) i
  have hw : g ∘ localGuess = native := word_at_pin (B := fun i => (src.pattern i).bins.Bin)
    (lev := src.asPath.depth last high) (w := fun _ => w) i st (r.fits i c) q
  have wire := scheduled_eval (r.widthNode header rect fits i) localGuess id (fun z : Fin k × Words i.val => y z.1 z.2) g
  rw [hw] at wire
  have outEq : out = (r.widthNode header rect fits i).eval (assign native) ∘ Sum.inl :=
    funext fun z => congrFun wire (.inl z)
  rw [outEq]
  exact r.widthNode_read header leaf rect fits seeds number bound base positive growth word i c q old y previous

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
