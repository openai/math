import OAI.Computability.BorderVNP.ShortenEnrichedNamedPath

/-!
# A normalized program of the literal named physical node circuits

The motion and stage of each admissible child tuple are taken from its own
physical node execution. Guessing any valid histogram saves the actual
output pins and sparse rows, and the resulting state is admissible at the
next source level. The guard accepts exactly the normalized history codec.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath

open Crossing Cover Cover.Frame Epoch Epoch.Round Shortening Shortening.Adaptive Packing Physical
open Shortening.PublicRelative Shortening.PreparedBins Shortening.PublicParallel Shortening.StaticRows NamedKernel
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u v
variable {D m b k : ℕ} [NeZero D] {K : Type u} [Field K] {P : Type} [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} (p : SourcePath b e h H ν) (last high : ℕ)
    (V E : ℕ → ℕ) (w : ℕ) (cap : ℕ → ℕ) {Extra : ℕ → Type v}
    (keep : ∀ j, p.NamedAt last high V E w P bits k Extra j → Prop) (hk : 0<k)

/-- Actual geometric projection of the admissible named state. -/
noncomputable abbrev namedView (j : ℕ) (x : (NamedState.Admissible (p.NamedGood last high V E w cap keep) j)) := x.val.placed

/-- Every input cable uses its actual sparse name within its child rectangle. -/
noncomputable abbrev childSlots (i : Fin b) (c : Fin k → (NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val)) : CableSlots (raw fun j => (c j).val.placed) :=
  ⟨k*E i.val,parallelName fun j => (c j).val.names.cables⟩


set_option genInjectivity false in
/-- The complete named program and its selected, measured, circuit-correct
stages. The original sparse input and destination rows remain explicit. -/
structure NamedRun (nodes : ∀ i : Fin b, p.Node last high V E w k i) where
  /-- The normalized physical history on its actual admissible named arrays. -/
  program : Normalized.Program (A := NamedState.Admissible (p.NamedGood last high V E w cap keep))
    (depth := p.asPath.depth last high) (B := fun i => (p.pattern i).bins.Bin) e (p.namedView last high V E w cap keep)
  /-- Every attained count fits the public histogram width. -/
  fits : program.Fits (fun _ => w)
  /-- The real shared node circuit enforces the exact histogram encoder. -/
  correct : LocalCorrect (program.codec fits) (NamedState.represents (good := p.NamedGood last high V E w cap keep)) (p.namedKernels last high V E w nodes)
  /-- The selected labels and motions from the actual child words. -/
  selected : ∀ (i : Fin b) (c : Fin k → (NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val)),
    (p.pattern i).SelectionAt (p.stepDepth last high i) (fun j => (c j).val.placed) hk
  /-- The physical stage is the one installed on these words and input names. -/
  installed : ∀ (i : Fin b) (c : Fin k → NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val), p.InstalledStage last high (p.namedView last high V E w cap keep) hk i c (selected i c) (p.childSlots last high V E w cap keep i c) (program.stage i c)
  /-- Actual sparse destination rows used on each history. -/
  directory : ∀ (i : Fin b) (c : Fin k → NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val) (q : (program.stage i c).Index e),
    Directory ((program.stage i c).result e q) (V (i.val+1)) (E (i.val+1))
  /-- The seed rectangle of the actual public compiler. -/
  seedCount : Fin b → ℕ
  /-- Static seed numbering shared by the population pass, output site names and output cables. -/
  seedCode : ∀ i : Fin b, Shortening.PublicDenseReceipt.Seed (p.pattern i).bins
    (p.asPath.depth last high (i.val+1)) ≃ Fin (seedCount i)
  /-- The old-only intermediate frame of the very same selected node. -/
  operands : ∀ i : Fin b, Shortening.PublicDenseReceipt.Operands (Fin k × p.StatePins last high V E w i.val)
    (Shortening.PublicDenseReceipt.Seed (p.pattern i).bins (p.asPath.depth last high (i.val+1))) D (k*E i.val) w
  /-- The actual bin key is a deck address followed by the fixed relative bin tag. -/
  keyBits : ∀ i, (operands i).keyBits = Shortening.PublicDenseReceipt.operandBits D (p.pattern i).bins.Bin
    (p.asPath.depth last high (i.val+1))
  /-- All gates of the old-only operand table are covered by this actual geometry pass. -/
  operand_size : ∀ i, (operands i).frame.size ≤ (nodes i).size
  /-- The complete table computed from the assigned child words describes this chosen stage. -/
  operand_read : ∀ (i : Fin b) (c : Fin k → NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val),
    (operands i).OnStage e (program.stage i c) (parallelName fun j => (c j).val.names.sites)
      (parallelName fun j => (c j).val.names.cables) (seedCode i) (fun z => (c z.1).val.words z.2)
  /-- Both site and cable numbers use the source table's own fixed seed ordering. -/
  numbered : ∀ (i : Fin b) (c : Fin k → NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val) hist,
    (∀ v, ((directory i c hist).sites v).val = (siteRows e (program.stage i c).input
      (parallelName fun j => (c j).val.names.sites) (seedCode i).toEmbedding v).val) ∧
    ∀ z, ((directory i c hist).cables z).val = (program.stage i c).cableNumber e (seedCode i).toEmbedding hist z
  /-- The stored network is the exact dense reindexing at its assigned rows. -/
  stored : ∀ (i : Fin b) (c : Fin k → NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val) (q : (program.stage i c).Index e), (program.advance i c q).val.placed = ((program.stage i c).result e q).dense (directory i c q).cables

  /-- The actual saved state carries the very same sparse site and cable directory. -/
  saved_names : ∀ (i : Fin b) (c : Fin k → NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val) (q : (program.stage i c).Index e),
    HEq (program.advance i c q).val.names (directory i c q).dense

variable {p last high V E w cap keep hk} in
/-- The actual source order numbers both output rectangles throughout all accepted branches. -/
theorem NamedRun.fixed_directory_numbers {nodes : ∀ i : Fin b, p.Node last high V E w k i}
    (r : p.NamedRun last high V E w cap keep hk nodes) (i : Fin b) :
    ∃ seeds : ℕ, ∃ seed : Shortening.PublicDenseReceipt.Seed (p.pattern i).bins (p.asPath.depth last high (i.val+1)) ≃ Fin seeds,
      ∀ (c : Fin k → NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val) hist,
        (∀ v, ((r.directory i c hist).sites v).val = (siteRows e (r.program.stage i c).input
          (parallelName fun j => (c j).val.names.sites) seed.toEmbedding v).val) ∧
        ∀ z, ((r.directory i c hist).cables z).val = (r.program.stage i c).cableNumber e seed.toEmbedding hist z :=
  ⟨r.seedCount i,r.seedCode i,r.numbered i⟩

variable {p last high V E w cap keep hk} in
/-- The fixed site ordering of all physical branch successors. -/
theorem NamedRun.fixed_site_numbers {nodes : ∀ i : Fin b, p.Node last high V E w k i}
    (r : p.NamedRun last high V E w cap keep hk nodes) (i : Fin b) :
    ∃ seeds : ℕ, ∃ seed : Shortening.PublicDenseReceipt.Seed (p.pattern i).bins (p.asPath.depth last high (i.val+1)) ≃ Fin seeds,
      ∀ (c : Fin k → NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val) hist v,
        ((r.directory i c hist).sites v).val = (siteRows e (r.program.stage i c).input
          (parallelName fun j => (c j).val.names.sites) seed.toEmbedding v).val := by
  obtain ⟨n,seed,names⟩ := r.fixed_directory_numbers i
  exact ⟨n,seed,fun c hist => (names c hist).1⟩

variable {p last high V E w cap keep hk} in
/-- Specialize the one fixed stage-wide seed ordering to the chosen child words. -/
theorem NamedRun.site_numbers {nodes : ∀ i : Fin b, p.Node last high V E w k i}
    (r : p.NamedRun last high V E w cap keep hk nodes) (i : Fin b)
    (c : Fin k → NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val) :
    ∃ seeds : ℕ, ∃ seed : Shortening.PublicDenseReceipt.Seed (p.pattern i).bins (p.asPath.depth last high (i.val+1)) ≃ Fin seeds,
      ∀ hist v, ((r.directory i c hist).sites v).val = (siteRows e (r.program.stage i c).input
        (parallelName fun j => (c j).val.names.sites) seed.toEmbedding v).val := by
  obtain ⟨seeds,seed,hs⟩ := r.fixed_site_numbers i
  exact ⟨seeds,seed,hs c⟩

/-- Each retained old site occupies its original within-copy sparse row. -/
theorem NamedRun.retained_sites {nodes : ∀ i : Fin b, p.Node last high V E w k i}
    (r : p.NamedRun last high V E w cap keep hk nodes) (i : Fin b)
    (c : Fin k → NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val)
    (q : (r.program.stage i c).Index e) (v : (raw fun j => (c j).val.placed).layout.Site) :
    ((r.directory i c q).sites (.inl v)).val = ((parallelName fun j => (c j).val.names.sites) v).val := by
  obtain ⟨_,_,names⟩ := r.site_numbers i c
  exact names q (.inl v)

/-- The exact destination names consumed by quantitative geometry and record replay. -/
noncomputable def NamedRun.saveNames {nodes : ∀ i : Fin b, p.Node last high V E w k i}
    (r : p.NamedRun last high V E w cap keep hk nodes) : r.program.SaveNames where
  capacity := fun i _ _ => E (i.val+1)
  number := fun i c q => (r.directory i c q).cables
  stored := r.stored

/-- Any extra payload invariant can be extended on the exact serialized bits
of an attained node. The common geometric, record and directory invariants
are discharged by the physical kernel itself. -/
def RetainsNamed : Prop :=
  ∀ (i : Fin b) (c : Fin k → (NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val))
    (sel : (p.pattern i).SelectionAt (p.stepDepth last high i) (fun j => (c j).val.placed) hk)
    (s : Stage m (p.pattern i).bins.Bin (p.asPath.depth last high (i.val+1)) (fun j => (c j).val.placed)),
    p.InstalledStage last high (p.namedView last high V E w cap keep) hk i c sel (p.childSlots last high V E w cap keep i c) s →
    ∀ (q : s.Index e) (dir : Directory (s.result e q) (V (i.val+1)) (E (i.val+1)))
      (z : p.StatePins last high V E w (i.val+1) → Bool),
      dir.dense.Reads (p.catalog (i.val+1)) (segmentField (factorEnum D) (p.catalog (i.val+1)) rfl) z →
      ∃ x : Extra (i.val+1), keep (i.val+1) ⟨(s.result e q).dense dir.cables,dir.dense,z,x⟩

/-- No further payload invariant is required for the physical geometric
state and its actual words. -/
theorem retains_unit : p.RetainsNamed (P := P) (bits := bits) (Extra := fun _ => Unit) last high V E w cap
    (fun _ _ => True) hk := fun _ _ _ _ _ _ _ _ _ => ⟨(),trivial⟩

set_option maxHeartbeats 800000 in
/-- Assemble the very node frames selected by the source path into an actual
named adaptive program. Choices can depend on all child bits, and the
stage, guard, saved directory and geometry continue to share one witness. -/
theorem namedRun_of_nodes (nodes : ∀ i : Fin b, p.Node last high V E w k i) (widthCap : Fin b → ℕ)
    (run : ∀ i : Fin b, SourceTemplate.NodeRun.{u,v} (P := Port k P i.val) (bits := width bits k i.val)
      (p.pattern i) (p.stepDepth last high i) hk (p.catalog (i.val+1)) (widthCap i) (nodes i))
    (widths : ∀ i : Fin b, Fintype.card (Cube D → Deck (p.asPath.depth last high i.val+1))*cap i.val ≤ widthCap i)
    (growth : ∀ i : Fin b, (p.pattern i).record*k*cap i.val ≤ cap (i.val+1))
    (retain : p.RetainsNamed last high V E w cap keep hk) :
    Nonempty (p.NamedRun last high V E w cap keep hk nodes) := by
  let inputs := fun (i : Fin b) (c : Fin k → (NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val)) => fun j => (c j).val
  choose seedCounts seedCodes operand keySize operandCost applyNode using run
  have execute (i : Fin b) (c : Fin k → (NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val)) := applyNode i (inputs i c)
    (fun j => (c j).property.placed) (fun j => (c j).property.reads) (fun j => by
      obtain ⟨data,within⟩ := (c j).property.expanded
      exact (widths_of_recordsWithin _ data within).trans (widths i))
  choose select stage names receipt siteIDs cableIDs operandRead room guard output using execute
  let kernel := p.namedKernels last high V E w nodes
  let oldWords (i : Fin b) (c : Fin k → (NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val)) :=
    fun z : Fin k × p.StatePins last high V E w i.val => (c z.1).val.words z.2
  let savedWords (i : Fin b) (c : Fin k → (NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val)) (q : (stage i c).Index e) :=
    (kernel i.val i.isLt).eval (Sum.elim (oldWords i c) (NamedState.guess (w := fun _ => w) e stage room i c q)) ∘ Sum.inl
  have installed (i : Fin b) (c : Fin k → (NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val)) :=
    p.installed_of_receipt last high (p.namedView last high V E w cap keep) hk i c (select i c) (p.childSlots last high V E w cap keep i c) (stage i c) (receipt i c)
  have readback (i : Fin b) (c : Fin k → (NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val)) (q : (stage i c).Index e) :
      (names i c q).dense.Reads (p.catalog (i.val+1)) (segmentField (factorEnum D) (p.catalog (i.val+1)) rfl)
        (savedWords i c q) := by
    let g := NamedState.guess (w := fun _ => w) e stage room i c q
    let pin := pinEquiv (I := Cube D) (B := fun i => (p.pattern i).bins.Bin)
      (depth := p.asPath.depth last high) (e := e) (fun _ => w) i
    have hword : g ∘ pin = NamedReceipt.word (stage i c) (room i c) q := word_at_pin (B := fun i => (p.pattern i).bins.Bin) (lev := p.asPath.depth last high) (w := fun _ => w) i (stage i c) (room i c) q
    have heval := scheduled_eval (nodes i) pin id (oldWords i c) g
    rw [hword] at heval
    have hbits : savedWords i c q = (nodes i).eval (Sum.elim (oldWords i c) (NamedReceipt.word (stage i c) (room i c) q)) ∘ Sum.inl :=
      funext fun j => congrFun heval (.inl j)
    rw [hbits]
    exact output i c q
  have payloadChoice (i : Fin b) (c : Fin k → (NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val)) (q : (stage i c).Index e) := retain i c (select i c) (stage i c)
    (installed i c) q (names i c q) (savedWords i c q) (readback i c q)
  choose extra metadata using payloadChoice
  have closed (i : Fin b) (c : Fin k → (NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val)) (q : (stage i c).Index e) :
      p.NamedGood last high V E w cap keep (i.val+1) (NamedState.save e stage room kernel names extra i c q) := by
    obtain ⟨data,hr⟩ := (stage i c).namedSave_records e q (names i c q) (installed i c).records true (cap i.val)
      (fun j => (c j).property.expanded)
    refine ⟨(installed i c).saved q _ (names i c q).cables,readback i c q,⟨data,?_⟩,metadata i c q⟩
    intro t
    have hi : portFintype (k := k) (P := P) (b := i.val+1) = instFintypeProd (Fin k) (Port k P i.val) :=
      Subsingleton.elim _ _
    change 1 + @localRecords D _ portFintype _ _ _ _ _ _ ≤ _
    rw [hi]
    exact (hr t).trans (growth i)
  let F := NamedState.program e stage room kernel names extra closed
  have guards (i : Fin b) (c : Fin k → (NamedState.Admissible (p.NamedGood last high V E w cap keep) i.val))
      (g : Pin (Cube D) (fun i => (p.pattern i).bins.Bin) (p.asPath.depth last high) e.count (fun _ => w) i.val → Bool) :
      (kernel i.val i.isLt).eval (Sum.elim (oldWords i c) g) (.inr ()) = true ↔
        BankCircuit.Accepted e (stage i c).matched (fields (e := e) (fun _ => w) i g) := by
    let pin := pinEquiv (I := Cube D) (B := fun i => (p.pattern i).bins.Bin)
      (depth := p.asPath.depth last high) (e := e) (fun _ => w) i
    have hflag := congrFun (scheduled_eval (nodes i) pin id (oldWords i c) g) (.inr ())
    change (scheduled (nodes i) pin id).eval (Sum.elim (oldWords i c) g) (.inr ()) = true ↔ _
    rw [hflag]
    exact guard i c (g ∘ pin)
  exact ⟨⟨F,NamedState.fits e stage room kernel names extra closed,
    NamedState.correct e stage room kernel names extra closed guards,select,installed,names,seedCounts,seedCodes,operand,keySize,operandCost,operandRead,(fun i c q => ⟨siteIDs i c q,cableIDs i c q⟩),fun _ _ _ => rfl,fun _ _ _ => HEq.rfl⟩⟩

end PackedHistoryCircuit.Normalized.SourcePath

end BorderVNP
end Computability
end OAI
