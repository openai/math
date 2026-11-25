import OAI.ThreeFlat.Diagonal.NativeWarmSources
import OAI.ThreeFlat.Diagonal.TraceSeedEntryBounds

namespace OAI
/-! # Source of the selected physical S44 directory and S49 seed kernel -/
namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation
open Computability.VPVNP.BurstRAM PrivateRAM RAM PhysicalStage NodePublication NavigationNodeRows TickWorkspace
open RootArchive HistoryInitialSeed HistoryStageBody.Physical HistoryNodeDirectory HistoryNodeDirectory.Selected
open scoped Fin.CommRing Classical
variable {F : Type} [Field F] [Fintype F] {W p H J d l budget : ℕ} {B : TickActiveROM.Layout}
  {fit : RAM.Contraction.Fits (TickWeightedBank.shape F p H J) W} {clock : TickChronology.Clock} {X : State d l}

theorem Selection.seed_publication (pars : Parameters) (degree : ℕ) (stages : List NavigationDirectory.Stage)
    (r : Run F X) (C : r.Charges) (O : X.ArchiveSites) (seed : LayerData O.layer) (start pay : X.Site→ℕ)
    (layers : List Layers) (m out prepared warm : Memory W)
    (s : Selection r C O seed start pay (pars.nodeArchive (pars.archive degree W) stages W)
      (parameterArchive pars degree stages W) layers budget m)
    (ran : out=state (pars.nodeArchive (pars.archive degree W) stages W)
      (program (r.archiveList s.history C O s.path seed)) m layers.length)
    (x : TickActiveROM.CellInput B clock fit) (nodes : Nodes (parameterArchive pars degree stages W))
    (teams : ℕ) (groups : Fin (parameterArchive pars degree stages W).initialLanes→Fin (parameterArchive pars degree stages W).groups)
    (done : (parameterArchive pars degree stages W).preparedInput x nodes teams layers out groups prepared)
    (sizes : PublishSizes (parameterArchive pars degree stages W) W)
    (headers : B.bounds+4≤2^W) (bounds : B.bounds+4≤base pars.age 20)
    (requests : B.auxRequest+8*B.bits≤base pars.age 20)
    (hdr : 16*layers.length ≤ stride pars.age)
    (layerRows : ∀t∈layers,8*(t.actual.first+t.actual.count) ≤ stride pars.age)
    (startup : ∀a,a<base pars.age 53→warm a=prepared a)
    (v : X.Site) (j : Fin (pars.archive degree W).initialSites) (rank : (O.ord v).val=j.val)
    (below : O.id v<(parameterArchive pars degree stages W).rootsTotal) :
    (∀ c : Fin 8,warm (base pars.age 44+8*O.id v+c.val)=out (base pars.age 44+8*O.id v+c.val)) ∧
    (∀ c : Fin 5,warm ((pars.archive degree W).initialRecords+5*j.val+c.val)=
      m ((pars.archive degree W).initialRecords+5*j.val+c.val)) := by
  let S:=stride pars.age
  let a:=parameterArchive pars degree stages W
  have fixed : 128≤S:=sizes.fixed
  have size : 8*a.rootsTotal≤S:=sizes.nodes
  have pos : O.id v=j.val:=by change O.layer.first+_=_;rw [s.zero,Nat.zero_add,rank]
  have lower : j.val<a.rootsTotal:=pos ▸ below
  have room : 8*(j.val+1)≤S:=(Nat.mul_le_mul_left 8 lower).trans size
  have current : a.current<2^W :=
    (show a.current≤base pars.age 50 by change 41*S≤51*S; omega).trans_lt sizes.address
  constructor
  · intro c
    let loc:=base pars.age 44+8*O.id v+c.val
    have z : base pars.age 43≤loc ∧ loc<base pars.age 45 := by
      change 44*S≤45*S+8*O.id v+c.val ∧ 45*S+8*O.id v+c.val<46*S
      have:=c.isLt;omega
    have top : loc<base pars.age 53:=by
      have hi : loc<46*S:=z.2
      change loc<54*S;omega
    exact (startup loc top).trans (RootArchive.prepared_stage_cell x pars degree stages sizes nodes teams
      layers groups out prepared done current headers bounds requests loc (Or.inr (Or.inl z)))
  · intro c
    let loc:=(pars.archive degree W).initialRecords+5*j.val+c.val
    have z : base pars.age 49≤loc:=by change 50*S≤50*S+5*j.val+c.val;omega
    have top : loc<base pars.age 53:=by change 50*S+5*j.val+c.val<54*S;have:=c.isLt;omega
    exact (startup loc top).trans (Selection.prepared_journal_cell pars degree stages r C O seed start pay
      layers m out prepared s ran x nodes teams groups done sizes headers bounds requests hdr layerRows loc (Or.inr z))

theorem Selection.bumped_published_seed (pars : Parameters) (degree : ℕ) (stages : List NavigationDirectory.Stage)
    (r : Run F X) (C : r.Charges) (O : X.ArchiveSites) (seed : LayerData O.layer) (start pay : X.Site→ℕ)
    (layers : List Layers) (m out prepared warm : Memory W)
    (s : Selection r C O seed start pay (pars.nodeArchive (pars.archive degree W) stages W)
      (parameterArchive pars degree stages W) layers budget m)
    (ran : out=state (pars.nodeArchive (pars.archive degree W) stages W)
      (program (r.archiveList s.history C O s.path seed)) m layers.length)
    (x : TickActiveROM.CellInput B clock fit) (nodes : Nodes (parameterArchive pars degree stages W))
    (teams : ℕ) (groups : Fin (parameterArchive pars degree stages W).initialLanes→Fin (parameterArchive pars degree stages W).groups)
    (done : (parameterArchive pars degree stages W).preparedInput x nodes teams layers out groups prepared)
    (sizes : PublishSizes (parameterArchive pars degree stages W) W)
    (headers : B.bounds+4≤2^W) (bounds : B.bounds+4≤base pars.age 20)
    (requests : B.auxRequest+8*B.bits≤base pars.age 20)
    (hdr : 16*layers.length ≤ stride pars.age)
    (layerRows : ∀t∈layers,8*(t.actual.first+t.actual.count) ≤ stride pars.age)
    (startup : ∀a,a<base pars.age 53→warm a=prepared a)
    (v : X.Site) (j : Fin (pars.archive degree W).initialSites) (rank : (O.ord v).val=j.val)

    (below : O.id v<(parameterArchive pars degree stages W).rootsTotal)
    {N : ℕ} {dir : Directory W N} {tag : ((Fin 3→Bool)→F)→ℕ} {val : Fin N→NodeValue F}
    (i : Fin N) (atID : O.id v=i.val) (before : Memory W)
    (ledger : Ledger pars.age dir tag val (TickTerminalRoot.slotKeep pars.age) warm i.val before)
    (shape : TraceBucketAtom.Layout) {V : Type} {k : ℕ}
    (G : Computability.VPVNP.Compression.LiftedSlots V (pars.archive degree W).initialDegree (Computability.VPVNP.Compression.BitWord k))
    (baseOrder : V≃Fin (pars.archive degree W).axes)
    (width : SlotImage.Edge V (Computability.VPVNP.Compression.BitWord k) (pars.archive degree W).initialDegree→ℕ)
    («meta» : (pars.archive degree W).InitialNodeMetadata G baseOrder width m)
    (kernelBase : O.layer.kernels=(pars.archive degree W).initialRecords) (kind : O.layer.kind=0)
    (scratch : volume pars.age+42 ≤ stride pars.age) (extRoom : 2*pay v≤volume pars.age)
    {depth : ℕ} (chunk : pars.perLanePairs=2^depth) :
    CursorSeed F W pars.totalPairs depth (initial pars.age shape)
      ⟨O.id v,j.val%(2^pars.axes),j.val/(2^pars.axes),2*pay v⟩
      (base pars.age 49+5*j.val) (bump (ownerData W pars.age) before) := by
  let S:=stride pars.age
  let a:=parameterArchive pars degree stages W
  obtain ⟨head,kernel⟩:=Selection.seed_publication pars degree stages r C O seed start pay layers m out
    prepared warm s ran x nodes teams groups done sizes headers bounds requests hdr layerRows startup v j rank below
  have fixed : 128≤S:=sizes.fixed
  have top : 51*S<2^W:=sizes.address
  have sz : 8*a.rootsTotal≤S:=sizes.nodes
  have cap : 8*(i.val+1)≤S:=(Nat.mul_le_mul_left 8 (atID ▸ below)).trans sz
  have pos : O.id v=j.val:=by change O.layer.first+_=_;rw [s.zero,Nat.zero_add,rank]
  apply Selection.bumped_seed_control ledger s ran (pars.archive degree W) G baseOrder width m «meta» shape
    v j rank atID kernelBase rfl
  · intro c
    simpa only [←atID] using head c
  · exact kernel
  · change 20*S≤50*S;omega
  · exact scratch
  · change 19*S<2^W;omega
  · omega
  · change 45*S+8*i.val+7<2^W;omega
  · change 50*S+5*j.val+4<2^W;omega
  · change volume pars.age+42≤S at scratch;omega
  · exact kind
  · exact Nat.two_pow_pos _
  · rfl
  · rfl
  · exact chunk

/-- Use the chronological archive after identifying its public lane count. -/
theorem Selection.bumped_published_seed_in (pars : Parameters) (degree : ℕ) (stages : List NavigationDirectory.Stage)
    (nav : RootArchive) (same : nav=parameterArchive pars degree stages W)
    (r : Run F X) (C : r.Charges) (O : X.ArchiveSites) (seed : LayerData O.layer) (start pay : X.Site→ℕ)
    (layers : List Layers) (m out prepared warm : Memory W)
    (s : Selection r C O seed start pay (pars.nodeArchive (pars.archive degree W) stages W)
      nav layers budget m)
    (ran : out=state (pars.nodeArchive (pars.archive degree W) stages W)
      (program (r.archiveList s.history C O s.path seed)) m layers.length)
    (x : TickActiveROM.CellInput B clock fit) (nodes : Nodes nav)
    (teams : ℕ) (groups : Fin nav.initialLanes→Fin nav.groups)
    (done : nav.preparedInput x nodes teams layers out groups prepared)
    (sizes : PublishSizes nav W)
    (headers : B.bounds+4≤2^W) (bounds : B.bounds+4≤base pars.age 20)
    (requests : B.auxRequest+8*B.bits≤base pars.age 20)
    (hdr : 16*layers.length ≤ stride pars.age)
    (layerRows : ∀t∈layers,8*(t.actual.first+t.actual.count) ≤ stride pars.age)
    (startup : ∀a,a<base pars.age 53→warm a=prepared a)
    (v : X.Site) (j : Fin (pars.archive degree W).initialSites) (rank : (O.ord v).val=j.val)

    (below : O.id v<nav.rootsTotal)
    {N : ℕ} {dir : Directory W N} {tag : ((Fin 3→Bool)→F)→ℕ} {val : Fin N→NodeValue F}
    (i : Fin N) (atID : O.id v=i.val) (before : Memory W)
    (ledger : Ledger pars.age dir tag val (TickTerminalRoot.slotKeep pars.age) warm i.val before)
    (shape : TraceBucketAtom.Layout) {V : Type} {k : ℕ}
    (G : Computability.VPVNP.Compression.LiftedSlots V (pars.archive degree W).initialDegree (Computability.VPVNP.Compression.BitWord k))
    (baseOrder : V≃Fin (pars.archive degree W).axes)
    (width : SlotImage.Edge V (Computability.VPVNP.Compression.BitWord k) (pars.archive degree W).initialDegree→ℕ)
    («meta» : (pars.archive degree W).InitialNodeMetadata G baseOrder width m)
    (kernelBase : O.layer.kernels=(pars.archive degree W).initialRecords) (kind : O.layer.kind=0)
    (scratch : volume pars.age+42 ≤ stride pars.age) (extRoom : 2*pay v≤volume pars.age)
    {depth : ℕ} (chunk : pars.perLanePairs=2^depth) :
    CursorSeed F W pars.totalPairs depth (initial pars.age shape)
      ⟨O.id v,j.val%(2^pars.axes),j.val/(2^pars.axes),2*pay v⟩
      (base pars.age 49+5*j.val) (bump (ownerData W pars.age) before)
    := by
  subst nav
  exact Selection.bumped_published_seed pars degree stages r C O seed start pay layers m out prepared warm
    s ran x nodes teams groups done sizes headers bounds requests hdr layerRows startup v j rank below i atID before
    ledger shape G baseOrder width «meta» kernelBase kind scratch extRoom chunk

end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation
open Computability.VPVNP.BurstRAM PrivateRAM RAM PhysicalStage NodePublication NavigationNodeRows TickWorkspace
open RootArchive HistoryStageBody.Physical HistoryStageSetup HistoryNodeDirectory HistoryNodeDirectory.Selected
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {W p H J d l budget : ℕ} {B : TickActiveROM.Layout}
  {fit : RAM.Contraction.Fits (TickWeightedBank.shape F p H J) W} {clock : TickChronology.Clock} {X : State d l}

omit [Fintype F] in
/-- Immutable banks at the actual entry of the selected per-node history loop.
The stage journal is read from navigation's final memory, while the directory
comes from the subsequent native node publication. -/
theorem Selection.stage_kind {r : Run F X} {C : r.Charges} {O : X.ArchiveSites} {seed : LayerData O.layer}
    {n : NodeArchive} {a : RootArchive} {layers : List Layers} {mid out : Memory W} {start pay : X.Site→ℕ}
    (s : Selection r C O seed start pay n a layers budget mid)
    (ran : out=state n (program (r.archiveList s.history C O s.path seed)) mid layers.length)
    (q : NodeRow) (occurs : q∈r.archiveList s.history C O s.path seed) (j : Fin q.layer.count) :
    out (n.banks.nodes+8*(q.layer.first+j.val))=(q.layer.kind:Word W) := by
  rw [ran, ← congrArg List.length s.layout]
  exact (issued_guard _ n mid s.source.room (archive_chronological r s.history C O s.path seed)
    q.layer ⟨q,occurs,rfl⟩ j).1

set_option maxRecDepth 8000 in
/-- Request initialization and the real cursor startup preserve the journal
and the completed S43/S44 rows. -/
theorem Selection.warm_sources (pars : Parameters) (degree : ℕ) (stages : List NavigationDirectory.Stage)
    (r : Run F X) (C : r.Charges) (O : X.ArchiveSites) (seed : LayerData O.layer) (start pay : X.Site→ℕ)
    (layers : List Layers) (mid out prepared warm : Memory W)
    (s : Selection r C O seed start pay (pars.nodeArchive (pars.archive degree W) stages W)
      (parameterArchive pars degree stages W) layers budget mid)
    (ran : out=state (pars.nodeArchive (pars.archive degree W) stages W)
      (program (r.archiveList s.history C O s.path seed)) mid layers.length)
    (x : TickActiveROM.CellInput B clock fit) (nodes : Nodes (parameterArchive pars degree stages W))
    (teams : ℕ) (groups : Fin (parameterArchive pars degree stages W).initialLanes→Fin (parameterArchive pars degree stages W).groups)
    (done : (parameterArchive pars degree stages W).preparedInput x nodes teams layers out groups prepared)
    (sizes : PublishSizes (parameterArchive pars degree stages W) W)
    (headers : B.bounds+4≤2^W) (bounds : B.bounds+4≤base pars.age 20)
    (requests : B.auxRequest+8*B.bits≤base pars.age 20)
    (hdr : 16*layers.length ≤ stride pars.age)
    (layerRows : ∀t∈layers,8*(t.actual.first+t.actual.count) ≤ stride pars.age)
    (startup : ∀a,a<base pars.age 53→warm a=prepared a) :
    WarmSources pars.age pars.banks (r.archiveList s.history C O s.path seed) mid out warm := by
  let S:=stride pars.age
  let a:=parameterArchive pars degree stages W
  have current:a.current<2^W:=(show a.current≤base pars.age 50 by change 41*S≤51*S;omega).trans_lt sizes.address
  have pub (i : ℕ) (lo:base pars.age 43 ≤ i) (hi:i<base pars.age 45) : warm i=out i := by
    have higher:base pars.age 45≤base pars.age 53:=Nat.mul_le_mul_right S (by decide)
    exact (startup i (hi.trans_le higher)).trans (RootArchive.prepared_stage_cell x pars degree stages
      sizes nodes teams layers groups out prepared done current headers bounds requests i (.inr (.inl ⟨lo,hi⟩)))
  have fits (q : NodeRow) (occ : q∈r.archiveList s.history C O s.path seed) (j : Fin q.layer.count) :
      8*(q.layer.first+j.val+1)≤S := by
      have member:(⟨q.layer,q.parent⟩:Layers)∈layers:=by
        rw [←s.layout]
        exact List.mem_map.mpr ⟨q,occ,rfl⟩
      have paid:8*(q.layer.first+q.layer.count)≤S:=layerRows _ member
      exact (Nat.mul_le_mul_left 8 (by have:=j.isLt;omega)).trans paid
  refine ⟨?_,?_,pub,?_,?_⟩
  · intro i lo hi
    have higher:base pars.age 40≤base pars.age 53:=Nat.mul_le_mul_right S (by decide)
    exact (startup i (hi.trans_le higher)).trans (Selection.prepared_journal_cell pars degree stages r C O seed
      start pay layers mid out prepared s ran x nodes teams groups done sizes headers bounds requests hdr layerRows
      i (.inl ⟨lo,hi⟩))
  · intro i lo hi
    exact (startup i hi).trans (Selection.prepared_journal_cell pars degree stages r C O seed
      start pay layers mid out prepared s ran x nodes teams groups done sizes headers bounds requests hdr layerRows
      i (.inr lo))
  · intro q occ j
    have bound:=fits q occ j
    apply Eq.trans _ (s.stage_kind ran q occ j)
    apply pub
    · change 44*S≤45*S+8*(q.layer.first+j.val)
      omega
    · change 45*S+8*(q.layer.first+j.val)<46*S
      omega
  · intro q occ j
    have published:=s.stage_directory ran q occ j
    have bound:=fits q occ j
    apply published.retain
    · intro k _
      have:=k.isLt
      apply pub
      · change 44*S≤45*S+8*(q.layer.first+j.val)+k.val
        omega
      · change 45*S+8*(q.layer.first+j.val)+k.val<46*S
        omega
    · apply pub
      · change 44*S≤44*S+2*(q.layer.first+j.val)+1
        omega
      · change 44*S+2*(q.layer.first+j.val)+1<46*S
        omega

/-- The journal preservation gives the stronger union of header and body
probes consumed by both physical kernel emitters. -/
theorem WarmSources.stage_frame {u : ℕ} {b : Banks} {xs : List NodeRow} {mid out warm : Memory W}
    (src : WarmSources u b xs mid out warm) {first next heads top : ℕ}
    (start : base u 20≤first) (body : base u 20≤heads) (finish : top≤base u 40) :
    ∀ i,(first ≤ i ∧ i<next ∨ heads ≤ i)→i<top→warm i=mid i := by
  intro i lower upper
  exact src.journal i (lower.elim (fun h=>start.trans h.1) (fun h=>body.trans h)) (upper.trans_le finish)

/-- The two physical spans for original and successor incident records. -/
def halfArchiveCell (u i : ℕ) : Prop :=
  (base u 20 ≤ i ∧ i<base u 40) ∨ (base u 49 ≤ i ∧ i<base u 53)

theorem WarmSources.half_frame {u : ℕ} {b : Banks} {xs : List NodeRow} {mid out warm : Memory W}
    (src : WarmSources u b xs mid out warm) {i : ℕ} (cell : halfArchiveCell u i) :
    warm i=mid i ∧ HistoryStageSetup.NavigationCell u i := by
  rcases cell with h|h
  · exact ⟨src.journal _ h.1 h.2,h.1,h.2.trans_le (Nat.mul_le_mul_right _ (by decide : 41≤61))⟩
  · exact ⟨src.seedMetadata _ h.1 h.2,(Nat.mul_le_mul_right _ (by decide : 21≤50)).trans h.1,
      h.2.trans_le (Nat.mul_le_mul_right _ (by decide : 54≤61))⟩

theorem WarmSources.half_rows {u : ℕ} {b : Banks} {xs : List NodeRow} {mid out warm : Memory W}
    (src : WarmSources u b xs mid out warm) {q t : ℕ} {A : State q t} {O : A.ArchiveSites}
    (half : State.HalfRows O (halfArchiveCell u) (fun i=>(mid i).val)) :
    State.HalfRows O (HistoryStageSetup.NavigationCell u) (fun i=>(warm i).val) :=
  half.transfer (fun _ h=>congrArg Fin.val (src.half_frame h).1) (fun _ h=>(src.half_frame h).2)

/-- All scalar LUTs, compactor pages and port catalogues come from the installed S38 words. -/
theorem WarmSources.library {u : ℕ} {b : Banks} {xs : List NodeRow} {mid out warm : Memory W}
    (src : WarmSources u b xs mid out warm) (B : Block F) (height : ℕ)
    (installed : Mounted B height W (base u 38) mid) (size : libraryWords B height ≤ stride u) :
    Mounted B height W (base u 38) warm := by
  refine ⟨fun j=>?_⟩
  have low:base u 20≤base u 38:=Nat.mul_le_mul_right _ (by decide)
  have room:base u 38+stride u≤base u 40:=apart (by decide)
  exact (src.journal _ (low.trans (Nat.le_add_right _ _)) (by have:=j.isLt;omega)).trans (installed.words j)

end
end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation
open Computability.VPVNP.BurstRAM PrivateRAM RAM PhysicalStage NodePublication NavigationNodeRows
open HistoryStageSetup
open scoped Fin.CommRing
noncomputable section
variable {F Pins : Type} [Field F] {W : ℕ}

def warmDirectoryLayer (b : Banks) (m : Memory W) (s : Layer) : Prop :=
  ∀ j : Fin s.count,DirectoryRow b s j m ∧ m (b.nodes+8*(s.first+j.val))=(s.kind:Word W)

/-- The two directories actually used by a leaf of the chronological word visit. -/
def warmDirectoryVisit (b : Banks) (m : Memory W) : Run.WordVisit F Pins :=
  fun _ _ _ _ old _ row=>
    warmDirectoryLayer b m old.layer ∧ warmDirectoryLayer b m row.sites.layer

private theorem layer_first_directory {b : Banks} {warm : Memory W} {d l : ℕ} {X : State d l}
    (r : Run F X) (h : r.plan.History) (C : r.Charges) (O : X.ArchiveSites)
    (p : r.ArchivePath h C O) (initial : LayerData O.layer)
    (read : ∀ q∈r.archiveList h C O p initial,warmDirectoryLayer b warm q.layer) :
    warmDirectoryLayer b warm O.layer := by
  cases r with
  | done => exact read _ (List.mem_cons_self ..)
  | step => exact read _ (List.mem_cons_self ..)

private theorem layer_directory_visits {b : Banks} {warm : Memory W} {d l : ℕ} {X : State d l}
    (r : Run F X) (h : r.plan.History) (J : Run.WordSteps Pins r) (L : X.Words Pins)
    (C : r.Charges) (O : X.ArchiveSites) (p : r.ArchivePath h C O) (initial : LayerData O.layer)
    (read : ∀q∈r.archiveList h C O p initial,warmDirectoryLayer b warm q.layer) :
    r.WordVisits (warmDirectoryVisit b warm) h J L C O p := by
  induction r with
  | done => trivial
  | step R next ih =>
    let tail:= (next h.1).archiveList (Run.tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data
    have after (q : NodeRow) (mem : q∈tail) :
        warmDirectoryLayer b warm q.layer :=
      read q (List.mem_cons_of_mem _ mem)
    exact ⟨⟨read _ (List.mem_cons_self ..),layer_first_directory (next h.1) (Run.tailHistory R next h)
      (C.2 h.1) p.1.sites p.2 p.1.data after⟩,ih h.1 (Run.tailHistory R next h)
      (J.2 h.1) (J.1 L h.1).words (C.2 h.1) p.1.sites p.2 p.1.data after⟩

/-- Both original and successor S43/S44 records are available at every physical
stage, including the last one and stages immediately following the seed. -/
theorem WarmSources.directory_visits {age : ℕ} {b : Banks} {mid out warm : Memory W}
    {d l : ℕ} {X : State d l} {r : Run F X} {h : r.plan.History} {C : r.Charges}
    {O : X.ArchiveSites} {p : r.ArchivePath h C O} {initial : LayerData O.layer}
    (src : WarmSources age b (r.archiveList h C O p initial) mid out warm)
    (J : Run.WordSteps Pins r) (L : X.Words Pins) :
    r.WordVisits (warmDirectoryVisit b warm) h J L C O p :=
  layer_directory_visits r h J L C O p initial (fun q h j=>⟨src.directory q h j,src.kind q h j⟩)

end
end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation
open Computability.VPVNP.BurstRAM PrivateRAM RAM PhysicalStage NodePublication NavigationNodeRows
noncomputable section
variable {F Pins : Type} [Field F] {W : ℕ}

/-- The real source memory describes all lists of the successor, and every
child, half-edge and quota lookup fits in a native word. -/
def stageDataVisit (mid : Memory W) : Run.WordVisit F Pins :=
  fun _ _ _ _ _ _ row=>row.data.Reads (natural mid) ∧ row.data.Below (2^W) (natural mid)

def orderedWordVisit : Run.WordVisit F Pins :=
  fun _ _ l _ _ _ _=>State.OrderedHalves _ l

private theorem ordered_visits {d l : ℕ} {X : State d l} (r : Run F X) (h : r.plan.History)
    (J : Run.WordSteps Pins r) (L : X.Words Pins) (C : r.Charges) (O : X.ArchiveSites)
    (p : r.ArchivePath h C O) (initial : X.OrderedHalves L) :
    r.WordVisits orderedWordVisit h J L C O p := by
  induction r with
  | done=>trivial
  | step R next ih=>exact ⟨initial,ih h.1 (Run.tailHistory R next h) (J.2 h.1)
      (J.1 L h.1).words (C.2 h.1) p.1.sites p.2 (J.1 L h.1).halves⟩

private theorem first_data {mid : Memory W} {d l : ℕ} {X : State d l}
    (r : Run F X) (h : r.plan.History) (C : r.Charges) (O : X.ArchiveSites)
    (p : r.ArchivePath h C O) (seed : LayerData O.layer)
    (read : ∀q∈r.archiveList h C O p seed,q.data.Reads (natural mid) ∧ q.data.Below (2^W) (natural mid)) :
    seed.Reads (natural mid) ∧ seed.Below (2^W) (natural mid) := by
  cases r <;> exact read _ (List.mem_cons_self ..)

private theorem data_visits {mid : Memory W} {d l : ℕ} {X : State d l}
    (r : Run F X) (h : r.plan.History) (J : Run.WordSteps Pins r) (L : X.Words Pins)
    (C : r.Charges) (O : X.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer)
    (read : ∀q∈r.archiveList h C O p seed,q.data.Reads (natural mid) ∧ q.data.Below (2^W) (natural mid)) :
    r.WordVisits (stageDataVisit mid) h J L C O p := by
  induction r with
  | done=>trivial
  | step R next ih=>
    let ys:=(next h.1).archiveList (Run.tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data
    have tail (q : NodeRow) (hq:q∈ys):=read q (List.mem_cons_of_mem _ hq)
    exact ⟨first_data (next h.1) (Run.tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data tail,
      ih h.1 (Run.tailHistory R next h) (J.2 h.1) (J.1 L h.1).words (C.2 h.1) p.1.sites p.2 p.1.data tail⟩

def publicationVisit (b : Banks) (mid warm : Memory W) : Run.WordVisit F Pins :=
  fun R i L ws O c row=>warmDirectoryVisit b warm R i L ws O c row ∧
    orderedWordVisit R i L ws O c row ∧ stageDataVisit mid R i L ws O c row

theorem Selection.publication_visits [Fintype F] {d l budget age : ℕ} {X : State d l} {r : Run F X}
    {C : r.Charges} {O : X.ArchiveSites} {seed : LayerData O.layer} {start pay : X.Site→ℕ}
    {n : NodeArchive} {a : RootArchive} {rows : List Layers} {mid out warm : Memory W} {b : Banks}
    (s : Selection r C O seed start pay n a rows budget mid)
    (pub : WarmSources age b (r.archiveList s.history C O s.path seed) mid out warm)
    (J : Run.WordSteps Pins r) (L : X.Words Pins) (ordered : X.OrderedHalves L) :
    r.WordVisits (publicationVisit b mid warm) s.history J L C O s.path := by
  have data:=data_visits r s.history J L C O s.path seed (mid:=mid) (by
    intro q hq
    obtain ⟨i,rfl⟩:=every_view _ q hq
    exact ⟨s.source.source.reads i,s.source.source.bounds i⟩)
  exact r.wordVisits_pair _ _ s.history J L C O s.path (pub.directory_visits J L)
    (r.wordVisits_pair _ _ s.history J L C O s.path (ordered_visits r s.history J L C O s.path ordered) data)

end
end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

end OAI
