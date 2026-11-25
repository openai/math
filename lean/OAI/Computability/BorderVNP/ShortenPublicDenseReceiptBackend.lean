import OAI.Computability.BorderVNP.ShortenPublicDenseReceiptTransport
import OAI.Computability.BorderVNP.PackedRoundCost
import OAI.Computability.BorderVNP.ShortenCompiledAt

/-! # Checked dense successor on the selected joint geometric and numeric input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicDenseReceipt

open Cover Cover.Frame Cover.AddressCircuit Hecke Crossing Epoch Catalog StaticRows CombiningStep
open PreparedBins Framed PublicSegments PublicRelative PublicPopulation PublicRoundInput PublicParallel
open Packing DirectoryCircuit PublicDirectory BankCircuit VPVNP.VerifierNetwork ParseBatchSort
open BorderVNP.PackedHistoryCircuit.Normalized
open scoped Classical BorderVNP.Epoch.Cube

variable {D n m lev d copies V E w seeds : ℕ} [NeZero D]
variable {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)
variable {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Copy number in an evenly padded public table. -/
def copyOf {k v : ℕ} (i : Fin (k*v)) : Fin k := (finProdFinEquiv.symm i).1

/-- The table of a physical site or cable reports the correct owning copy. -/
theorem copyOf_parallelName {k v : ℕ} {T : Fin k → Type*} (id : ∀ i, T i ↪ Fin v) (z : Σ i, T i) :
    copyOf (parallelName id z) = z.1 := congrArg Prod.fst (unflat_flat z.1 _)

/-- Count inputs are indexed by actual cover tile, relative bin and paid
term. The program reads a full binary multiplicity at each of these names. -/
abbrev Seed (lev : ℕ) := (Cube D → Deck (lev+1)) × B.Bin

/-- Shared classifier, selected motion, and the saved sparse fields. -/
noncomputable abbrev Shared (Data : Type) (d n copies V E w : ℕ) :=
  Source Data (↥B.types) (Fin (Fintype.card (PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)))
    (Fintype.card (Cube D)) (d+2*n) copies (copies*V) (copies*E) w

/-- The site's finite catalog and exact target address on the next step. -/
noncomputable abbrev Payload (d n : ℕ) :=
  ProductSlots (Fintype.card (Cube D)) (d+2*n) ⊕ ↥((sitePattern (n := n) B).nextSites e S)

/-- All sparse successor wires and the profile check. -/
noncomputable abbrev Result (d n copies V E seeds w : ℕ) :=
  (Fin (edgeCapacity e (copies*E) seeds) ⊕
    Raw (Payload B e d n) (siteCapacity e (copies*V) seeds) (edgeCapacity e (copies*E) seeds) w w) ⊕ Unit

/-- Address width of a numeric seed name in the selected physical row table. -/
noncomputable abbrev numericWidth (d n : ℕ) :=
  Nat.clog 2 (Fintype.card B.Bin) + keyWidth (Fintype.card (Cube D)) (d+2*n)

/-- The complete classified cable table consumed by the checked dense cut. -/
noncomputable abbrev NumericTable (Data : Type) (d n copies V E w : ℕ) :=
  Table (Shared B Data d n copies V E w) (copies*E) (numericWidth B d n)

/-- Active bits, stable moved bin keys, and true widths of the attained physical cables. -/
noncomputable def numericPins {Data : Type} (d n copies V E w : ℕ) {lev : ℕ} (level : lev+1=d+2*n)
    (field : FieldBit (↥S) (Cube D) (lev+2*n+1) → Data) :
    PublicPopulation.Pins (Fin (copies*E)) (NumericTable B Data d n copies V E w) (numericWidth B d n) w :=
  let deep := fieldAtLevel (show lev+2*n+1=d+2*n+2*n by omega) field
  let pins := jointPins (V := copies*V) (k := w) (w := w) B (factorEnum D) (copyOf (k := copies) (v := E))
    deep (M := Fin (Fintype.card (PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)))
  populationPins (Sum.inr ∘ pins.live) oldField

/-- The old occupancy, orientation, endpoints and padding columns beside the numeric keys. -/
noncomputable def numericColumns (Data : Type) (d n copies V E w : ℕ) :
    Columns (NumericTable B Data d n copies V E w) (copies*E) D w := columns occupied oldField

/-- Numeric code of the absolute tile and relative bin at the actual geometric level. -/
noncomputable def numericCode {lev d n : ℕ} (level : lev+1=d+2*n) :
    Seed B lev ↪ Fin (2^numericWidth B d n) :=
  (seedLevel level).toEmbedding.trans (addressCode (factorEnum D) (binCode B.Bin))

private noncomputable def retainedTable {X Table Geo Word Out : Type} [Fintype X] [Fintype Table] [Fintype Geo]
    [Fintype Word] [Fintype Out] (pre : Frame X (Table ⊕ Geo)) (check : Frame ((Table ⊕ Geo) ⊕ Word) Out) :
    Frame (X ⊕ Word) (Table ⊕ Out) :=
  (check.withInput.select (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr)).subst (withWords pre)

private theorem retainedTable_size {X Table Geo Word Out : Type} [Fintype X] [Fintype Table] [Fintype Geo]
    [Fintype Word] [Fintype Out] (pre : Frame X (Table ⊕ Geo)) (check : Frame ((Table ⊕ Geo) ⊕ Word) Out) :
    (retainedTable pre check).size = pre.size+check.size := by
  simp only [retainedTable,Frame.subst_size,withWords_size,Frame.select_size,Frame.withInput_size]

private theorem retainedTable_eval {X Table Geo Word Out : Type} [Fintype X] [Fintype Table] [Fintype Geo]
    [Fintype Word] [Fintype Out] (pre : Frame X (Table ⊕ Geo)) (check : Frame ((Table ⊕ Geo) ⊕ Word) Out)
    (x : X → Bool) (z : Word → Bool) :
    (retainedTable pre check).eval (Sum.elim x z) =
      Sum.elim (pre.eval x ∘ Sum.inl) (check.eval (Sum.elim (pre.eval x) z)) := by
  funext i; cases i <;> simp [retainedTable,withWords_eval]

variable {Data : Type} [Fintype Data]

set_option maxHeartbeats 1800000 in
/-- For any geometric installation returned for the selected labels and
samples, one common circuit checks the words and saves its actual dense
successor. The old site's payload is only read at genuinely occupied IDs. -/
def BackendReads (P : Type) (bits : P → ℕ) (level : lev+1=d+2*n)
    (field : FieldBit (↥S) (Cube D) (lev+2*n+1) → Data)
    (seed : ((Cube D → Deck (d+2*n)) × B.Bin) ≃ Fin seeds)
    (f : Frame (Shared B Data d n copies V E w ⊕ Words (Seed B lev) e.count w) (Result B e d n copies V E seeds w)) : Prop :=
  ∀ (child : Fin copies → PlacedPack D P bits K (Cube D) (lev+2*n))
    (site : ∀ i, (child i).pack.layout.Site ↪ Fin V) (row : ∀ i, (child i).pack.layout.Edge ↪ Fin E)
    (dummy : ∀ i, Fin E → (child i).pack.layout.Site)
    (occ : Fin (copies*E) → Bool) (oldRaw : Raw Data (copies*V) (copies*E) w w → Bool)
    (cls : Classified Data (↥B.types) (copies*V) (copies*E) w w → Bool)
    (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
    (ω : Fin copies → PackSample (lattice 1) elliptic (Cube D) (lev+1) n),
    let old := parallelName site
    let slot := parallelName row
    let hole := parallelDummy dummy
    let physSeed := (seedLevel level).trans seed
    let nextHole := nextDummy e (raw child) slot hole physSeed
    let enum := factorEnum D
    let pick := fun i => sampledChoice (candidateEnum D n) (ω i)
    let shift := fun i j => deckCast level ((ω i).2.2 j)
    let x := Sum.elim (Sum.elim occ oldRaw) (Sum.elim (motionWires enum pick shift) cls)
    (∀ j, occ j = true ↔ j ∈ Set.range slot) →
    SegmentReady S (raw child).layout old slot hole (fun v => (child v.1).site v.2) field
      (fun c => (child c.1).charged c.2) oldRaw →
    PhysicalReads B enum (by omega) (fieldAtLevel (Nat.add_right_comm lev (2*n) 1) field) (fun i => (child i).pack)
      (fun i => (child i).active) (childSites child) L slot cls →
    ∀ (maxWidth : ℕ), (∑ c, (raw child).layout.width c) ≤ maxWidth →
      Nat.clog 2 (widthMultiplier e*maxWidth+1) ≤ w →
    ∀ (g : B.DensePlacement child L ω slot m),
      g.old = movedOld (fun i => (child i).pack) ω (childSites child) →
      g.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart →
      g.project = (fun a => tileProject a.1) →
      let s := B.densePlacedStep child L ω slot g
      ∀ z : Words (Seed B lev) e.count w → Bool, let y := f.eval (Sum.elim x z)
        (y (.inr ()) = true ↔ Accepted e s.matched (fun a t j => z (a,t,j))) ∧
        ∀ hist : s.Index e, (∀ a t, (hist a).val t = value (fun j => z (a,t,j))) →
          (s.directory e old physSeed.toEmbedding nextHole hist).dense.Reads ((sitePattern (n := n) B).nextSites e S)
            (segmentField enum ((sitePattern (n := n) B).nextSites e S) level) (y ∘ Sum.inl)

set_option maxHeartbeats 1800000 in
/-- The numeric table and the dense successor are certified together on the selected
labels, motions, placed stage, and exact same guess word. -/
def BackendTableReads (P : Type) (bits : P → ℕ) (level : lev+1=d+2*n)
    (field : FieldBit (↥S) (Cube D) (lev+2*n+1) → Data)
    (seed : ((Cube D → Deck (d+2*n)) × B.Bin) ≃ Fin seeds)
    (f : Frame (Shared B Data d n copies V E w ⊕ Words (Seed B lev) e.count w) (NumericTable B Data d n copies V E w ⊕ Result B e d n copies V E seeds w)) : Prop :=
  ∀ (child : Fin copies → PlacedPack D P bits K (Cube D) (lev+2*n))
    (site : ∀ i, (child i).pack.layout.Site ↪ Fin V) (row : ∀ i, (child i).pack.layout.Edge ↪ Fin E)
    (dummy : ∀ i, Fin E → (child i).pack.layout.Site)
    (occ : Fin (copies*E) → Bool) (oldRaw : Raw Data (copies*V) (copies*E) w w → Bool)
    (cls : Classified Data (↥B.types) (copies*V) (copies*E) w w → Bool)
    (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
    (ω : Fin copies → PackSample (lattice 1) elliptic (Cube D) (lev+1) n),
    let old := parallelName site
    let slot := parallelName row
    let hole := parallelDummy dummy
    let physSeed := (seedLevel level).trans seed
    let nextHole := nextDummy e (raw child) slot hole physSeed
    let enum := factorEnum D
    let pick := fun i => sampledChoice (candidateEnum D n) (ω i)
    let shift := fun i j => deckCast level ((ω i).2.2 j)
    let x := Sum.elim (Sum.elim occ oldRaw) (Sum.elim (motionWires enum pick shift) cls)
    (∀ j, occ j = true ↔ j ∈ Set.range slot) →
    SegmentReady S (raw child).layout old slot hole (fun v => (child v.1).site v.2) field
      (fun c => (child c.1).charged c.2) oldRaw →
    PhysicalReads B enum (by omega) (fieldAtLevel (Nat.add_right_comm lev (2*n) 1) field) (fun i => (child i).pack)
      (fun i => (child i).active) (childSites child) L slot cls →
    ∀ (maxWidth : ℕ), (∑ c, (raw child).layout.width c) ≤ maxWidth →
      Nat.clog 2 (widthMultiplier e*maxWidth+1) ≤ w →
    ∀ (g : B.DensePlacement child L ω slot m),
      g.old = movedOld (fun i => (child i).pack) ω (childSites child) →
      g.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart →
      g.project = (fun a => tileProject a.1) →
      let s := B.densePlacedStep child L ω slot g
      ∀ z : Words (Seed B lev) e.count w → Bool, let output := f.eval (Sum.elim x z)
        let y := output ∘ Sum.inr
        Ready e (numericPins B d n copies V E w level field) (numericColumns B Data d n copies V E w)
          (numericCode B level) physSeed (raw child) (B.publicBin child L ω) (fun _ => true) old slot nextHole
          (output ∘ Sum.inl) ∧
        ((y (.inr ()) = true ↔ Accepted e s.matched (fun a t j => z (a,t,j))) ∧
        ∀ hist : s.Index e, (∀ a t, (hist a).val t = value (fun j => z (a,t,j))) →
          (s.directory e old physSeed.toEmbedding nextHole hist).dense.Reads ((sitePattern (n := n) B).nextSites e S)
            (segmentField enum ((sitePattern (n := n) B).nextSites e S) level) (y ∘ Sum.inl))

omit [Fintype Data] in
set_option maxHeartbeats 2500000 in
/-- Compile the sparse numeric input, moved site rows and checked dense
successor at a single fixed fan-in. The fixed gate constants precede all
tile levels, row counts, widths, and local port alphabets. -/
theorem backend_table_frames (hm : 0 < m) (n : ℕ) :
    ∃ C p F s : ℕ, ∀ {P : Type} {bits : P → ℕ} (d lev copies V E seeds w : ℕ), 1 ≤ d → (level : lev+1=d+2*n) →
      ∀ (Data : Type) [Fintype Data] (field : FieldBit (↥S) (Cube D) (lev+2*n+1) → Data)
        (seed : ((Cube D → Deck (d+2*n)) × B.Bin) ≃ Fin seeds),
        seeds ≤ 2^w → siteCapacity e (copies*V) seeds ≤ 2^w → edgeCapacity e (copies*E) seeds ≤ 2^w →
        ∃ pf : Frame (Shared B Data d n copies V E w) (NumericTable B Data d n copies V E w),
        ∃ f : Frame (Shared B Data d n copies V E w ⊕ Words (Seed B lev) e.count w) (NumericTable B Data d n copies V E w ⊕ Result B e d n copies V E seeds w),
          pf.size ≤ f.size ∧ (∀ x z, f.eval (Sum.elim x z) ∘ Sum.inl = pf.eval x) ∧ (∀ l, d+1 ≤ l → Nat.clog 2 (seeds+copies*E) + (Nat.clog 2 (Fintype.card B.Bin)+keyWidth (Fintype.card (Cube D)) (d+2*n)) + w+1 ≤ l →
            w+Nat.clog 2 (e.count+1)+1 ≤ l →
            f.size ≤ (1+copies*E*(C*(d+1)^p)+copies*E*Nat.clog 2 (Fintype.card B.Bin)*(2*Fintype.card B.Bin+1)+1) +
              seeds*((sitePattern (n := n) B).bins+90*Fintype.card (Cube D)*(d+2*n+1)) +
              (copies*V+copies*E+seeds+1)*F*l^s) ∧ BackendTableReads B e P bits level field seed f := by
  let enum := factorEnum D
  let index := candidateEnum D n
  let pat := sitePattern (n := n) B
  obtain ⟨C,p,prepare⟩ := ready_from_classified_frames e B enum index
  obtain ⟨U,a,U',a',G,b,compile⟩ := prepared_frames e enum pat S hm
  obtain ⟨F,s,budget⟩ := round_cost_polylog e U a U' a' G b
  refine ⟨C,p,F,s,?_⟩
  intro P bits d lev copies V E seeds w hd level Data instData field seed hn hs he
  let deep := fieldAtLevel (show lev+2*n+1=d+2*n+2*n by omega) field
  let physSeed := (seedLevel level).trans seed
  let code := (seedLevel level).toEmbedding.trans (addressCode enum (binCode B.Bin))
  let radius := fun t : B.types => t.val.radius
  let perm := CanonicalPlacement.perm (T := Cube D → Deck (lev+1)) radius B.chart
  let k := Nat.clog 2 (Fintype.card B.Bin)+keyWidth (Fintype.card (Cube D)) (d+2*n)
  let pins := jointPins (V := copies*V) (k := w) (w := w) B enum (copyOf (k := copies) (v := E)) deep (M := Fin (Fintype.card (PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)))
  let src := Shared B Data d n copies V E w
  let table := Table src (copies*E) k
  let num : Pins (Fin (copies*E)) table k w := populationPins (Sum.inr ∘ pins.live) oldField
  let col : Columns table (copies*E) D w := columns occupied oldField
  obtain ⟨pre,preSize,preOut⟩ := prepare d hd Data (copies*V) (copies*E) w copies seeds copyOf deep seed
  let geo := BatchPorts (Fintype.card (Cube D)) pat S d copies (copies*V) seeds
  let identity := Frame.initial (id : table ⊕ geo → table ⊕ geo)
  obtain ⟨check,size,correct⟩ := compile (B := B.Bin) (P := P) (bits := bits) d lev (lev+2*n) copies
    (copies*V) (copies*E) seeds k w hd level identity num col code physSeed perm copyOf hn hs he
  let f := retainedTable pre check
  let pf := pre.select Sum.inl
  refine ⟨pf,f,?_,?_,?_,?_⟩
  · exact (Frame.select_size pre Sum.inl).le.trans ((Nat.le_add_right _ _).trans_eq (retainedTable_size pre check).symm)
  · intro x z
    funext j
    exact (congrFun (retainedTable_eval pre check x z) (.inl j)).trans (Frame.select_eval pre Sum.inl x j).symm
  · intro l hdl words guesses
    have card : Fintype.card (Seed B lev) = seeds := (Fintype.card_congr physSeed).trans (Fintype.card_fin seeds)
    let route : table → (table ⊕ BatchPorts (Fintype.card (Cube D)) pat S d copies (copies*V) seeds) ⊕
        Words (Seed B lev) e.count w := Sum.inl ∘ Sum.inl
    have part := budget (copies*E) (copies*V) k w d l (mapPins route num) code (by omega) hdl (by rwa [card]) guesses
    rw [card] at part
    have ca : Fintype.card ((Cube D → Deck (lev+1)) × B.Bin) = seeds := card
    rw [ca] at size
    simp only [identity,Frame.initial_size,zero_add] at size
    have hsize := Nat.add_le_add preSize (size.trans (by simpa only [Nat.add_assoc] using part))
    exact (retainedTable_size pre check).le.trans (by simpa only [Nat.add_assoc] using hsize)
  intro child site row dummy occ oldRaw cls L ω old slot hole physical nextHole en pick shift x present ready read bound total room g hold hchart hproj stage z output y
  let L' := Labels.transport B L (congrArg (·+2*n) level)
  obtain ⟨numeric,geo⟩ := preOut (fun i => (child i).pack) (fun i v => levelCast (congrArg (·+2*n) level) (childSites child i v))
    (fun i => (child i).active) L' old slot hole occ oldRaw cls (copyOf_parallelName row) present ready.names
    (child_reads_atLevel B enum field child L slot cls hd level read) pick shift bound total room
  have tags := tags_atLevel B index level (fun i => (child i).pack) (fun i => (child i).active) (childSites child) L ω
  change Ready e num col (addressCode enum (binCode B.Bin)) seed (raw child) _ _ old slot _ (pre.eval x ∘ Sum.inl) at numeric
  have hh : jointTags B (fun j => (index j).1) (fun j => (index j).2) (fun i => (child i).pack) (fun i => (child i).active)
      (fun i v => levelCast (congrArg (·+2*n) level) (childSites child i v)) L' pick shift =
      fun c => (B.publicBin child L ω c).map (seedLevel level) := tags
  rw (config := {transparency := .all}) [hh] at numeric
  have phys := ready_atLevel e level num col (addressCode enum (binCode B.Bin)) seed (raw child)
    (B.publicBin child L ω) old slot hole (pre.eval x ∘ Sum.inl) numeric
  let mem := fun i v => ready.valid ⟨i,v⟩
  let pub := B.densePublicPlacement child stage ω mem hold hchart hproj
  obtain ⟨valid,payload⟩ := ready.fields_atLevel (show lev+2*n+1=d+2*n+2*n by omega)
  have siteRead := dense_preFields_reads B child stage ω mem hold hchart hproj enum index hd level copyOf old
    (copyOf_parallelName site) seed deep oldRaw valid payload
  have gread : PlacementReads stage.input stage.label stage.perm enum pat S copyOf stage.placed pub old
      physical.toEmbedding (pre.eval x ∘ Sum.inr) := geo ▸ siteRead
  have pass : identity.eval (pre.eval x) = pre.eval x := funext (Frame.initial_eval id _)
  have checked := correct child slot (B.publicBin child L ω) (fun _ => true) g old nextHole (pre.eval x) z
  rw [pass] at checked
  have ⟨flag,next⟩ := checked phys
  have actual := retainedTable_eval pre check x z
  have left : output ∘ Sum.inl = pre.eval x ∘ Sum.inl := congrArg (· ∘ Sum.inl) actual
  have right : y = check.eval (Sum.elim (pre.eval x) z) := congrArg (· ∘ Sum.inr) actual
  rw [left,right]
  exact ⟨phys,flag,next pub gread⟩

omit [Fintype Data] in
set_option maxHeartbeats 2500000 in
/-- Compile the sparse numeric input, moved site rows and checked dense
successor at a single fixed fan-in. The fixed gate constants precede all
tile levels, row counts, widths, and local port alphabets. -/
theorem backend_frames (hm : 0 < m) (n : ℕ) :
    ∃ C p F s : ℕ, ∀ {P : Type} {bits : P → ℕ} (d lev copies V E seeds w : ℕ), 1 ≤ d → (level : lev+1=d+2*n) →
      ∀ (Data : Type) [Fintype Data] (field : FieldBit (↥S) (Cube D) (lev+2*n+1) → Data)
        (seed : ((Cube D → Deck (d+2*n)) × B.Bin) ≃ Fin seeds),
        seeds ≤ 2^w → siteCapacity e (copies*V) seeds ≤ 2^w → edgeCapacity e (copies*E) seeds ≤ 2^w →
        ∃ f : Frame (Shared B Data d n copies V E w ⊕ Words (Seed B lev) e.count w) (Result B e d n copies V E seeds w),
          (∀ l, d+1 ≤ l → Nat.clog 2 (seeds+copies*E) + (Nat.clog 2 (Fintype.card B.Bin)+keyWidth (Fintype.card (Cube D)) (d+2*n)) + w+1 ≤ l →
            w+Nat.clog 2 (e.count+1)+1 ≤ l →
            f.size ≤ (1+copies*E*(C*(d+1)^p)+copies*E*Nat.clog 2 (Fintype.card B.Bin)*(2*Fintype.card B.Bin+1)+1) +
              seeds*((sitePattern (n := n) B).bins+90*Fintype.card (Cube D)*(d+2*n+1)) +
              (copies*V+copies*E+seeds+1)*F*l^s) ∧ BackendReads B e P bits level field seed f := by
  obtain ⟨C,p,F,s,build⟩ := backend_table_frames B e hm n
  refine ⟨C,p,F,s,?_⟩
  intro P bits d lev copies V E seeds w hd level Data instData field seed hn hs he
  obtain ⟨_,f,_,_,cost,reads⟩ := build (P := P) (bits := bits) d lev copies V E seeds w hd level Data field seed hn hs he
  refine ⟨f.select Sum.inr,by simpa only [Frame.select_size] using cost,?_⟩
  intro child site row dummy occ oldRaw cls L ω old slot hole physical nextHole en pick shift x present ready read
    bound total room g hold hchart hproj stage z y
  have projected : y = f.eval (Sum.elim x z) ∘ Sum.inr := funext fun j => Frame.select_eval ..
  rw [projected]
  exact (reads child site row dummy occ oldRaw cls L ω present ready read bound total room g hold hchart hproj z).2

end Shortening.PublicDenseReceipt

end BorderVNP
end Computability
end OAI
