import OAI.ThreeFlat.Diagonal.PhysicalNodeArchiveBounds
import OAI.ThreeFlat.Diagonal.TickBucketScanValues
import OAI.ThreeFlat.RAM.TickScanRanges

namespace OAI
/-! # Every packed node-header word fits at the actual cursor layout -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows PhysicalStage NavigationDirectory
open scoped Classical
noncomputable section

private def PointerFits (W : ℕ) (s : Layer) : Prop :=
  s.kind<2^W ∧ s.children<2^W ∧ s.kernels<2^W ∧ s.incident<2^W

private theorem node_pointers (K : ℕ) (c : Cursor) (t : Stage) :
    let s:=nodeLayer K c t
    let upper:=(allocate K c t).next.heap
    s.children≤upper ∧ s.kernels≤upper ∧ s.incident≤upper := by
  cases t <;> simp only [nodeLayer,allocate,CompressorPacking.Native.ShrinkStage.extraEnd,
    CompressorPacking.Native.ShrinkStage.headerExtra,RefreshStageLayout.extraEnd,RefreshStageLayout.headerExtra]
    <;> simp only [Nat.reduceLT, Nat.reduceEqDiff, ite_false, Nat.add_mul, Nat.mul_add] <;> omega

private theorem head_layer (K : ℕ) (xs : List Stage) (c : Cursor) (s : Layer) :
    ∃ q∈nodeLayers K xs c s,q.actual=s := by
  cases xs <;> exact ⟨_,List.mem_cons_self ..,rfl⟩

/-- The parent base belongs to the following real layer and its owner pointer to
the following allocation. The terminal descriptor uses zero in both columns. -/
private theorem pointer_fields {W : ℕ} (K : ℕ) (xs : List Stage) (c : Cursor) (s : Layer)
    (first : PointerFits W s) (wide : 2<2^W) (heap : (finish K xs c).heap<2^W)
    (ids : ∀ q∈nodeLayers K xs c s,q.actual.first<2^W) :
    ∀ q∈nodeLayers K xs c s,PointerFits W q.actual ∧ q.parent.first<2^W ∧ q.parent.owners<2^W := by
  induction xs generalizing c s with
  | nil =>
    intro q h
    obtain rfl:=List.mem_singleton.mp h
    exact ⟨first,by dsimp;omega,by dsimp;omega⟩
  | cons t tail ih =>
    let next:=(allocate K c t).next
    let layer:=nodeLayer K c t
    let rs:=nodeLayers K tail next layer
    have restIds (q : Layers) (mem : q∈rs) : q.actual.first<2^W := ids q (List.mem_cons_of_mem _ mem)
    have restHeap : (finish K tail next).heap<2^W:=heap
    have end' : next.heap<2^W := by rw [heap_finish] at restHeap;omega
    intro q h
    rcases List.mem_cons.mp h with rfl|mem
    · obtain ⟨q,member,atLayer⟩:=head_layer K tail next layer
      have ord:=restIds q member
      rw [atLayer] at ord
      have owner:=owner_end_eq_next_heap K c t
      refine ⟨first,ord,?_⟩
      change (allocate K c t).words 44<2^W
      change (allocate K c t).next.heap<2^W at end'
      omega
    · have ptr:=node_pointers K c t
      have kind : layer.kind<2^W := by
        change stageKind t < 2^W
        cases t with
        | shrink => exact lt_trans (by decide : 1 < 2) wide
        | refresh => exact wide
      exact ih next layer ⟨kind,ptr.1.trans_lt end',ptr.2.1.trans_lt end',ptr.2.2.trans_lt end'⟩
        restHeap restIds q mem

theorem cursor_tape_bounds {F : Type} [Field F] [Fintype F] (B : Block F) {u rem low stride cells off tariff : ℕ}
    (shape : PhysicalPinsExpr.Shape) (hu : 40≤u) (fixed : directoryCap B≤u)
    (levels : B.levels+1≤u) (factor : B.allocations.sum≤u) (half : low=u^10/2)
    (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6) (pairs : 2*shape.halfBits≤2^(3*u^10)) :
    let W:=16*u^10
    let p:=Parameters.cursor B u rem low stride cells shape off tariff
    let A:=p.archive (2^B.exponent 0) W
    let ss:=(B.repeat (u^8)).directory rem p.axes
    let N:=p.nodeArchive A ss W
    TapeBounds W N (nodeLayers A.K ss A.cursor A.seedLayer) := by
  intro W p A ss N
  let rows:=nodeLayers A.K ss A.cursor A.seedLayer
  have space:=Parameters.node_publication_arena B u rem low stride cells shape off tariff hu levels factor half depth
  have ctr : N.counter=N.banks.current+3 := rfl
  have head : N.counter<N.headerBase := space.counter
  have headers : N.headerBase+16*rows.length≤N.banks.charges := space.header
  have ch : N.banks.charges<2^W := by
    have a:=space.chargeEnd;have b:=space.nodeEnd
    change N.banks.charges+_≤N.banks.nodes at a
    change N.banks.nodes+_<2^W at b
    omega
  have degree : 2^B.exponent 0≤u := by unfold directoryCap at fixed;omega
  have atDepth : p.axes≤u^10+2*u^6 := by change (B.repeat (u^8)).charge+rem≤_;omega
  have seedEnd : A.metadataEnd<2^W := (p.initial_space (2^B.exponent 0) hu degree atDepth).records.endFit
  have seed : PointerFits W A.seedLayer := by
    dsimp only [PointerFits,Archive.seedLayer]
    have base : A.initialRecords+5*A.initialSites≤A.metadataEnd := by unfold Archive.metadataEnd;rw [Nat.add_mul];omega
    have z:=Nat.two_pow_pos W
    exact ⟨z,z,(by omega),base.trans_lt seedEnd⟩
  have heap : (finish A.K ss A.cursor).heap<2^W := space.heap.trans_lt ch
  have roots (q : Layers) (hq : q∈rows) : q.actual.first<2^W := by
    have span := (space.span q hq).2
    change N.banks.nodes+8*(q.actual.first+q.actual.count)<2^W at span
    omega
  have size : 16<2^W:=space.wide
  refine ⟨by omega,head,headers,?_⟩
  intro i j
  let q:=rows.get i
  have mem : q∈rows := List.get_mem rows i
  have dims:=pointer_fields A.K ss A.cursor A.seedLayer seed (by omega) heap roots q mem
  have chEnd : N.banks.charges+2*(q.actual.first+q.actual.count)≤N.banks.nodes := (space.span q mem).1
  have nodeEnd : N.banks.nodes+8*(q.actual.first+q.actual.count)<2^W := (space.span q mem).2
  have index : i.val+1≤rows.length := i.isLt
  have hEnd : hdr N (i.val+1)≤N.banks.charges :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left 16 index) N.headerBase).trans headers
  have frame:=cursor_bounds B (rem:=rem) (low:=low) (stride:=stride) (cells:=cells)
    (off:=off) (tariff:=tariff) shape hu fixed levels factor half depth pairs i
  have ar : q.actual.childCount≤N.childCap:=frame.arity
  have cap : max N.childCap (max N.halfCap N.motifCap)<2^W:=frame.caps
  have child : q.actual.childCount<2^W:= ar.trans_lt ((le_max_left ..).trans_lt cap)
  have finalBit : (if q.parent.finalLayer then 1 else 0) < 2^W := by
    split <;> omega
  obtain ⟨⟨kind,children,kernels,incident⟩,par,owners⟩:=dims
  change header N.banks q.actual q.parent (hdr N (i.val+1)) j.val<2^W
  fin_cases j <;> dsimp only [Fin.val_mk,header] <;>
    first | assumption | omega | (split <;> omega)


end
end ThreeFlat.Diagonal.NavigationPass.NodePublication

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication

open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows RAM.TickActiveROM
open PhysicalStage NavigationDirectory HistoryContraction TickPhaseModel TickChronology
open scoped Classical
noncomputable section
variable {F : Type} [Field F] [Fintype F]

private theorem root_lane_words {u k : ℕ} (hu : 40≤u) (depth : k≤u^10+2*u^6) :
    4*2^k ≤ TickWorkspace.stride u := by
  have lower : u^6 ≤ u^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have age : 40 ≤ u^10 := hu.trans (Nat.le_self_pow (by decide) _)
  calc
    _ = 2^(2+k) := (pow_add ..).symm
    _ ≤ 2^(u^10*4) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = _ := pow_mul ..

/-- Every four-word interval row for the cursor lanes fits before its scan count. -/
theorem cursor_root_space (B : Block F) {u rem low stride cells off tariff : ℕ}
    (shape : PhysicalPinsExpr.Shape) (hu : 40≤u)
    (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6) :
    let W := 16*u^10
    let p := Parameters.cursor B u rem low stride cells shape off tariff
    let A := p.archive (2^B.exponent 0) W
    let ss := (B.repeat (u^8)).directory rem p.axes
    let R := p.rootArchive A (p.nodeArchive A ss W) ss W
    TickWorkspace.base u 5+4*R.initialLanes ≤ TickWorkspace.base u 6 := by
  change TickWorkspace.base u 5+4*2^((B.repeat (u^8)).charge+rem) ≤ TickWorkspace.base u 6
  exact (Nat.add_le_add_left (root_lane_words hu ((Nat.le_add_right _ _).trans depth)) _).trans
    (TickWorkspace.apart (by decide : 5<6))

omit [Fintype F] in
/-- The mounted request, interval, count, and map banks have room for the actual
finite rows, one row per initial cursor lane. -/
theorem cursor_root_scan_ranges (B : Block F) {u rem low : ℕ}
    (shape : PhysicalPinsExpr.Shape) (hu : 40≤u)
    (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6)
    (chunk : shape.bits≤2^(u^10-u^4)) (teams cap q nt ns np : ℕ)
    {S : HistoryContraction.Shape} {P : HistoryContraction.Plan F S} {bits : P.History→ℕ}
    {c : Clock} {span : ℕ}
    (T : Buckets P bits c (TickPhysicalABI.mounted u shape.bits teams cap q nt ns np).bits
      (2^((B.repeat (u^8)).charge+rem)) span) (v : Plan.Terminal P bits) :
    let A := TickPhysicalABI.mounted u shape.bits teams cap q nt ns np
    ScanRanges A (T.finiteRows (A := A) v).length (16*u^10) := by
  intro A
  have rows : (T.finiteRows (A := A) v).length=2^((B.repeat (u^8)).charge+rem) := by
    simp only [Buckets.finiteRows,List.length_map,Plan.bucketRows,BucketRows.pack_length,
      Buckets.rows,ClippedPairBuckets.rows,List.length_ofFn]
  rw [rows]
  have age : 40 ≤ u^10 := hu.trans (Nat.le_self_pow (by decide) _)
  have requests : 8*shape.bits ≤ TickWorkspace.stride u := by
    calc
      _ ≤ 8*2^(u^10-u^4) := Nat.mul_le_mul_left _ chunk
      _ = 2^(3+(u^10-u^4)) := (Nat.pow_add 2 3 (u^10-u^4)).symm
      _ ≤ 2^(u^10*4) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = _ := pow_mul ..
  have minimum := (node_word_space hu).2
  have fit := TickWorkspace.word_space (i := 8) (u := u) (by omega) (by omega)
  exact ScanRanges.mounted u shape.bits teams cap q nt ns np _ _ requests
    (root_lane_words hu ((Nat.le_add_right _ _).trans depth))
    ((Nat.le_add_right _ _).trans fit.le)

end
end ThreeFlat.Diagonal.NavigationPass.NodePublication

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows PhysicalStage NavigationDirectory ApproximateImage
open scoped Fin.CommRing Classical
noncomputable section

private theorem mount_header_bound (base width prefixWords nodeWords total bound dest : ℕ)
    (count : prefixWords+nodeWords ≤ total) (fits : base+width*total ≤ bound)
    (start : bound ≤ dest) : base+width*prefixWords+width*nodeWords ≤ dest := by
  rw [Nat.add_assoc, ← Nat.mul_add]
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left width count) base).trans (fits.trans start)

set_option maxHeartbeats 1600000 in
private theorem cursor_mount_geometry {F : Type} [Field F] [Fintype F] (B : Block F)
    (u rem low stride cells : ℕ) (shape : PhysicalPinsExpr.Shape) (off tariff : ℕ)
    (hu : 40≤u) (levels : B.levels+1≤u) (factor : B.allocations.sum≤u)
    (half : low=u^10/2) (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6)
    (fit : off+(16*u^10)*((Parameters.gridWords B u)++
      (Parameters.cursor B u rem low stride cells shape off tariff).staticWords B (u^8) rem (16*u^10)).length≤ shape.parameterBits)
    (rawLow : 2+shape.advice+shape.teamBits+shape.timeBits+shape.parameterBits≤TickWorkspace.stride u) :
    let W:=16*u^10
    let p:=Parameters.cursor B u rem low stride cells shape off tariff
    let A:=p.archive (2^B.exponent 0) W
    let ss:=(B.repeat (u^8)).directory rem p.axes
    let N:=p.nodeArchive A ss W
    let rs:=nodeLayers A.K ss A.cursor A.seedLayer
    let R:=p.rootArchive A N ss W
    let lib:=Parameters.gridWords B u
    let directory:=A.directory ss (R.rootCount*A.initialDegree) W
    let before:=lib++directory
    let after:=(List.ofFn (fun j : Fin 22=>R.word j))++stageTape rs
    let words:=lib++p.staticWords B (u^8) rem W
    words = before++(nodeTape N.banks N.headerBase rs++after) ∧
      p.rawTables+W*words.length ≤ TickWorkspace.stride u ∧
      N.rawHeader = p.rawTables+W*before.length ∧ N.phase < 2^W ∧
      N.rawHeader+W*(16*rs.length) ≤ N.headerBase ∧ N.headerBase+16*rs.length < 2^W := by
  intro W p A ss N rs R lib directory before after words
  have parts : words=before++(nodeTape N.banks N.headerBase rs++after) := by
    simp only [words,before,after,Parameters.staticWords,List.append_assoc]; rfl
  have span : p.rawTables+W*words.length≤TickWorkspace.stride u := by
    change off+W*words.length≤ shape.parameterBits at fit
    change 2+shape.advice+shape.teamBits+shape.timeBits+off+W*words.length≤_
    omega
  have book : p.codebookWords=lib.length := (Parameters.gridWords_length B u).symm
  have dl : directory.length=64*(ss.length+2) := Archive.directory_length ..
  have atRaw : N.rawHeader=p.rawTables+W*before.length := by
    change p.rawTables+W*p.codebookWords+W*(64*(ss.length+2))=p.rawTables+W*(lib++directory).length
    rw [List.length_append, book, dl]
    exact (Nat.add_assoc _ _ _).trans
      (congrArg (fun size => p.rawTables + size) (Nat.mul_add W lib.length (64*(ss.length+2))).symm)
  have space:=Parameters.node_publication_arena B u rem low stride cells shape off tariff hu levels factor half depth
  have nodeFit : N.banks.charges<2^W := by
    have h:=space.chargeEnd;have z:=space.nodeEnd
    change N.banks.charges+_≤N.banks.nodes at h
    change N.banks.nodes+_<2^W at z
    omega
  have dest : N.headerBase+16*rs.length<2^W:=space.header.trans_lt nodeFit
  have within : before.length+16*rs.length≤words.length := by
    have size : words.length = before.length + (16*rs.length + after.length) := by
      rw [parts]
      simp only [List.length_append, nodeTape_length]
    omega
  have startHeap : TickWorkspace.stride u≤N.headerBase := TickWorkspace.lower u 41
  have apart : N.rawHeader+W*(16*rs.length)≤N.headerBase := by
    rw [atRaw]
    exact mount_header_bound p.rawTables W before.length (16*rs.length) words.length
      (TickWorkspace.stride u) N.headerBase within span startHeap
  have gap : 2≤TickWorkspace.stride u := by
    have agePos : 0 < u^10 := Nat.pow_pos (show 0 < u by omega)
    have power : 2≤2^(u^10) := Nat.le_self_pow (Nat.ne_of_gt agePos) 2
    exact power.trans (Nat.le_self_pow (by decide : 4≠0) _)
  have p0 : TickWorkspace.base u 0+TickWorkspace.stride u≤N.banks.current := TickWorkspace.apart (by decide : 0<40)
  have phase : N.phase<2^W := by
    change TickWorkspace.base u 0+2<2^W
    exact ((Nat.add_le_add_left gap _).trans p0).trans_lt (space.current.trans nodeFit)
  exact ⟨parts,span,atRaw,phase,apart,dest⟩

private theorem framed_parameter_read {W : ℕ} (m original : Memory W)
    (base limit len : ℕ) (word : ℕ → Word W) (span : base+W*len ≤ limit)
    (frame : ∀ x, x < limit → m x = original x)
    (source : ∀ i, i < len → ∀ j, j < W → original (base+W*i+j) =
      (((word i).val.testBit (W-1-j)).toNat : Word W)) :
    ∀ i, i < len → ∀ j, j < W → m (base+W*i+j) =
      (((word i).val.testBit (W-1-j)).toNat : Word W) := by
  intro i hi j hj
  have within := Nat.mul_le_mul_left W (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at within
  exact (frame _ (by omega)).trans (source i hi j hj)

private theorem mount_framed_words {W : ℕ} (N : NodeArchive) (rs : List Layers) (m : Memory W)
    (base : ℕ) (before after words : List ℕ)
    (parts : words = before++(nodeTape N.banks N.headerBase rs++after))
    (atRaw : N.rawHeader = base+W*before.length) (phase : N.phase < 2^W)
    (apart : N.rawHeader+W*(16*rs.length) ≤ N.headerBase) (dest : N.headerBase+16*rs.length < 2^W)
    (read : ∀ i, i < words.length → ∀ j, j < W → m (base+W*i+j) =
      (((words[i]?.getD 0 : Word W).val.testBit (W-1-j)).toNat : Word W)) :
    Mount (image N rs.length) (tapeWord N rs) m := by
  refine mount_tape N rs m base before after atRaw phase apart dest ?_
  intro packed i hi j hj
  have eqWords : packed = words := parts.symm
  rw [eqWords] at hi ⊢
  exact read i hi j hj

set_option maxHeartbeats 1600000 in
/-- Read the S41 node headers directly from the actual mounted public parameter pins
after the stage traversal. Its low-memory frame is used only on those original bits. -/
theorem cursor_mount_tape {F : Type} [Field F] [Fintype F] (B : Block F)
    (u rem low stride cells : ℕ) (shape : PhysicalPinsExpr.Shape) (off tariff : ℕ)
    (D : Fin shape.advice→Bool) (team : Fin shape.teamBits→Bool) (step : Fin shape.timeBits→Bool)
    (initialBits : Fin shape.parameterBits→Bool) (oa na oc nc : Fin shape.bits→Bool)
    (m : Memory (16*u^10)) (hu : 40≤u) (levels : B.levels+1≤u) (factor : B.allocations.sum≤u)
    (half : low=u^10/2) (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6)
    (fit : off+(16*u^10)*((Parameters.gridWords B u)++
      (Parameters.cursor B u rem low stride cells shape off tariff).staticWords B (u^8) rem (16*u^10)).length≤ shape.parameterBits)
    (rawLow : 2+shape.advice+shape.teamBits+shape.timeBits+shape.parameterBits≤TickWorkspace.stride u)
    (frame : let par:=Parameters.cursorMount B u rem low stride cells shape off tariff initialBits
      ∀ x,x<TickWorkspace.stride u → m x=TickMountedPins.memory (w:=16*u^10) (fields D team step par oa na oc nc) x) :
    let W:=16*u^10
    let p:=Parameters.cursor B u rem low stride cells shape off tariff
    let A:=p.archive (2^B.exponent 0) W
    let ss:=(B.repeat (u^8)).directory rem p.axes
    let N:=p.nodeArchive A ss W
    let rs:=nodeLayers A.K ss A.cursor A.seedLayer
    Mount (image N rs.length) (tapeWord N rs) m := by
  intro W p A ss N rs
  let R:=p.rootArchive A N ss W
  let lib:=Parameters.gridWords B u
  let directory:=A.directory ss (R.rootCount*A.initialDegree) W
  let before:=lib++directory
  let after:=(List.ofFn (fun j : Fin 22=>R.word j))++stageTape rs
  let words:=lib++p.staticWords B (u^8) rem W
  have geometry : words = before++(nodeTape N.banks N.headerBase rs++after) ∧
      p.rawTables+W*words.length ≤ TickWorkspace.stride u ∧
      N.rawHeader = p.rawTables+W*before.length ∧ N.phase < 2^W ∧
      N.rawHeader+W*(16*rs.length) ≤ N.headerBase ∧ N.headerBase+16*rs.length < 2^W :=
    cursor_mount_geometry B u rem low stride cells shape off tariff hu levels factor half depth fit rawLow
  obtain ⟨parts,span,atRaw,phase,apart,dest⟩ := geometry
  let word (i : ℕ) : Word W := (words[i]?.getD 0 : ℕ)
  let original : Memory W := TickMountedPins.memory (w:=W)
    (fields D team step (TickParameterWords.mount (w:=W) off words.length word initialBits) oa na oc nc)
  have source : ∀ i, i < words.length → ∀ j, j < W → original (p.rawTables+W*i+j) =
      (((word i).val.testBit (W-1-j)).toNat : Word W) :=
    TickParameterWords.source (w:=W) (q:=shape.advice) (nt:=shape.teamBits) (ns:=shape.timeBits)
      (params:=shape.parameterBits) (a:=shape.bits) D team step initialBits oa na oc nc off words.length word fit
  exact mount_framed_words N rs m p.rawTables before after words parts atRaw phase apart dest
    (framed_parameter_read m original p.rawTables (TickWorkspace.stride u) words.length word span frame source)



end
end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
