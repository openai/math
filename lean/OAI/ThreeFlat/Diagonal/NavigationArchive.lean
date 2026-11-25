import OAI.ThreeFlat.RAM.HeaderScanLayout
import OAI.ThreeFlat.Diagonal.NavigationHistoryWindow
import OAI.ThreeFlat.Diagonal.NavigationPackedMount
import OAI.ThreeFlat.Diagonal.NavigationArchiveDirectory
import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily
import OAI.ThreeFlat.RAM.AdmissionPost
import OAI.ThreeFlat.Diagonal.NavigationBody
import OAI.ThreeFlat.Diagonal.SharedHistoryRegister
import OAI.ThreeFlat.Diagonal.ProgramDirectory
import OAI.ThreeFlat.RAM.InitialRelayBootstrap
import OAI.ThreeFlat.RAM.TerminalWireArchive

namespace OAI
/-! # Two-stage startup and physical suffix verification for the diagonal tick navigator -/

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure PhysicalStage
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {W : ℕ}

namespace RawHistogram

/-- Decode just one big-endian count word of the input. The definition applies to every raw
bitstring, including strings that fail the stage admission checks. -/
def word (raw : ℕ → Bool) (i : ℕ) : Word W :=
  MotifBinaryPacking.word W (fun j => raw (W*i+(W-1-j.val)))

theorem digit (raw : ℕ → Bool) (i j : ℕ) (hj : j<W) :
    (word (W:=W) raw i).val.testBit (W-1-j)=raw (W*i+j) := by
  let b : Fin W := ⟨W-1-j,by omega⟩
  have h := congrFun ((MotifBinaryPacking.word W).symm_apply_apply
    (fun z : Fin W => raw (W*i+(W-1-z.val)))) b
  change (word raw i).val.testBit (W-1-j)=raw (W*i+(W-1-(W-1-j))) at h
  simpa only [show W-1-(W-1-j)=j by omega] using h

def stage (M K : ℕ) (raw : ℕ → Bool) (first : ℕ) : HistogramRegister.Words M K W :=
  fun i k => word raw (first+i.val*K+k.val)

/-- The real stage parser sees its consecutive substring of the original AUX register.
The stage starts after exactly `first` complete words. -/
theorem bit_stage (M K : ℕ) (raw : ℕ → Bool) (first : ℕ) :
    HistogramRegister.bitTable (stage (W:=W) M K raw first) =
      (fun j => raw (W*first+j.val)) := by
  funext j
  obtain ⟨⟨u,b⟩,rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective u
  change HistogramRegister.bitTable _ (HistogramRegister.address i k b)=
    raw (W*first+(HistogramRegister.address i k b).val)
  rw [HistogramRegister.bitTable_at,HistogramRegister.address_val]
  change (word (W:=W) raw _).val.testBit (W-1-b.val)=_
  rw [digit _ _ _ b.isLt]
  congr 1; ring

theorem stage_prefix (M K : ℕ) (raw : ℕ → Bool) (first cap : ℕ)
    (fit : W*first+M*K*W≤cap) :
    ((List.ofFn (fun i : Fin cap => raw i.val)).drop (W*first)).take (M*K*W)=
      List.ofFn (HistogramRegister.bitTable (stage (W:=W) M K raw first)) := by
  rw [bit_stage]
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_ofFn]
    omega
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]

/-- Start the physical twenty-row packer on the selected old/new tape. The resulting memory
supplies any later stage with its genuine decoded words. -/
theorem generate (x : PackedStageArchive.Layout) {p r k : ℕ} (M : Machine W p r k)
    (pc : Fin 20 ↪ Fin p) (reg : Fin 8 ↪ Fin r) (pub : Fin 0 → Fin k) (exit : Fin p)
    (installed : (PackedStageArchive.block x).Installed M pc reg pub exit)
    (c : Config W p r) (m : Memory W) (entry : c.pc=pc 0) (phaseFit : x.phase<2^W)
    (raw : ℕ→Bool)
    (apart : x.destination+x.count≤x.source m ∨ x.source m+W*x.count≤x.destination)
    (dstFit : x.destination+x.count<2^W) (srcFit : x.source m+W*x.count<2^W)
    (input : ∀ i<W*x.count, m (x.source m+i)=((raw i).toNat : Word W)) :
    ∃ out, advance M.program (x.count*(5*W+6)+10) c m =
        some (out,fillSegment x.destination x.count (fun j=>word raw (j-x.destination)) m) ∧
      out.pc=exit := by
  apply PackedStageArchive.generate x M pc reg pub exit installed c m entry phaseFit _ apart dstFit srcFit
  intro i hi b hb
  rw [Nat.add_sub_cancel_left,digit raw i b hb,Nat.add_assoc]
  exact input (W*i+b) (by have := Nat.mul_le_mul_left W (Nat.succ_le_of_lt hi); rw [Nat.mul_succ] at this; omega)

theorem stage_loaded (raw : ℕ→Bool) (dest count first M K : ℕ) (fit : first+M*K≤count)
    (m : Memory W) (i : Fin M) (k : Fin K) :
    fillSegment dest count (fun j=>word raw (j-dest)) m (dest+first+i.val*K+k.val)=
      stage (W:=W) M K raw first i k := by
  have h : i.val*K+k.val<M*K := by
    have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    have := k.isLt
    omega
  simp [fillSegment,stage,show dest≤dest+first+i.val*K+k.val by omega,
    show dest+first+i.val*K+k.val<dest+count by omega,
    show dest+first+i.val*K+k.val-dest=first+i.val*K+k.val by omega]

end RawHistogram

def Archive.initialField (A : Archive) (i : ℕ) : PhysicalPinsExpr.Formula 1 :=
  MotifRows.field (.load (.lit A.control)) i

def Archive.initialOffset (A : Archive) (i : ℕ) : PhysicalPinsExpr.Formula 1 :=
  .cut (.reg 0) (A.initialField i)

def Archive.initialKernel (A : Archive) : PhysicalPinsExpr.Formula 1 :=
  let row := PhysicalPinsExpr.Formula.op .div (A.initialOffset 7) (.lit 5)
  let col := PhysicalPinsExpr.Formula.op .mod (A.initialOffset 7) (.lit 5)
  .select .eq col (.lit 0) (.load (.lit A.control)) (.select .eq col (.lit 1) row
    (.select .eq col (.lit 2) (.lit 0) (.select .eq col (.lit 3)
      (.op .mod row (A.initialField 6)) (.op .div row (A.initialField 6)))))

def Archive.initialHalfHeader (A : Archive) : PhysicalPinsExpr.Formula 1 :=
  let row := PhysicalPinsExpr.Formula.op .div (A.initialOffset 9) (.lit 2)
  let col := PhysicalPinsExpr.Formula.op .mod (A.initialOffset 9) (.lit 2)
  .select .eq col (.lit 0) (.lit (2*A.initialDegree))
    (.op .add (A.initialField 11) (.op .mul row (.lit (8*A.initialDegree))))

def Archive.initialHalf (A : Archive) : PhysicalPinsExpr.Formula 1 :=
  let slots := PhysicalPinsExpr.Formula.op .mul (A.initialField 4) (A.initialField 5)
  let q : CompressorPacking.Native.ShrinkStage.Halves.HalfColumns :=
    ⟨A.initialField 6,A.initialField 0,slots,A.initialField 2⟩
  CompressorPacking.Native.ShrinkStage.Halves.record q A.initialDegree (A.initialOffset 11)

/-- The leaf evaluator receives the site, remaining lane and cursor axis in the five-word
kernel row. Each incoming half addresses its source through the reverse graph columns. -/
def Archive.initialMetadata (A : Archive) : Procedure W :=
  let current := (A.control : Word W)
  (HeaderScan.procedure current 7 8 (HeaderScan.closed A.initialKernel)).seq
    ((HeaderScan.procedure current 9 10 (HeaderScan.closed A.initialHalfHeader)).seq
      (HeaderScan.procedure current 11 12 (HeaderScan.closed A.initialHalf)))

theorem Archive.seed_at (A : Archive) (ss : List NavigationDirectory.Stage) (finalEdges W : ℕ) (j : Fin 64) :
    (A.directory ss finalEdges W)[j.val]?=some (A.seedWords j.val) := by
  rw [Archive.directory,List.getElem?_append_left (by simp)]
  simp only [List.getElem?_ofFn,dite_eq_left j.isLt]

theorem Archive.stage_at (A : Archive) (pre : List NavigationDirectory.Stage) (s : NavigationDirectory.Stage)
    (post : List NavigationDirectory.Stage) (finalEdges W : ℕ) (j : Fin 64) :
    (A.directory (pre++s::post) finalEdges W)[64+64*pre.length+j.val]?=
      some ((NavigationDirectory.allocate A.K (NavigationDirectory.finish A.K pre A.cursor) s).words j.val) := by
  have n : 64*pre.length+j.val<64*(pre++s::post).length := by
    rw [List.length_append,List.length_cons,Nat.mul_add,Nat.mul_add]
    have := j.isLt
    omega
  rw [Archive.directory,List.getElem?_append_right (by simp only [List.length_ofFn]; omega),
    List.length_ofFn,show 64+64*pre.length+j.val-64=64*pre.length+j.val by omega,
    List.getElem?_append_left (by rw [NavigationDirectory.tape_length]; exact n)]
  exact NavigationDirectory.tape_header A.K pre s post A.cursor j

/-- Recover the live header from the actual packed immutable directory. A caller may
have changed the cursor and any words outside the header since the original hydration. -/
theorem Archive.stage_header (A : Archive) (pre : List NavigationDirectory.Stage) (s : NavigationDirectory.Stage)
    (post : List NavigationDirectory.Stage) (finalEdges : ℕ) (current : Word W) (m : Memory W)
    (base : A.cursor.header=A.seed+64)
    (pointer : (m current.val).val=(NavigationDirectory.finish A.K pre A.cursor).header)
    (fits : A.seed+(A.directory (pre++s::post) finalEdges W).length<2^W)
    (packed : ∀ i v,64+64*pre.length≤ i → i<64+64*pre.length+64 →
      (A.directory (pre++s::post) finalEdges W)[i]?=some v → (m (A.seed+i)).val=v) :
    RAM.HeaderScan.Scans.Header current m (NavigationDirectory.finish A.K pre A.cursor).header 63
      (NavigationDirectory.allocate A.K (NavigationDirectory.finish A.K pre A.cursor) s).words := by
  refine ⟨pointer,?_,?_⟩
  · rw [NavigationDirectory.header_finish,base]
    rw [Archive.directory_length,List.length_append,List.length_cons] at fits
    omega
  · intro i hi
    let j : Fin 64 := ⟨i,by omega⟩
    have h := packed _ _ (Nat.le_add_right _ j.val) (by have := j.isLt; omega)
      (A.stage_at pre s post finalEdges W j)
    simpa only [NavigationDirectory.header_finish,base,Nat.add_assoc] using h

def Archive.lib (A : Archive) : PackedStageArchive.Layout :=
  ⟨A.phase,A.rawCodebook,A.rawCodebook,A.staticCodebook,A.codebookWords⟩

def Archive.static (A : Archive) (steps : List NavigationDirectory.Stage) (finalEdges W : ℕ) :
    PackedStageArchive.Layout := ⟨A.phase,A.rawStatic,A.rawStatic,A.seed,(A.directory steps finalEdges W).length⟩

/-- Mount the three physical input streams and install the pointer to the seed header. -/
def Archive.boot (A : Archive) (steps : List NavigationDirectory.Stage) (finalEdges : ℕ) : Procedure W :=
  (PackedStageArchive.procedure A.lib).seq ((PackedStageArchive.procedure (A.static steps finalEdges W)).seq
    ((PackedStageArchive.procedure (A.hist steps)).seq (start (A.control : Word W) A.seed)))

private theorem Mount.before {x : PackedStageArchive.Layout} {m : Memory W} {word : ℕ→Word W}
    (h : Mount x word m) (lo n : ℕ) (newData : ℕ→Word W) (phase : x.phase<lo)
    (source : x.source m+W*x.count≤lo) : Mount x word (fillSegment lo n newData m) := by
  have frame (i : ℕ) (hi : i<lo) : fillSegment lo n newData m i=m i := by
    have outside : ¬ lo ≤ i := Nat.not_le_of_gt hi
    simp [fillSegment, outside]
  have ep : x.source (fillSegment lo n newData m)=x.source m := by simp [PackedStageArchive.Layout.source,frame _ phase]
  obtain ⟨a,b,c,raw⟩ := h
  refine ⟨a,by rw [ep]; exact b,c,?_⟩
  intro i hi j hj
  rw [ep,frame]
  · exact raw i hi j hj
  · have z := Nat.mul_le_mul_left W (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at z
    omega

def Archive.tableWord (A : Archive) (steps : List NavigationDirectory.Stage) (finalEdges : ℕ) (p : ℕ) :
    Word W := (((A.directory steps finalEdges W)[p-A.seed]?).getD 0 : ℕ)

/-- Read both public prefix segments from the single parameter-word bit string. Later
node tables in the same mounted parameter vector do not affect either of these scans. -/
theorem Archive.mount_public (A : Archive) (steps : List NavigationDirectory.Stage) (edges : ℕ)
    (library suffix : List ℕ) (m : Memory W)
    (len : A.codebookWords=library.length)
    (src : A.rawStatic=A.rawCodebook+W*library.length)
    (phase : A.phase<2^W) (libLow : A.rawCodebook+W*library.length≤A.staticCodebook)
    (dirLow : A.rawStatic+W*(A.directory steps edges W).length≤A.seed)
    (libFit : A.staticCodebook+library.length<2^W) (dirFit : A.seed+(A.directory steps edges W).length<2^W)
    (bits : let words:=library++(A.directory steps edges W++suffix)
      ∀ i<words.length,∀ j<W,m (A.rawCodebook+W*i+j)=
        ((((words[i]?.getD 0 : ℕ):Word W).val.testBit (W-1-j)).toNat : Word W)) :
    Mount A.lib (fun p=>(library[p-A.staticCodebook]?.getD 0 : ℕ)) m ∧
      Mount (A.static steps edges W) (A.tableWord steps edges) m := by
  have ls : A.lib.source m=A.rawCodebook := by
    change (if m A.phase=1 then A.rawCodebook else A.rawCodebook)=A.rawCodebook
    split <;> rfl
  have ds : (A.static steps edges W).source m=A.rawStatic := by
    change (if m A.phase=1 then A.rawStatic else A.rawStatic)=A.rawStatic
    split <;> rfl
  constructor
  · refine ⟨phase,?_,?_,?_⟩
    · change A.lib.source m+W*A.codebookWords≤A.staticCodebook
      rw [ls,len]
      exact libLow
    · simpa only [Archive.lib,len] using libFit
    · intro i hi j hj
      change i<A.codebookWords at hi
      rw [len] at hi
      rw [ls]
      simpa [Archive.lib,List.getElem?_append_left hi] using bits i (by simp; omega) j hj
  · refine ⟨phase,?_,dirFit,?_⟩
    · change (A.static steps edges W).source m+W*(A.directory steps edges W).length≤A.seed
      rw [ds]
      exact dirLow
    · intro i hi j hj
      change i<(A.directory steps edges W).length at hi
      have inside : library.length+i < (library++(A.directory steps edges W++suffix)).length := by
        simp only [List.length_append]
        omega
      have target:=bits (library.length+i) inside j hj
      rw [List.getElem?_append_right (by omega),show library.length+i-library.length=i by omega,
        List.getElem?_append_left hi] at target
      rw [ds,src]
      simpa only [Archive.static,Archive.tableWord,Nat.mul_add,Nat.add_assoc,Nat.add_sub_cancel_left] using target

theorem Archive.mount_histogram (A : Archive) (steps : List NavigationDirectory.Stage) (m : Memory W)
    (raw : ℕ→Bool) (phase : A.phase<2^W) (low : (A.hist steps).source m+W*A.histWords steps≤A.cursor.dense)
    (fit : A.cursor.dense+A.histWords steps<2^W)
    (bits : ∀ i<W*A.histWords steps,m ((A.hist steps).source m+i)=(raw i).toNat) :
    Mount (A.hist steps) (fun p=>RawHistogram.word raw (p-A.cursor.dense)) m := by
  refine ⟨phase,low,fit,?_⟩
  intro i hi j hj
  change i<A.histWords steps at hi
  have bound:=Nat.mul_le_mul_left W (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at bound
  have read:=bits (W*i+j) (by omega)
  rw [←Nat.add_assoc] at read
  simpa only [Archive.hist,Nat.add_sub_cancel_left,RawHistogram.digit raw i j hj] using read

/-- The real bank loaders read the compact common library, the chronological static table,
and the same raw histogram consumed by the physical history parser. All resulting writes are
specified, including the words left unchanged outside the three destination intervals. -/
theorem Archive.boot_spec (A : Archive) (steps : List NavigationDirectory.Stage) (finalEdges : ℕ)
    (m : Memory W) (library : ℕ→Word W) (raw : ℕ→Bool)
    (first : Mount A.lib library m)
    (second : Mount (A.static steps finalEdges W) (A.tableWord steps finalEdges) m)
    (third : Mount (A.hist steps) (fun j=>RawHistogram.word raw (j-A.cursor.dense)) m)
    (phase : A.phase<A.seed) (high : A.seed≤A.staticCodebook)
    (staticLow : A.rawStatic+W*(A.directory steps finalEdges W).length≤A.seed)
    (histLow : (A.hist steps).source m+W*A.histWords steps≤A.seed) :
    let y := A.static steps finalEdges W
    let z := A.hist steps
    let m₁ := fillSegment A.lib.destination A.lib.count library m
    let m₂ := fillSegment y.destination y.count (A.tableWord steps finalEdges) m₁
    let m₃ := fillSegment z.destination z.count (fun j=>RawHistogram.word raw (j-A.cursor.dense)) m₂
    (A.boot steps finalEdges).Spec (fun p=>p=m) (fun _ out=>out=writeMemory m₃ (A.control:Word W) (A.seed:Word W))
      ((A.lib.count*(5*W+6)+10)+((y.count*(5*W+6)+10)+((z.count*(5*W+6)+10)+3))) := by
  intro y z m₁ m₂ m₃
  have boot : (start (A.control : Word W) (A.seed : Word W)).Spec (fun p=>p=m₃)
      (fun _ out=>out=writeMemory m₃ (A.control:Word W) (A.seed:Word W)) 3 := by
    intro n r k M pc reg pub exit inst data cfg p entry same
    subst p
    exact start_spec _ _ M pc reg pub exit inst data cfg m₃ entry trivial
  have phaseHigh : A.phase<A.lib.destination := phase.trans_le high
  have clean := third.before A.lib.destination A.lib.count library phaseHigh (histLow.trans high)
  have baseline : z.source m₁=z.source m := by
    simp only [m₁,PackedStageArchive.Layout.source,fillSegment,
      show ¬A.lib.destination≤z.phase by exact Nat.not_le.mpr phaseHigh,false_and,ite_false]
  have later := clean.before y.destination y.count (A.tableWord steps finalEdges) phase
    (by change z.source m₁+W*A.histWords steps≤A.seed; rw [baseline]; exact histLow)
  have archive : y.source m+W*y.count≤A.lib.destination := by
    change y.source m+W*y.count≤A.staticCodebook
    simpa only [y,Archive.static,PackedStageArchive.Layout.source,ite_self] using staticLow.trans high
  intro n r k M pc reg pub exit installed words cfg input entry origin
  exact Procedure.Spec.mono
    (Procedure.Spec.seq (mount_spec A.lib library m first)
      (Procedure.Spec.seq (mount_spec y _ m₁
          (second.before A.lib.destination A.lib.count library phaseHigh archive))
        (Procedure.Spec.seq (mount_spec z _ m₂ later) boot (fun _ _ h=>h))
        (fun _ _ h=>h)) (fun _ _ h=>h))
    (fun _ hp=>hp) (by rintro i o ⟨m1,_,m2,_,m3,_,h⟩; exact h) le_rfl
    M pc reg pub exit installed words cfg input entry origin

/-- Codebook, stage header and shared histogram overlays are three disjoint dense archives.
The finite shrinking and refresh passes then consume this mounted memory in chronological order. -/
def active (A : Archive) (B : PhysicalStage.Block F) (blocks residualBits finalEdges : ℕ) : Procedure W :=
  let steps := (B.repeat blocks).directory residualBits A.axes
  let current := (A.control : Word W)
  let counter := ((A.control+3 : ℕ) : Word W)
  (A.boot steps finalEdges).seq
    ((InitialRelayBootstrap.procedure current ⟨A.cursor.graph,A.axes*A.initialDegree,A.cursor.width⟩ A.axes A.initialDegree A.relayWidth).seq
      (A.initialMetadata.seq ((start current A.cursor.header).seq ((start counter blocks).seq
        ((repeated current counter A.K B).seq (TerminalWireArchive.program (A.terminal steps finalEdges W)))))))

/-- During navigation, the static headers from the cursor onward and the original dense
histogram words remain available. The selected-layout flag of an earlier header may change. -/
structure Archive.Live (A : Archive) (steps : List NavigationDirectory.Stage) (edges : ℕ)
    (raw : ℕ→Bool) (cur : Word W) (c : NavigationDirectory.Cursor) (m : Memory W) : Prop where
  pointer : (m cur.val).val=c.header
  headers : ∀ i v,c.header≤A.seed+i → (A.directory steps edges W)[i]?=some v → (m (A.seed+i)).val=v
  counts : ∀ j,j<A.K*(steps.map NavigationDirectory.Stage.motifs).sum →
    m (A.cursor.dense+j)=RawHistogram.word raw j

/-- The output of the static and dense hydration is the initial live archive. Seed-column
and metadata preparation are allowed to change all of the other RAM words before the first
native shrinking instruction, including the register holding the current header pointer. -/
theorem Archive.live_of_boot (A : Archive) (steps : List NavigationDirectory.Stage) (edges : ℕ)
    (raw : ℕ→Bool) (cur : Word W) (pre out : Memory W)
    (pointer : (out cur.val).val=A.cursor.header)
    (disj : A.seed+(A.directory steps edges W).length≤A.cursor.dense)
    (wordFit : ∀ v∈A.directory steps edges W,v<2^W)
    (frame : let mid:=fillSegment A.seed (A.directory steps edges W).length (A.tableWord steps edges) pre
      let endMem:=fillSegment A.cursor.dense (A.histWords steps) (fun j=>RawHistogram.word raw (j-A.cursor.dense)) mid
      ∀ i,(A.cursor.header≤ i ∧ i<A.seed+(A.directory steps edges W).length) ∨
        (A.cursor.dense≤ i ∧ i<A.cursor.dense+A.histWords steps) → out i=endMem i) :
    A.Live steps edges raw cur A.cursor out := by
  refine ⟨pointer,?_,?_⟩
  · intro i v lo get
    have hi : i<(A.directory steps edges W).length := by
      by_contra! le
      simp [List.getElem?_eq_none le] at get
    have eq : (A.directory steps edges W)[i]=v := by simpa [List.getElem?_eq_getElem hi] using get
    have fits:=wordFit v (eq ▸ List.getElem_mem (l:=A.directory steps edges W) (n:=i) hi)
    rw [frame (A.seed+i) (.inl ⟨lo,by omega⟩)]
    have outside : ¬(A.cursor.dense≤A.seed+i ∧ A.seed+i<A.cursor.dense+A.histWords steps) := by omega
    have inside : A.seed≤A.seed+i ∧ A.seed+i<A.seed+(A.directory steps edges W).length := by omega
    simp only [fillSegment,ite_eq_right outside,ite_eq_left inside,Archive.tableWord,Nat.add_sub_cancel_left,
      get,Option.getD_some,Fin.val_cast_of_lt fits]
  · intro j hj
    change j<A.histWords steps at hj
    rw [frame (A.cursor.dense+j) (.inr ⟨by omega,by omega⟩)]
    simp [fillSegment,show A.cursor.dense+j<A.cursor.dense+A.histWords steps by omega]

theorem Archive.Live.header {A : Archive} {pre post : List NavigationDirectory.Stage}
    {s : NavigationDirectory.Stage} {edges : ℕ} {raw : ℕ→Bool} {cur : Word W} {m : Memory W}
    (live : A.Live (pre++s::post) edges raw cur (NavigationDirectory.finish A.K pre A.cursor) m)
    (base : A.cursor.header=A.seed+64)
    (fits : A.seed+(A.directory (pre++s::post) edges W).length<2^W) :
    RAM.HeaderScan.Scans.Header cur m (NavigationDirectory.finish A.K pre A.cursor).header 63
      (NavigationDirectory.allocate A.K (NavigationDirectory.finish A.K pre A.cursor) s).words := by
  apply A.stage_header pre s post edges cur m base live.pointer fits
  intro i v hi _ get
  apply live.headers _ _ _ get
  rw [NavigationDirectory.header_finish,base]
  omega

/-- The terminal sentinel is the last of the same hydrated headers used by each native
stage. The pointer returned by the last actual pass selects this sentinel directly. -/
theorem Archive.Live.terminal_header {A : Archive} {steps : List NavigationDirectory.Stage}
    {edges : ℕ} {raw : ℕ→Bool} {cur : Word W} {m : Memory W}
    (live : A.Live steps edges raw cur (NavigationDirectory.finish A.K steps A.cursor) m)
    (base : A.cursor.header=A.seed+64)
    (fit : A.seed+(A.directory steps edges W).length<2^W) :
    RAM.HeaderScan.Scans.Header cur m (NavigationDirectory.finish A.K steps A.cursor).header 63
      (TerminalWireArchive.header (A.terminal steps edges W)) := by
  refine ⟨live.pointer,?_,?_⟩
  · rw [NavigationDirectory.header_finish,base]
    rw [Archive.directory_length,Nat.mul_add] at fit
    omega
  · intro i hi
    let j : Fin 64 := ⟨i,by omega⟩
    have get : (A.directory steps edges W)[64+64*steps.length+j.val]?=
        some (TerminalWireArchive.header (A.terminal steps edges W) j.val) := by
      rw [Archive.directory,List.getElem?_append_right (by rw [List.length_ofFn];omega),
        List.length_ofFn,show 64+64*steps.length+j.val-64=64*steps.length+j.val by omega,
        List.getElem?_append_right (by rw [NavigationDirectory.tape_length];omega),
        NavigationDirectory.tape_length,Nat.add_sub_cancel_left]
      rw [List.getElem?_ofFn,dite_eq_left j.isLt]
    have addr : A.seed+(64+64*steps.length+j.val)=(NavigationDirectory.finish A.K steps A.cursor).header+i := by
      rw [NavigationDirectory.header_finish,base]
      dsimp [j]
      omega
    simpa only [addr] using live.headers _ _ (by rw [addr];omega) get

theorem Archive.Live.raw {A : Archive} {pre post : List NavigationDirectory.Stage}
    {s : NavigationDirectory.Stage} {edges : ℕ} {raw : ℕ→Bool} {cur : Word W} {m : Memory W}
    (live : A.Live (pre++s::post) edges raw cur (NavigationDirectory.finish A.K pre A.cursor) m)
    (i : Fin s.motifs) (j : Fin A.K) :
    let first:=A.K*(pre.map NavigationDirectory.Stage.motifs).sum
    m ((NavigationDirectory.finish A.K pre A.cursor).dense+A.K*i.val+j.val)=
      RawHistogram.stage (W:=W) s.motifs A.K raw first i j := by
  intro first
  rw [NavigationDirectory.dense_finish]
  change m (A.cursor.dense+first+A.K*i.val+j.val)=RawHistogram.word raw (first+i.val*A.K+j.val)
  rw [show A.cursor.dense+first+A.K*i.val+j.val=A.cursor.dense+(first+i.val*A.K+j.val) by ring]
  apply live.counts
  have cut:=Nat.mul_le_mul_right A.K (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at cut
  have hj:=j.isLt
  simp only [List.map_append,List.map_cons,List.sum_append,List.sum_cons,Nat.mul_add]
  dsimp [first]
  rw [Nat.mul_comm A.K s.motifs]
  omega

/-- A published shrink pass may alter its own word 27 and either kind of pass may allocate
the entire interval from its old to its new heap. Both leave every future header and all
original packed histogram words intact. -/
theorem Archive.Live.advance {A : Archive} {steps : List NavigationDirectory.Stage} {edges : ℕ}
    {raw : ℕ→Bool} {cur : Word W} {c : NavigationDirectory.Cursor} {m out : Memory W}
    (live : A.Live steps edges raw cur c m) (s : NavigationDirectory.Stage)
    (pointer : (out cur.val).val=(NavigationDirectory.allocate A.K c s).next.header)
    (static : A.seed+(A.directory steps edges W).length≤c.heap)
    (dense : A.cursor.dense+A.K*(steps.map NavigationDirectory.Stage.motifs).sum≤c.heap)
    (later : c.header+64≤A.cursor.dense) (control : c.heap≤cur.val)
    (frame : ∀ i,i≠cur.val → i≠c.header+27 → i<c.heap → out i=m i) :
    A.Live steps edges raw cur (NavigationDirectory.allocate A.K c s).next out := by
  have nextHeader : (NavigationDirectory.allocate A.K c s).next.header=c.header+64 := by cases s <;> rfl
  refine ⟨pointer,?_,?_⟩
  · intro i v after get
    rw [nextHeader] at after
    have hi : i<(A.directory steps edges W).length := by
      by_contra! le
      simp [List.getElem?_eq_none le] at get
    rw [frame (A.seed+i) (by omega) (by omega) (by omega)]
    exact live.headers i v (by omega) get
  · intro j hj
    rw [frame (A.cursor.dense+j) (by omega) (by omega) (by omega)]
    exact live.counts j hj

/-- Supplying the genuine branch parser to a native stage is independent of finitary
reindexing of its motif rows. The packed table supplies its W-bit words on the same raw
register that is used by the recursive history parser. -/
theorem Archive.Live.input {A : Archive} {pre post : List NavigationDirectory.Stage}
    {s : NavigationDirectory.Stage} {edges : ℕ} {raw : ℕ→Bool} {cur : Word W} {m : Memory W}
    (live : A.Live (pre++s::post) edges raw cur (NavigationDirectory.finish A.K pre A.cursor) m)
    {n : ℕ} (Q : RecordFamily n) (same : Q.motifs=s.motifs) (fits : Q.Fits A.K W)
    (cap : ℕ) (room : W*(A.K*(pre.map NavigationDirectory.Stage.motifs).sum)+Q.motifs*A.K*W≤cap) :
    let first:=A.K*(pre.map NavigationDirectory.Stage.motifs).sum
    let x:=RawHistogram.stage (W:=W) Q.motifs A.K raw first
    (∀ i j,m ((NavigationDirectory.finish A.K pre A.cursor).dense+A.K*i.val+j.val)=x i j) ∧
    ((List.ofFn (fun i : Fin cap=>raw i.val)).drop (W*first)).take (Q.record fits).width=
      List.ofFn (HistogramRegister.bitTable x) := by
  intro first x
  constructor
  · intro i j
    exact live.raw (i.cast same) j
  · exact RawHistogram.stage_prefix Q.motifs A.K raw first cap room

/-- Sequence the literal native pass and its remaining program on the actual tensor run.
The next branch is obtained by parsing these same raw bits; an invalid current histogram or
any later invalid stage has zero total return at every larger clock. -/
theorem run_step {d l D L : ℕ} {A : State d l} (R : Move F A D L) (later : ∀ i,Run F (R.next i))
    (E : (Run.step R later).Records) (raw : List Bool) (field : FieldCode F W)
    (current tail : Procedure W) (m₀ : Memory W) (siteData : Fin R.rules.count→Memory W→Prop)
    (terminal : Fin R.rules.count→Memory W→Prop) (t₀ t₁ : ℕ)
    (front : TickStageSpec.Admission field current.block current.publicData (fun m=>m=m₀)
      (fun _=>(E.1.read (raw.take E.1.width)).isSome)
      (fun _ m=>∃ i,E.1.read (raw.take E.1.width)=some i ∧ siteData i m) t₀)
    (back : ∀ i,E.1.read (raw.take E.1.width)=some i → ∀ m,siteData i m →
      TickStageSpec.Admission field tail.block tail.publicData (fun u=>u=m)
        (fun _=>((later i).plan.read ((later i).codes (E.2 i)) (raw.drop E.1.width)).isSome)
        (fun _ out=>terminal i out) t₁) :
    TickStageSpec.Admission field (current.seq tail).block (current.seq tail).publicData
      (fun m=>m=m₀) (fun _=>((Run.step R later).plan.read ((Run.step R later).codes E) raw).isSome)
      (fun _ out=>∃ i,E.1.read (raw.take E.1.width)=some i ∧ terminal i out) (t₀+t₁) := by
  let ok := ((Run.step R later).plan.read ((Run.step R later).codes E) raw).isSome = true
  let head := E.1.read (raw.take E.1.width)
  let middle (m : Memory W) := ∃ i,head=some i ∧ siteData i m
  let last (m : Memory W) := ∃ i,head=some i ∧ terminal i m
  have choose (i : Fin R.rules.count) (ht : head=some i) :
      ok ↔ ((later i).plan.read ((later i).codes (E.2 i)) (raw.drop E.1.width)).isSome := by
    change ((Run.step R later).plan.read ((Run.step R later).codes E) raw).isSome ↔ _
    rw [Run.read_step_some]
    change (∃ j,head=some j ∧ _) ↔ _
    simp only [ht,Option.some.injEq,exists_eq_left']
  have cont : TickStageSpec.Admission field tail.block tail.publicData middle (fun _=>ok)
      (fun _ out=>last out) t₁ := by
    intro n r k M pc reg pub exit rom data cfg m entry hm
    obtain ⟨i,ht,stored⟩:=hm
    obtain ⟨yes,no⟩:=(back i ht m stored) M pc reg pub exit rom data cfg m entry rfl
    constructor
    · intro pass
      obtain ⟨t,htime,c,out,done,good,run⟩:=yes ((choose i ht).mp pass)
      exact ⟨t,htime,c,out,done,⟨i,ht,good⟩,run⟩
    · intro bad
      exact no (fun good=>bad ((choose i ht).mpr good))
  have fork : TickStageSpec.Admission field (current.seq tail).block (current.seq tail).publicData
      (fun m=>m=m₀) (fun _=>ok) (fun _ out=>∃ tmp,middle tmp ∧ last out) (t₀+t₁) := by
    apply TickStageSpec.admission_seq field current tail front cont
    · intro m hm yes
      obtain ⟨i,ht,_⟩:=(Run.read_step_some R later E raw).mp yes
      simp [ht]
    · intro m out hm hg post
      exact ⟨post,Iff.rfl⟩
  intro n r k M pc reg pub exit rom data cfg mem entry initial
  obtain ⟨pass,fail⟩:=fork M pc reg pub exit rom data cfg mem entry initial
  constructor
  · intro good
    obtain ⟨ticks,ht,c,out,halted,⟨_,_,result⟩,steps⟩:=pass good
    exact ⟨ticks,ht,c,out,halted,result,steps⟩
  · exact fail

/-- The terminal graph supplies precisely the widths of the plan's finite boundary wire.
The order is base vertex, outgoing port, then lane in both the stored and abstract tensors. -/
theorem stored_width_word {d l : ℕ} (A : State d l) (C : SlotImage.Columns) (m : Memory W)
    (stored : SlotImage.Stored A.graph A.order (CompressorPacking.Native.tagOrdinal l) C
      (fun i=>(m i).val) A.width) (i : Fin A.edgeCount) :
    (m (C.widths+i.val)).val=A.wireWidth i := by
  obtain ⟨⟨⟨v,p⟩,lane⟩,rfl⟩:=A.wireOrder.surjective i
  simp only [State.wireWidth,Equiv.symm_apply_apply,State.wireOrder_val]
  exact stored.widthWord ((v,p),lane)

theorem stored_width_sum {d l : ℕ} (A : State d l) (C : SlotImage.Columns) (m : Memory W)
    (stored : SlotImage.Stored A.graph A.order (CompressorPacking.Native.tagOrdinal l) C
      (fun i=>(m i).val) A.width) :
    (∑ i ∈ Finset.range A.edgeCount,(m (C.widths+i)).val)=A.widthSum := by
  rw [←Fin.sum_univ_eq_sum_range,←State.wireWidth_sum A]
  exact Finset.sum_congr rfl (fun i _=>stored_width_word A C m stored i)

/-- The physical terminal prefix cell plus the edge's little-endian bit number is the
actual flattened coordinate read by the selected-root interpreter. -/
theorem terminal_bit_address {d l : ℕ} (A : State d l) (C : SlotImage.Columns)
    (x : TerminalWireArchive.Layout) (m : Memory W) (room : TerminalWireArchive.Bounds x W)
    (base : x.widthBase=C.widths) (edges : x.edges=A.edgeCount) (fit : A.widthSum≤x.capacity)
    (stored : SlotImage.Stored A.graph A.order (CompressorPacking.Native.tagOrdinal l) C
      (fun i=>(m i).val) A.width) (i : Fin A.edgeCount) (j : Fin (A.wireWidth i)) :
    ((TerminalWireArchive.image x m) (x.prefixBase+i.val)).val+j.val=(A.bitAddress i j).val := by
  have top : (∑ n ∈ Finset.range i.val,(m (C.widths+n)).val)≤A.widthSum := by
    rw [←stored_width_sum A C m stored]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono i.isLt.le) (by intros; omega)
  rw [TerminalWireArchive.image_entry x m room i.val (by rw [edges];exact i.isLt.le),
    TerminalWireArchive.total,base,min_eq_right (by omega),A.bitAddress_val,←Fin.sum_univ_eq_sum_range]
  congr 1
  exact Finset.sum_congr rfl (fun z _=>stored_width_word A C m stored (Fin.castLE i.isLt.le z))

/-- The actual terminating native guard agrees with the chronological parser for the
raw input word. The two possible suffix sources lie on the mounted old/new AUX tape. -/
theorem terminal_decode {S : HistoryContraction.Shape} (P : HistoryContraction.Plan F S)
    (E : P.Codes) (bits : P.History → ℕ) (capacity : ℕ) (s tail : List Bool) (h : P.History)
    (parsed : P.read E s=some (h,tail)) (extent : s.length=capacity)
    (x : TerminalWireArchive.Layout) (m : Memory W) (room : TerminalWireArchive.Bounds x W)
    (size : x.capacity=tail.length)
    (width : (∑ j ∈ Finset.range x.edges,(m (x.widthBase+j)).val)=bits h)
    (phase : x.phase<x.prefixBase) (old : x.oldSource+x.capacity≤x.prefixBase)
    (fresh : x.newSource+x.capacity≤x.prefixBase)
    (source : ∀ i : Fin tail.length,
      m ((if (m x.phase).val=1 then x.newSource else x.oldSource)+i.val)=0 ↔ tail.get i=false) :
    TerminalWireArchive.canonical x (TerminalWireArchive.image x m) ↔
      (P.decodeShared E bits capacity s).isSome := by
  rw [P.decodeShared_suffix E bits capacity s h tail parsed extent]
  have frame (a : ℕ) (before : a<x.prefixBase) : TerminalWireArchive.image x m a=m a := by
    simp [TerminalWireArchive.image,fillSegment,show ¬x.prefixBase≤a by omega]
  unfold TerminalWireArchive.canonical
  rw [TerminalWireArchive.image_entry x m room x.edges le_rfl]
  simp only [TerminalWireArchive.total,width,frame _ phase]
  have raw (i : Fin tail.length) :
      TerminalWireArchive.image x m ((if (m x.phase).val=1 then x.newSource else x.oldSource)+i.val)=0 ↔
        tail.get i=false := by
    rw [frame]
    · exact source i
    · have := i.isLt; split_ifs <;> omega
  constructor
  · rintro ⟨fits,pad⟩
    have below : bits h≤tail.length := by omega
    refine ⟨below,fun i hi=> (raw i).mp (pad i.val (by omega) (by have := i.isLt; omega))⟩
  · rintro ⟨fits,pad⟩
    refine ⟨by omega,?_⟩
    intro i hi upper
    let j : Fin tail.length := ⟨i,by omega⟩
    exact (raw j).mpr (pad j (by change bits h ≤ i; omega))

/-- Close the navigation loop using the actual final slot graph and the terminal header it
returned. All fuel values above the displayed bound reject a malformed suffix. -/
theorem Archive.terminal_admission (a : Archive) (steps : List NavigationDirectory.Stage) (edges : ℕ)
    {S : HistoryContraction.Shape} (P : HistoryContraction.Plan F S) (E : P.Codes)
    (bits : P.History→ℕ) (s tail : List Bool) (h : P.History)
    (parsed : P.read E s=some (h,tail)) (extent : s.length=a.pairCapacity)
    (field : FieldCode F W) (m : Memory W) (raw : ℕ→Bool)
    {d l : ℕ} (endState : State d l) (cols : SlotImage.Columns) :
    let cur:=(a.control : Word W)
    let c:=NavigationDirectory.finish a.K steps a.cursor
    let x:=a.terminal steps edges W
    a.Live steps edges raw cur c m → a.cursor.header=a.seed+64 →
    a.seed+(a.directory steps edges W).length<2^W → TerminalWireArchive.Bounds x W →
    c.header<x.prefixBase → x.prefixBase+x.edges<a.control → x.widthBase+x.edges≤x.prefixBase →
    x.phase<x.prefixBase → x.oldSource+x.capacity≤x.prefixBase → x.newSource+x.capacity≤x.prefixBase →
    (∀ i : Fin tail.length,m ((if (m x.phase).val=1 then x.newSource else x.oldSource)+i.val)=0 ↔ tail.get i=false) →
    x.capacity=tail.length → x.widthBase=cols.widths → x.edges=endState.edgeCount → endState.widthSum=bits h →
    SlotImage.Stored endState.graph endState.order (CompressorPacking.Native.tagOrdinal l) cols
      (fun i=>(m i).val) endState.width →
    let body:=TerminalWireArchive.program (W:=W) x
    TickStageSpec.Admission field body.block body.publicData (fun i=>i=m)
      (fun _=>(P.decodeShared E bits a.pairCapacity s).isSome)
      (fun _ out=>out=TerminalWireArchive.image x m)
      ((11+(x.edges+1)*(2*(TerminalWireArchive.prefixWord x).work+4))+
        (6+(x.capacity+1)*(2*(TerminalWireArchive.checkWord x).work+4))) := by
  intro cur c x live origin fit room headLow ctrlLow low ph old fresh source size start num width stored body
  have head:=live.terminal_header origin fit
  have controlFits : a.control<2^W := room.current
  have ctl : cur.val=a.control := Fin.val_cast_of_lt controlFits
  have h0 : (m a.control).val=c.header := by simpa only [ctl] using head.pointer
  have word0 : (m c.header).val=x.capacity+1 := by simpa [TerminalWireArchive.header] using head.values 0 (by decide)
  have after : (TerminalWireArchive.image x m x.current).val=c.header := by
    change (TerminalWireArchive.image x m a.control).val=_
    rw [TerminalWireArchive.image,fillSegment]
    split_ifs with seen
    · omega
    · exact h0
  have sentinel : (TerminalWireArchive.image x m ((TerminalWireArchive.image x m x.current).val)).val=x.capacity+1 := by
    rw [after,TerminalWireArchive.image,fillSegment]
    split_ifs with seen
    · omega
    · exact word0
  have amount : (∑ j ∈ Finset.range x.edges,(m (x.widthBase+j)).val)=bits h := by
    rw [start,num,stored_width_sum endState cols m stored,width]
  have agree:=terminal_decode P E bits a.pairCapacity s tail h parsed extent x m room size amount ph old fresh source
  intro p r K machine pc regs slots exit installed values c₀ initial begin pre
  obtain ⟨pass,fail⟩:=TerminalWireArchive.admission field x room m (head.get 1 (by decide)) (head.get 2 (by decide))
    (fun j hj=>Or.inl (by omega)) sentinel machine pc regs slots exit installed values c₀ initial begin pre
  constructor
  · intro accepted
    obtain ⟨ticks,time,last,out,halted,⟨tmp,same,returned⟩,ran⟩:=pass (agree.mpr accepted)
    exact ⟨ticks,time,last,out,halted,returned.trans same,ran⟩
  · intro rejected
    exact fail (fun canonical=>rejected (agree.mp canonical))

end
end ThreeFlat.Diagonal.NavigationPass

end OAI
