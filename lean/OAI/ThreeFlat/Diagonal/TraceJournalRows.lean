import OAI.ThreeFlat.Diagonal.TraceArchiveSource
import OAI.ThreeFlat.Diagonal.TraceIterationJournal
import OAI.ThreeFlat.Diagonal.CursorSeedSites
import OAI.ThreeFlat.Diagonal.PhysicalRunRootNumber

namespace OAI
/-! # Reading stored node rows and framing the executed stage journal -/

namespace ThreeFlat.Diagonal.NavigationPass.TraceRecovery
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open PhysicalStage PhysicalStage.Run NavigationDirectory HistoryContraction CompressorPacking Native
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F]

def Recovered {d l : ℕ} {A : State d l} (r : Run F A) (E : r.Records) (C : r.Charges)
    (O : A.ArchiveSites) (data : LayerData O.layer) (raw : List Bool)
    (post : List NodeRow → Layer → Prop) : Prop :=
  ∃ (h : r.plan.History) (suffix : List Bool) (p : r.ArchivePath h C O),
    r.plan.read (r.codes E) raw=some (h,suffix) ∧ r.FinalNumbered h C O p ∧
    post (r.archiveList h C O p data) (r.finalArchive h C O p).1

def castSites {d l L : ℕ} (e : l=L) (A : State d l) (O : A.ArchiveSites) :
    (e ▸ A : State d L).ArchiveSites :=
  ⟨O.layer,by cases e;exact O.ord⟩

theorem numbered_castSites {d l L : ℕ} (e : l=L) (A : State d l) (O : A.ArchiveSites)
    (numbered : O.Numbered) : (castSites e A O).Numbered := by cases e;exact numbered

theorem recovered_recast {d l L k w tariff : ℕ} (e : l=L) (A : State d l) (r : Run F (e ▸ A : State d L))
    {sizes : List ℕ} (table : Program.RecordTable r k w sizes) (C : Program.Certified r tariff)
    (O : A.ArchiveSites) (data : LayerData O.layer) (raw : List Bool) (post : List NodeRow→Layer→Prop) :
    Recovered r table.records C.1 (castSites e A O) data raw post →
    Recovered (Program.recast e A r) (Program.changeTable e A r table).records
      (Program.certRecast e A r C).1 O data raw post := by cases e;exact id

private theorem initial_fits {K W : ℕ} (ops : List Stage) (c : Cursor) (s : Layer)
    (fit : ∀ q ∈ nodeLayers K ops c s,q.actual.first+q.actual.count≤2^W) :
    s.first+s.count≤2^W := by
  cases ops <;> exact fit _ (List.mem_cons_self ..)

def interleave {d l D L : ℕ} {A : State d l} (R : Move F A D L) (t : Fin R.rules.count)
    (old : A.ArchiveSites) {charge : (R.next t).Site→ℕ} (step : R.ArchiveStep t old charge)
    (data : LayerData old.layer) : NodeRow :=
  ⟨old.layer,⟨false,step.sites.layer.first,step.ownerPtr⟩,data,
    fun j=>(step.sites.ord (R.parent t (old.ord.symm j))).val⟩

private theorem prepend_recovered {d l D L : ℕ} {A : State d l} (R : Move F A D L)
    (next : ∀ t,Run F (R.next t)) (E : (Run.step R next).Records) (C : (Run.step R next).Charges)
    (O : A.ArchiveSites) (data : LayerData O.layer) (raw : List Bool) (post : List NodeRow→Layer→Prop)
    (t : Fin R.rules.count) (hit : E.1.read (raw.take E.1.width)=some t) (step : R.ArchiveStep t O (C.1 t)) :
    Recovered (next t) (E.2 t) (C.2 t) step.sites step.data (raw.drop E.1.width)
      (fun xs last=>post (interleave R t O step data :: xs) last) →
    Recovered (.step R next) E C O data raw post := by
  rintro ⟨h,suffix,p,tailHit,num,valid⟩
  refine ⟨Run.joinHistory R next t h,suffix,Run.joinArchivePath R next C O t h step p,
    Run.read_joinHistory R next E raw t hit h suffix tailHit,Run.joined_finalNumbered R next C O t h step p num,?_⟩
  rw [Run.archiveList_joinArchivePath,Run.finalArchive_layer_joinArchivePath]
  exact valid

theorem extend_stagePost {K : ℕ} {op : Stage} {ops : List Stage} {c : Cursor} {s s' : Layer}
    {«protected» : ℕ→Prop} {mem : ℕ→ℕ} {H M : ℕ} {initial : Layer→Prop} {q : NodeRow}
    (body : q.layer=s) (parent : q.parent=⟨false,(allocate K c op).next.node,(allocate K c op).words 44⟩)
    (suc : s'=nodeLayer K c op) (head : ArchivedSource q «protected» mem H M initial)
    {xs : List NodeRow} {last : Layer}
    (rest : stagePost K ops (allocate K c op).next s' «protected» mem H M initial xs last) :
    stagePost K (op::ops) c s «protected» mem H M initial (q::xs) last := by
  obtain ⟨rec,endLayer,res⟩:=rest
  subst s'
  refine ⟨?_,endLayer,?_⟩
  · change ⟨q.layer,q.parent⟩::records xs=_
    rw [rec,body,parent]
    rfl
  · intro r mem
    exact (List.mem_cons.mp mem).elim (fun e=>e.symm ▸ head) (res r)

theorem rows_of_one_stage {d l D L W limit s : ℕ} {A : State d l} (R : Move F A D L)
    (t : Fin R.rules.count) (old : A.ArchiveSites) {charge : (R.next t).Site→ℕ}
    (row : R.ArchiveStep t old charge) (data : LayerData old.layer)
    {a : Archive} (op : Stage) (c : Cursor) (P : Program F s) (rem : ℕ) (X : State (2^s) (P.charge+rem))
    {cur ctr : Word W} (raw : List Bool) {out final : Memory W}
    (journal : a.TraceJournal limit cur ctr P rem X (allocate a.K c op).next raw out final)
    («protected» : ℕ→Prop) {H M : ℕ} {initial : Layer→Prop} (base : initial old.layer ∨ RowContents data «protected» (fun x=>(final x).val) H M)
    (control : cur.val<ctr.val)
    (headers : (finish a.K (op::P.directory rem (Fintype.card X.Base)) c).header≤c.heap)
    (room : (allocate a.K c op).next.heap≤cur.val)
    (range : ∀ x,c.heap≤x→x<(allocate a.K c op).next.heap→«protected» x)
    (dataRead : row.data.Reads (fun x=>(out x).val))
    (fp : row.data.Footprint (fun x=>c.heap≤x ∧ x<(allocate a.K c op).next.heap) (fun x=>(out x).val))
    (owners : ParentReads (interleave R t old row data).parent (interleave R t old row data).owners
      (fun x=>(out x).val))
    (ownerRoom : ∀ j : Fin old.layer.count,c.heap≤row.ownerPtr+j.val ∧ row.ownerPtr+j.val<(allocate a.K c op).next.heap)
    (bounds : ∀ j,(row.data.halfWidth j).length≤H ∧ (row.data.motifCopies j).length≤M) :
    RowContents row.data «protected» (fun x=>(final x).val) H M ∧
    ArchivedSource (interleave R t old row data) «protected» (fun x=>(final x).val) H M initial := by
  have stay (i : ℕ) (hi : c.heap≤ i ∧ i<(allocate a.K c op).next.heap) : final i=out i :=
    Archive.TraceJournal.frame P rem X _ raw journal (ne_of_lt (hi.2.trans_le room))
      (ne_of_lt ((hi.2.trans_le room).trans control)) ⟨Or.inr (headers.trans hi.1),Or.inl hi.2⟩
  have equal (i : ℕ) (hi : c.heap≤ i ∧ i<(allocate a.K c op).next.heap) : (final i).val=(out i).val := congrArg Fin.val (stay i hi)
  refine ⟨⟨dataRead.of_footprint fp equal,(fp.transfer fp equal).mono (fun i hi=>range i hi.1 hi.2),
    fun j=>(bounds j).1,fun _ j=>(bounds j).2⟩,⟨base,?_,?_⟩⟩
  · intro nh j
    exact (equal _ (ownerRoom j)).trans (owners nh j)
  · intro _ j
    exact range _ (ownerRoom j).1 (ownerRoom j).2

structure JournalSpace (K W H M : ℕ) (ops : List Stage) (c : Cursor) (layer : Layer) (safe : ℕ→Prop) : Prop where
  nodes : ∀ q∈nodeLayers K ops c layer,q.actual.first+q.actual.count≤2^W
  header : (finish K ops c).header≤c.heap
  arena : ∀ i,c.heap≤ i→i<(finish K ops c).heap→safe i
  caps : ∀ op∈ops,stageHalves op≤H ∧ stageMotifs op≤M

/-- Every unmodified header column stays resident even after the decoder has
passed its row. A shrink may update only column 27 of a stage header. -/
theorem header_frame {a : Archive} {W limit s : ℕ} {cur ctr : Word W} (P : Program F s)
    (rem : ℕ) (X : State (2^s) (P.charge+rem)) (c : Cursor) (raw : List Bool)
    {input final : Memory W} (journal : a.TraceJournal limit cur ctr P rem X c raw input final)
    {addr : ℕ} (hc : addr≠cur.val) (ht : addr≠ctr.val) (heap : addr<c.heap)
    (untouched : ∀ i : ℕ, addr≠c.header+64*i+27) : final addr=input addr := by
  induction P generalizing rem c raw input final with
  | done s => exact journal addr ht
  | shrink s t G small tail ih =>
    obtain ⟨m,out,fit,j,boot,hit,shape,room,old,native,rest⟩:=journal
    have stay := native.archive addr hc (by simpa using untouched 0) (Or.inl heap)
    refine (ih _ _ _ _ rest ?_ ?_).trans (stay.trans (boot addr ht))
    · rw [heap_step]; omega
    · intro i
      change addr≠c.header+64+64*i+27
      simpa only [Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using untouched (i+1)
  | refresh s t h pad g γ tariff G hm hh sym rows zero conn degree tail ih =>
    obtain ⟨m,out,fit,j,boot,hit,shape,room,old,native,published,frame,rest⟩:=journal
    refine (ih _ _ _ _ rest ?_ ?_).trans ((frame addr hc (Or.inl heap)).trans (boot addr ht))
    · rw [heap_step]; omega
    · intro i
      change addr≠c.header+64+64*i+27
      simpa only [Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using untouched (i+1)

/-- Every fixed directory column of an already-processed stage is read back
from the final memory using the authentic incoming mounted archive. -/
theorem field_mounted {a : Archive} {W limit s edges : ℕ} {cur ctr : Word W}
    (P : Program F s) (rem : ℕ) (X : State (2^s) (P.charge+rem))
    (bits : ℕ→Bool) (raw : List Bool) {input final : Memory W}
    (journal : a.TraceJournal limit cur ctr P rem X a.cursor raw input final)
    (pre : List Stage) (op : Stage) (post : List Stage)
    (_steps : P.directory rem (Fintype.card X.Base)=pre++op::post)
    (visit : a.Visit (pre++op::post) edges bits cur [] X input)
    (start : a.cursor.header=a.seed+64) (sep : (finish a.K (pre++op::post) a.cursor).header≤a.cursor.heap)
    (ct : a.cursor.heap≤cur.val) (ctl : cur.val<ctr.val)
    (q : Fin 64) (unchanged : q.val≠27) :
    (final (a.cursor.header+(64*pre.length+q.val))).val=
      (allocate a.K (finish a.K pre a.cursor) op).words q.val := by
  let j:=a.cursor.header+(64*pre.length+q.val)
  have bound : j<a.cursor.heap := by
    rw [header_finish,List.length_append,List.length_cons] at sep
    have := q.isLt
    dsimp [j]; omega
  have frame := header_frame P rem X a.cursor raw journal (addr:=j) (by omega) (by omega) bound
    (fun i=>by have := q.isLt; dsimp [j];omega)
  have access := tape_header a.K pre op post a.cursor q
  have entry : (a.directory (pre++op::post) edges W)[64+(64*pre.length+q.val)]? =
      some ((allocate a.K (finish a.K pre a.cursor) op).words q.val) := by
    rw [Archive.directory,List.getElem?_append_right (by simp),List.length_ofFn,Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left (by have := q.isLt; simp [List.length_append,List.length_cons];omega)]
    exact access
  change (final j).val=_
  rw [frame]
  have issued := visit.live.headers _ _ (by change a.cursor.header≤_;rw [start];omega) entry
  simpa only [j,start,Nat.add_assoc] using issued

/-- The native terminal memory retains all field-44 pointer entries from the
actual initial `Archive.Visit`, although earlier choice fields were overwritten. -/
theorem field44_mounted {a : Archive} {W limit s edges : ℕ} {cur ctr : Word W}
    (P : Program F s) (rem : ℕ) (X : State (2^s) (P.charge+rem))
    (bits : ℕ→Bool) (raw : List Bool) {input final : Memory W}
    (journal : a.TraceJournal limit cur ctr P rem X a.cursor raw input final)
    (pre : List Stage) (op : Stage) (post : List Stage)
    (steps : P.directory rem (Fintype.card X.Base)=pre++op::post)
    (visit : a.Visit (pre++op::post) edges bits cur [] X input)
    (start : a.cursor.header=a.seed+64) (sep : (finish a.K (pre++op::post) a.cursor).header≤a.cursor.heap)
    (ct : a.cursor.heap≤cur.val) (ctl : cur.val<ctr.val) :
    (final (a.cursor.header+(64*pre.length+44))).val=
      (allocate a.K (finish a.K pre a.cursor) op).words 44 :=
  field_mounted P rem X bits raw journal pre op post steps visit start sep ct ctl ⟨44,by decide⟩ (by decide)

/-- The initial RAM writer's genuine row reads and footprint persist in the
final resident archive. Its cursor widths are constant and it has no motifs. -/
theorem seed_contents {W limit s lo hi dp H M : ℕ} {a : Archive} {cur ctr : Word W}
    (P : Program F s) (rem : ℕ) (X : State (2^s) (P.charge+rem)) (raw : List Bool)
    {input final : Memory W} (journal : a.TraceJournal limit cur ctr P rem X a.cursor raw input final)
    (reads : a.seedData.Reads (fun z=>(input z).val))
    (foot : a.seedData.Footprint (fun z => lo≤z ∧ z<hi) (fun z=>(input z).val))
    (nodeBound : 2*a.initialDegree≤H) (cells : hi≤dp) (counters : hi≤cur.val) (ctl : cur.val<ctr.val)
    (safe : ∀ z, lo≤z → z<hi → traceOutsideWrites a.K a.cursor (P.directory rem (Fintype.card X.Base)) z) :
    RowContents a.seedData (·<dp) (fun z=>(final z).val) H M := by
  have same (z : ℕ) (span : lo≤z ∧ z<hi) : (final z).val=(input z).val :=
    congrArg Fin.val (Archive.TraceJournal.frame P rem X a.cursor raw journal (by omega) (by omega)
      (safe z span.1 span.2))
  refine ⟨reads.of_footprint foot same,(foot.transfer foot same).mono (fun z hz=>hz.2.trans_le cells),?_,?_⟩
  · intro j
    simpa only [Archive.seedData,List.length_replicate] using nodeBound
  · intro nz
    exact (nz rfl).elim

/-- A single bound for the directory's public node counts and the high-water
mark of its writes suffices for the numerical backward-lane scanner. -/
theorem JournalSpace.of_rooms {K W dp : ℕ} {ops : List Stage} {c : Cursor} {layer : Layer}
    (first : layer.first=c.node)
    (nodes : c.node+layer.count+(ops.map Stage.nodes).sum+(ops.map successors).sum≤2^W)
    (headers : (finish K ops c).header ≤ c.heap) (heap : (finish K ops c).heap≤dp) :
    JournalSpace K W (ops.map stageHalves).sum (ops.map stageMotifs).sum ops c layer (·<dp) where
  nodes q hit := (node_room K ops c layer first q hit).trans nodes
  header := headers
  arena _ _ high := high.trans_le heap
  caps _op hit := ⟨List.le_sum_of_mem (List.mem_map_of_mem hit),List.le_sum_of_mem (List.mem_map_of_mem hit)⟩

theorem header_room {W limit cap edges : ℕ} {a : Archive} {cur : Word W}
    {steps : List Stage} (limits : a.TraceLimits limit cur steps edges cap) :
    (finish a.K steps a.cursor).header≤a.cursor.heap := by
  have entries := limits.tables
  have tails := limits.raw
  rw [Archive.directory_length] at entries
  rw [header_finish,limits.origin]
  omega

/-- The word and heap rooms required by a genuine executed selector journal
are exactly the public node-span bound and the placement of the DP scratch. -/
theorem JournalSpace.of_traceLimits {W limit cap edges dp : ℕ} {a : Archive} {cur : Word W}
    {steps : List Stage} {old : Layer} (limits : a.TraceLimits limit cur steps edges cap)
    (first : old.first=a.cursor.node)
    (nodes : a.cursor.node+old.count+(steps.map Stage.nodes).sum+(steps.map successors).sum≤2^W)
    (placement : (finish a.K steps a.cursor).heap≤dp) :
    JournalSpace a.K W (steps.map stageHalves).sum (steps.map stageMotifs).sum
      steps a.cursor old (·<dp) :=
  JournalSpace.of_rooms first nodes (header_room limits) placement

theorem JournalSpace.tail {K W H M : ℕ} {op : Stage} {ops : List Stage} {c : Cursor} {layer : Layer}
    {safe : ℕ→Prop} (space : JournalSpace K W H M (op::ops) c layer safe) :
    JournalSpace K W H M ops (allocate K c op).next (nodeLayer K c op) safe := by
  have begin : c.heap≤(allocate K c op).next.heap := by rw [heap_step];omega
  exact ⟨fun q h=>space.nodes q (List.mem_cons_of_mem _ h),space.header.trans begin,
    fun i hi=>space.arena i (begin.trans hi),fun o ho=>space.caps o (List.mem_cons_of_mem _ ho)⟩

theorem JournalSpace.local {K W H M : ℕ} {op : Stage} {ops : List Stage} {c : Cursor} {layer : Layer}
    {safe : ℕ→Prop} (space : JournalSpace K W H M (op::ops) c layer safe) :
    (allocate K c op).next.node≤2^W ∧ ∀ i,c.heap≤ i→i<(allocate K c op).next.heap→safe i := by
  have slots := initial_fits ops (allocate K c op).next (nodeLayer K c op) space.tail.nodes
  have later : (allocate K c op).next.heap≤(finish K ops (allocate K c op).next).heap := by rw [heap_finish];omega
  refine ⟨(Nat.le_add_right _ _).trans slots,fun i lo hi=>space.arena i lo (hi.trans_le later)⟩


end
end ThreeFlat.Diagonal.NavigationPass.TraceRecovery

end OAI
