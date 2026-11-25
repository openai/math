import OAI.ThreeFlat.RAM.HistoryRefreshIncidence
import OAI.ThreeFlat.RAM.HistoryRefreshKernel

namespace OAI
/-! # Execution of the single-party refresh root in the selected history machine -/
set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Diagonal.TickWorkspace HistoryScratch Computability.VPVNP.BurstRAM PrivateRAM HistoryGatherBody HistoryGatherExecution
open scoped Classical
noncomputable section

variable {u node x M P W : ℕ}
local notation "V" => volume u

/-- The selected gather's preliminary header and all port rows stay in S17;
only its actual output slots in the present S12 node sector are written. -/
theorem gather_outside_node (A : HistoryGatherBody.Layout) (plan : Plan W) (mem : Memory W)
    (safe : OutsideNode u node x) (stage : A.temp=base u 17) (vol : A.party.V=V)
    (header : 3+5*A.demandCap+4*A.supplyCap≤V) (width : ∀ q i,i<cap A q → plan.width q i≤V)
    (loc : Local) (valid : loc.Valid M P) (capacity : (M+2)*(P+2)*8*32≤V)
    (page : plan.gatherBase=atWord (base u 12) V M P node loc 0) (size : plan.gatherCount≤V) :
    output A plan mem x=mem x := by
  have begin_ : base u 14≤A.temp := by
    have h:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 14<17)
    rw [stage];omega
  have end_ : portsEnd A≤base u 18 := by
    have rows : 1+A.demandCap+A.supplyCap≤V := by omega
    have area := Nat.mul_le_mul_right V rows
    have growth : V^2≤V^4 := Nat.pow_le_pow_right (Nat.two_pow_pos _) (by decide)
    have sep:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 17<18)
    change base u 17+V^4≤base u 18 at sep
    unfold portsEnd
    rw [stage,vol]
    rw [pow_two] at growth
    omega
  have cap₁ : A.temp+V≤portsEnd A := by
    unfold portsEnd
    rw [vol]
    have count : 1 ≤ 1 + A.demandCap + A.supplyCap := by omega
    have capSize := Nat.mul_le_mul_right V count
    exact Nat.add_le_add_left (by simpa only [one_mul] using capSize) A.temp
  have after : base u 18≤base u 19 := by
    have t:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 18<19)
    omega
  apply output_away
  · rw [header_size]
    exact safe.scratch_range begin_ (by omega) (.inl (by omega))
  · intro q i hi
    have bounds:=HistoryGatherExecution.aperture A q i hi
    have w:=width q i hi
    rw [vol] at bounds
    exact safe.scratch_range (by omega) (by omega) (.inl (by omega))
  · rw [page]
    exact safe.private_range capacity loc valid _ size

end
end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.RAM.HistoryRefreshEmitter
open Computability.VPVNP.BurstRAM PrivateRAM HistoryStageBody.Physical Diagonal.TickWorkspace HistoryScratch
open HistoryMotifJoin HistoryGatherBody
open scoped Classical Fin.CommRing
noncomputable section

variable {F : Type*} {u : ℕ} (arch : HistoryStageBody.Physical.Archive) (f : Family) (node : ℕ)
  (winner : Fin f.parties) {kernelPtr incidentPtr : ℕ}
local notation "V" => volume u
local notation "W₀" => 16*u^10
local notation "A" => layout u arch f
local notation "nodePtr" => base u 44 + 8*node

/-- Static archive words can lie below the private arenas or in any directory
above S19. The actual cursor and stop in S18 are protected at the same node. -/
theorem outside_of_region {x:ℕ} (age:16≤u) (fit:node<V^2)
    (zone:x<base u 12 ∨ base u 19≤x ∨ x=base u 18 ∨ x=base u 18+1) :
    OutsideNode u node x := by
  have vb:16≤V:=age.trans ((Nat.le_self_pow (by decide:10≠0) u).trans Nat.lt_two_pow_self.le)
  have sq:V≤V^2:=Nat.le_self_pow (by decide) V
  have arena:(node+1)*V^2≤V^4:=by
    calc
      _≤V^2*V^2:=Nat.mul_le_mul_right _ fit
      _=V^4:=by ring
  have cache:8*node+8≤V^4:=by
    calc
      _=8*(node+1):=by ring
      _≤V^2*V^2:=Nat.mul_le_mul (by omega) fit
      _=V^4:=by ring
  have s12:=Diagonal.TickWorkspace.apart (u:=u) (by decide:12<13)
  have s13:=Diagonal.TickWorkspace.apart (u:=u) (by decide:13<14)
  have s14:=Diagonal.TickWorkspace.apart (u:=u) (by decide:14<18)
  have s18:=Diagonal.TickWorkspace.apart (u:=u) (by decide:18<19)
  change base u 12+V^4≤base u 13 at s12
  change base u 13+V^4≤base u 14 at s13
  exact ⟨by omega,by omega,by omega⟩

/-- All words of the genuine mounted library persist across the selected party
or its preceding checked-batch pass. -/
theorem mounted_kept {K:Type} [Field K] [Fintype K] (B:Diagonal.PhysicalStage.Block K)
    {height start:ℕ} {before after:Memory W₀} (resident:Mounted B height W₀ start before)
    (age:16≤u) (fit:node<V^2)
    (zone : start + libraryWords B height ≤ base u 12 ∨ base u 19 ≤ start)
    (keep:∀ x,OutsideNode u node x→after x=before x) : Mounted B height W₀ start after := by
  refine ⟨fun q=>?_⟩
  have bound:=q.isLt
  exact (keep _ (outside_of_region node age fit (by omega))).trans (resident.words q)

/-- The five consistency observations of a refresh site are all protected, including
the two immutable controls of the cursor band. -/
structure IncidenceOutside (u node kernelPtr incidentPtr : ℕ) : Prop where
  cursor : OutsideNode u node (base u 18)
  nodeWord : OutsideNode u node (base u 44+8*node+5)
  count : OutsideNode u node (kernelPtr+3)
  incident : OutsideNode u node (kernelPtr+4)
  mask : OutsideNode u node (incidentPtr+5)

theorem physical_incidence_outside (age:16≤u) (fit:node<V^2)
    (kernel:kernelPtr+5≤base u 12 ∨ base u 19≤kernelPtr)
    (motif:incidentPtr+6≤base u 12 ∨ base u 19≤ incidentPtr) :
    IncidenceOutside u node kernelPtr incidentPtr := by
  have large:=Diagonal.TickWorkspace.apart (u:=u) (by decide:19<44)
  exact ⟨outside_of_region node age fit (by omega),outside_of_region node age fit (by omega),
    outside_of_region node age fit (by omega),outside_of_region node age fit (by omega),
    outside_of_region node age fit (by omega)⟩

theorem IncidenceRead.keep_outside {m m' : Memory (16 * u ^ 10)}
    (read : IncidenceRead u f node winner m kernelPtr incidentPtr)
    (loc : IncidenceOutside u node kernelPtr incidentPtr)
    (same : ∀x,OutsideNode u node x → m' x=m x) :
    IncidenceRead u f node winner m' kernelPtr incidentPtr := by
  have atWord (a : ℕ) (h : OutsideNode u node a) : HistoryPartyBatchExec.numeric m' a = HistoryPartyBatchExec.numeric m a :=
    congrArg Fin.val (same _ h)
  exact ⟨by rw [atWord _ loc.cursor];exact read.cursor,(atWord _ loc.nodeWord).trans read.kernel,
    by rw [atWord _ loc.count];exact read.count,(atWord _ loc.incident).trans read.incident,
    (atWord _ loc.mask).trans read.mask⟩

private theorem privateStage_away {w : ℕ} (B : HistoryGatherBody.Layout) (m : Memory w) (x : ℕ)
    (away : ¬(B.privateStarts ≤ x ∧ x < B.privateStarts + 9)) : privateStage B m x = m x := by
  unfold privateStage HistoryMotifJoin.headerImage fillSegment
  exact ite_eq_right away

/-- Private-mask offsets occupy nine words beyond the live S18 cursor and stop. -/
theorem private_stage_outside (mem : Memory W₀) (x : ℕ) (safe : OutsideNode u node x) (age : 16≤u) :
    privateStage (withMotif (layout u arch f) 0) mem x=mem x := by
  have v : 16≤V:=age.trans ((Nat.le_self_pow (by decide : 10≠0) u).trans Nat.lt_two_pow_self.le)
  have grow : 5*V≤V^4 := calc
    _≤V*V:=Nat.mul_le_mul_right _ (by omega)
    _=V^2:=(pow_two V).symm
    _≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have h:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 18<19)
  have b:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 14<18)
  change base u 18+V^4≤base u 19 at h
  have away : x<base u 18+4*V ∨ base u 18+4*V+9≤x :=
    safe.scratch_range (by omega) (by omega) (.inr (by omega))
  have clean : ¬(base u 18+4*V≤x ∧ x<base u 18+4*V+9) := by omega
  exact privateStage_away (withMotif (layout u arch f) 0) mem x clean

variable (id : ((Fin 3→Bool)→F)→ℕ) (stage livePair : Memory (16 * u ^ 10))
  (plan : HistoryGatherExecution.Plan (16 * u ^ 10))
local notation "J" => rawArm A winner.val
local notation "full" => HistoryGatherExecution.output J plan livePair
local notation "entry" => entryOf A node winner id stage livePair full

/-- Every vacant invocation is established at its real entry memory. The active gather
uses its S17 port extents and the actual S12 private map of the selected party. -/
theorem physical_roster_frame [CommRing F]
    (original : IncidenceRead u f node winner stage kernelPtr incidentPtr)
    (immutable : IncidenceRoom u node kernelPtr incidentPtr) (loc : IncidenceOutside u node kernelPtr incidentPtr)
    (age : 16≤u) (count : node<V^2) (motifs : 0<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V) (mask : 2^f.parties<2^W₀)
    (lookup : arch.lut+1<2^W₀) (lutStride : arch.lutStride<2^W₀) (pages : arch.pages<2^W₀)
    (pageStride : arch.pageStride<2^W₀) (counts : arch.counts+1<2^W₀)
    (lutAway : arch.lut+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.lut)
    (countsAway : arch.counts+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.counts)
    (headerCap : 3+5*f.demands+4*f.supplies≤V) (ports : HistoryGatherExecution.portsEnd J<2^W₀)
    (widths : ∀q i,i<HistoryGatherExecution.cap J q → plan.width q i≤V)
    (mapBase : plan.gatherBase=HistoryPartyPair.atPair (J).party node 2) (pinCount : plan.gatherCount≤V)
    (pairKeep : ∀x,OutsideNode u node x → livePair x=beforeWinner A node winner id stage x) :
    ∀n,n≤f.parties → IncidenceRead u f node winner (entry n) kernelPtr incidentPtr ∧
      ∀x,OutsideNode u node x → entry n x=stage x := by
  have init:=fun x (h:OutsideNode u node x)=>private_stage_outside arch f node stage x h age
  have inRead:=original.keep_outside f node winner loc init
  have fold:=roster_preserves A node winner id stage livePair full
    (fun m=>IncidenceRead u f node winner m kernelPtr incidentPtr) (OutsideNode u node) inRead
  have active (x : ℕ) (h : OutsideNode u node x) : full x=entry winner.val x := by
    have entryAt := congrFun (winner_entry A node winner id stage livePair full) x
    have valid : (⟨2,winner.val+2,2,2⟩ : Local).Valid f.motifs f.parties :=
      ⟨by change 2 < f.motifs + 2; omega,
       by change winner.val + 2 < f.parties + 2; exact Nat.add_lt_add_right winner.isLt 2,
       (by decide : (2 : ℕ) < 8), (by decide : (2 : ℕ) < 32)⟩
    have kept := gather_outside_node J plan livePair h rfl rfl headerCap widths
      (⟨2,winner.val+2,2,2⟩ : Local) valid capacity mapBase pinCount
    exact kept.trans ((pairKeep x h).trans entryAt.symm)
  have check:=fold (fun r=>⟨r.keep_outside f node winner loc active,active⟩) (by
    intro j other mem read
    have receipts:=physical_vacant_room_all u arch f node winner j mem kernelPtr incidentPtr id read immutable other
      age count motifs capacity mask lookup lutStride pages pageStride counts lutAway countsAway headerCap ports
    have keep:=fun x (hx:OutsideNode u node x)=>receipts.2 x (.inr hx)
    exact ⟨read.keep_outside f node winner loc keep,keep⟩)
  intro n hn
  obtain ⟨r,save⟩:=check n hn
  exact ⟨r,fun x hx=>(save x hx).trans (init x hx)⟩

end
end ThreeFlat.RAM.HistoryRefreshEmitter

namespace ThreeFlat.RAM.HistoryRefreshEmitter
open Computability.VPVNP.BurstRAM PrivateRAM HistoryStageBody.Physical Diagonal.TickWorkspace HistoryScratch
open HistoryStageBody Diagonal.HistoryContraction HistoryPartyBatch HistoryPartyBatchExec BitNetwork.Ordered
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type*} {u node x : ℕ}
local notation "V" => volume u
local notation "W₀" => 16*u^10

/-- Constant pages of either physical type of party, at any valid motif slot. -/
structure PartyWindow (u : ℕ) (A : HistoryPartyBatch.Layout) : Prop where
  age : 16≤u
  arena : A.arena=base u 12
  volume : A.V=Physical.volume u
  seed : A.seed=base u 14+Physical.volume u
  header : A.batch=base u 14+2*Physical.volume u
  commands : A.commands=base u 15
  arguments : A.arguments=base u 16
  maps : A.maps=base u 18+5*Physical.volume u
  motif : A.motif<A.motifs
  party : A.party<A.parties
  capacity : (A.motifs+2)*(A.parties+2)*8*32≤Physical.volume u

theorem PartyWindow.of_layout (arch : HistoryStageBody.Physical.Archive) (f : Family) (i j : ℕ)
    (age : 16≤u) (m : i<f.motifs) (p : j<f.parties) (cap : (f.motifs+2)*(f.parties+2)*8*32≤V) :
    PartyWindow u { (layout u arch f).party with motif:=i,party:=j } :=
  ⟨age,rfl,rfl,rfl,rfl,rfl,rfl,rfl,m,p,cap⟩

private theorem window_bounds {A : HistoryPartyBatch.Layout} (loc : PartyWindow u A) :
    1024≤V ∧ 30*V≤V^4 ∧ base u 14+V^4≤base u 15 ∧ base u 15+V^4≤base u 16 ∧
    base u 16+V^4≤base u 18 ∧ base u 18+V^4≤base u 19 ∧ base u 19<2^W₀ := by
  have z : 1024≤V:=Nat.pow_le_pow_right (by decide : 0<2)
    ((show 10≤u by have:=loc.age;omega).trans (Nat.le_self_pow (by decide) _))
  have grow : 30*V≤V^4 := calc
    _≤V*V:=Nat.mul_le_mul_right _ (by omega)
    _=V^2:=(pow_two V).symm
    _≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have fin:=Diagonal.TickWorkspace.word_space (i:=19) (u:=u) (by have:=loc.age;omega)
    (by change 19<V^4;omega)
  exact ⟨z,grow,Diagonal.TickWorkspace.apart (by decide : 14<15),Diagonal.TickWorkspace.apart (by decide : 15<16),
    Diagonal.TickWorkspace.apart (by decide : 16<18),Diagonal.TickWorkspace.apart (by decide : 18<19),by omega⟩

theorem PartyWindow.seed_room {A : HistoryPartyBatch.Layout} (loc : PartyWindow u A) : A.seed+37<2^W₀ := by
  obtain ⟨a,b,c,d,e,f,g⟩:=window_bounds loc
  rw [loc.seed];omega

private theorem private_target {A : HistoryPartyBatch.Layout} (loc : PartyWindow u A)
    (safe : OutsideNode u node x) (k bank len : ℕ) (family : k<8) (valid : bank<32) (sz : len≤V) :
    let ptr:=atWord A.arena A.V A.motifs A.parties node ⟨A.motif+2,A.party+2,k,bank⟩ 0
    x<ptr ∨ ptr+len≤x := by
  rw [loc.arena,loc.volume]
  apply safe.private_range loc.capacity
  · exact ⟨Nat.add_lt_add_right loc.motif 2,Nat.add_lt_add_right loc.party 2,family,valid⟩
  · exact sz


/-- Scratch protection and all the local pages of this single occupied party. -/
structure PartyAway (u : ℕ) (A : HistoryPartyBatch.Layout) (node x : ℕ) : Prop where
  scratch : x<base u 14 ∨ base u 19≤x ∨ (base u 18≤x ∧ x<base u 18+5*volume u)
  page : ∀ k bank : ℕ, k<8 → bank<32 → ∀ len, len≤volume u →
    let ptr:=atWord A.arena A.V A.motifs A.parties node ⟨A.motif+2,A.party+2,k,bank⟩ 0
    x<ptr ∨ ptr+len≤x

theorem PartyAway.of_outside {A : HistoryPartyBatch.Layout} (loc : PartyWindow u A)
    (safe : OutsideNode u node x) : PartyAway u A node x :=
  ⟨by have h:=safe.scratch;have v : 0<volume u:=Nat.two_pow_pos _;omega,fun k bank hk hb len hlen=>private_target loc safe k bank len hk hb hlen⟩

theorem PartyAway.scratch_range {A : HistoryPartyBatch.Layout} (safe : PartyAway u A node x)
    {lo hi : ℕ} (start : base u 14≤lo) (stop : hi≤base u 19)
    (cursor : hi≤base u 18 ∨ base u 18+5*volume u≤lo) : x<lo ∨ hi≤x := by
  have h:=safe.scratch;omega

private theorem dest_outside {A : HistoryPartyBatch.Layout} (_loc : PartyWindow u A)
    (safe : PartyAway u A node x) (ck : Bool) (bank len : ℕ) (valid : bank<32) (size : len≤V) :
    x<dest A ck node bank ∨ dest A ck node bank+len≤x :=
  safe.page ck.toNat bank (by cases ck <;> decide) valid len size

private theorem maps_outside {A : HistoryPartyBatch.Layout} (loc : PartyWindow u A)
    (safe : PartyAway u A node x) (len : ℕ) (sz : len≤V) :
    x<A.maps ∨ A.maps+len≤x := by
  obtain ⟨h,g,a,b,c,d,e⟩:=window_bounds loc
  rw [loc.maps]
  exact safe.scratch_range (by omega) (by omega) (.inr (by omega))

open private prefix_step prefix_mono prefix_end from OAI.ThreeFlat.RAM.HistoryPartyTapeRun

private theorem command_range (T : HistoryBatchTape.Header) (i : Fin (T.r+T.s)) (j : Fin 3) :
    (T.stream≤HistoryBatchTape.command T i.val j 1 ∧
      HistoryBatchTape.command T i.val j 6≤T.stream+8*HistoryPartyTapeRun.batchRows T) ∨
    (T.maps≤HistoryBatchTape.command T i.val j 1 ∧
      HistoryBatchTape.command T i.val j 6≤T.maps+HistoryPartyTapeRun.batchPins T) := by
  let before (a b : ℕ) := Tree.BatchRows.span T.r a b i.val
  let width (a b : ℕ) := if i.val<T.r then a else b
  have bound (a b : ℕ) : before a b+width a b≤T.r*a+T.s*b :=
    (prefix_step T.r a b i.val).le.trans
      ((prefix_mono T.r a b i.isLt).trans_eq (prefix_end T.r T.s a b))
  let rows := before T.left.rows T.right.rows
  let count := width T.left.rows T.right.rows
  have rowBound : rows+count≤HistoryPartyTapeRun.batchRows T := bound _ _
  have pinBound := bound T.left.arity T.right.arity
  fin_cases j
  · left
    change T.stream≤T.stream+4*rows ∧ T.stream+4*rows+4*count≤T.stream+8*HistoryPartyTapeRun.batchRows T
    omega
  · right
    exact ⟨Nat.le_add_right _ _,by
      change T.maps+before T.left.arity T.right.arity+width T.left.arity T.right.arity≤T.maps+_
      exact (Nat.add_assoc ..).le.trans (Nat.add_le_add_left pinBound _)⟩
  · left
    change T.stream≤T.stream+4*HistoryPartyTapeRun.batchRows T+4*rows ∧
      T.stream+4*HistoryPartyTapeRun.batchRows T+4*rows+4*count≤T.stream+8*HistoryPartyTapeRun.batchRows T
    omega

/-- All actual children of either batch write within its selected S12 stream or the S18
maps suffix. Thus the previously used S18 cursor and stop are preserved. -/
theorem batch_away [CommRing F] (X : HistoryPartyBatchExec.Build W₀) (loc : PartyWindow u X.layout)
    (safe : PartyAway u X.layout node x) {h p : ℕ} {arity : Fin (X.table.r+X.table.s)→ℕ}
    (N : ∀i,BitNetwork F (arity i)) (wire : ∀i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ)
    (before : numeric X.input X.layout.cursor-1=node)
    (stream : X.table.stream=dest X.layout X.checks node 0) (maps : X.table.maps=X.layout.maps)
    (count : X.count≤V) (rows : 8*HistoryPartyTapeRun.batchRows X.table≤V)
    (pins : HistoryPartyTapeRun.batchPins X.table≤V) :
    BatchAway X (HistoryPartyTapeRun.jobs (w:=W₀) X.table N wire id) x := by
  obtain ⟨v,g,s14,s15,s16,s18,word⟩:=window_bounds loc
  have pre (lo hi : ℕ) (low : base u 14≤lo) (high : hi≤base u 18) :
      x<lo ∨ hi≤x:=safe.scratch_range low (by omega) (.inl high)
  have seedOff : x<X.layout.seed ∨ X.layout.seed+37≤x :=by rw [loc.seed];apply pre <;> omega
  have cursor : X.ctrl.val=X.layout.seed+33:=Fin.val_cast_of_lt (by rw [loc.seed];omega)
  have fit := dest_outside loc safe X.checks 1 4 (by decide) (by omega)
  refine ⟨by rw [cursor];omega,seedOff,?_,?_,?_,?_,?_⟩
  · rw [loc.header];apply pre <;> omega
  · rw [loc.commands];apply pre <;> omega
  · rw [loc.arguments];apply pre <;> omega
  · intro J member
    obtain ⟨i,_,member⟩:=List.mem_flatMap.mp member
    obtain ⟨j,eq⟩:=List.mem_iff_get.mp member
    obtain ⟨first,last⟩:=HistoryPartyTapeRun.group_bounds (w:=W₀) X.table N wire id i j
    rw [eq] at first last
    have span:=command_range X.table i j
    rw [first,last] at span
    rw [stream,maps] at span
    rcases span with arm|arm
    · have off:=dest_outside loc safe X.checks 0 _ (by decide) rows
      omega
    · have off:=maps_outside loc safe _ pins
      omega
  · change x<dest X.layout X.checks (numeric X.input X.layout.cursor-1) 1 ∨
      dest X.layout X.checks (numeric X.input X.layout.cursor-1) 1+4≤x
    rw [before];exact fit

theorem batch_outside_node [CommRing F] (X : HistoryPartyBatchExec.Build W₀) (loc : PartyWindow u X.layout)
    (safe : OutsideNode u node x) {h p : ℕ} {arity : Fin (X.table.r+X.table.s)→ℕ}
    (N : ∀i,BitNetwork F (arity i)) (wire : ∀i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ)
    (before : numeric X.input X.layout.cursor-1=node)
    (stream : X.table.stream=dest X.layout X.checks node 0) (maps : X.table.maps=X.layout.maps)
    (count : X.count≤V) (rows : 8*HistoryPartyTapeRun.batchRows X.table≤V)
    (pins : HistoryPartyTapeRun.batchPins X.table≤V) :
    BatchAway X (HistoryPartyTapeRun.jobs (w:=W₀) X.table N wire id) x :=
  batch_away X loc (.of_outside loc safe) N wire id before stream maps count rows pins

end
end ThreeFlat.RAM.HistoryRefreshEmitter

namespace ThreeFlat.RAM.HistoryRefreshEmitter
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryPartyBatchExec
open HistoryBoundedJoin HistoryMotifJoin HistoryPartyBatch HistoryBoundedBody BitNetwork.Ordered
open HistoryStageBody.Physical Diagonal.TickWorkspace HistoryScratch HistoryPartyPairExec
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {u : ℕ}
local notation "V" => volume u
local notation "W₀" => 16*u^10

section PhysicalPair
variable {F : Type*} [CommRing F] {a b : ℕ} (J : HistoryPartyBatch.Layout) (node : ℕ)
  (L : Tree F a) (R : Tree F b) (id : ((Fin 3→Bool)→F)→ℕ)
local notation "N" => pairNetwork L R
local notation "Q" => HistoryPartyPairExec.copyHeader J node L R
local notation "ops" => HistoryPartyPairExec.steps (w:=W₀) J node L R id
local notation "root" => HistoryPartyPair.atPair J node

omit [CommRing F] in
private theorem job_choices (x : HistoryReadyTape.Job W₀) (valid:x∈ops) :
    ∃ i:Fin 2,(x.start=(Q i).pins ∧ x.finish=(Q i).pins+pairArity L R i) ∨
      (x.start=(Q i).dest ∧ x.finish=(Q i).dest+4*(N i).cells) := by
  obtain ⟨i,_,hin⟩:=List.mem_flatMap.mp valid
  refine ⟨i,?_⟩
  rcases (by simpa only [Tape.jobs,List.mem_cons,List.not_mem_nil,or_false] using hin :
      x=⟨(Q i).pins,pairArity L R i,_⟩ ∨ x=⟨(Q i).dest,4*(N i).cells,_⟩) with rfl | rfl
  · exact .inl ⟨rfl,rfl⟩
  · exact .inr ⟨rfl,rfl⟩

omit [CommRing F] in
private theorem job_endpoints (i : Fin 2) :
    (Q i).pins≥J.maps ∧ (Q i).pins+pairArity L R i≤J.maps+(a+b) ∧
    root 0≤(Q i).dest ∧ (Q i).dest+4*(N i).cells≤root 0+4*(L.rows+R.rows) ∧
    (Q i).source=dest J (decide (i=0)) node 0+4*(N i).cells ∧
    (N i).cells≤L.rows+R.rows := by
  have leftRows : (N (0:Fin 2)).cells=L.rows := by
    change L.compile.cells=L.rows
    exact compiled_rows L
  have rightRows : (N (1:Fin 2)).cells=R.rows := by
    change R.compile.cells=R.rows
    exact compiled_rows R
  have h0 : before (fun k=>(N k).cells) (0:Fin 2)=0 := by simp [before]
  have h1 : before (fun k=>(N k).cells) (1:Fin 2)=L.rows := by
    simpa [before,Fin.sum_univ_one] using leftRows
  have first (k : Fin 2) : root 0≤(Q k).dest := Nat.le_add_right _ _
  fin_cases i
  · refine ⟨le_rfl,?_,first 0,?_,rfl,leftRows.le.trans (Nat.le_add_right _ _)⟩
    · change J.maps+a≤J.maps+(a+b)
      omega
    · change root 0+4*before (fun k=>(N k).cells) 0+4*(N 0).cells≤_
      rw [h0,leftRows]
      omega
  · refine ⟨?_,?_,first 1,?_,rfl,rightRows.le.trans (Nat.le_add_left _ _)⟩
    · change J.maps≤J.maps+a
      exact Nat.le_add_right _ _
    · change (J.maps+a)+b≤J.maps+(a+b)
      omega
    · change root 0+4*before (fun k=>(N k).cells) 1+4*(N 1).cells≤_
      rw [h1,rightRows]
      omega


omit [CommRing F] in
private theorem pair_keeps_windows (mem : Memory W₀) (loc : PartyWindow u J) (x : ℕ)
    (safe : PartyAway u J node x) (pins : a+b≤V) (rows : 4*(L.rows+R.rows)≤V) :
    Retained J node L R id mem x ∧
      (x<HistoryPartyPair.hub J ∨ HistoryPartyPair.hub J+25≤x) := by
  obtain ⟨size,g,s14,s15,s16,s18,word⟩:=window_bounds loc
  have pre (lo hi : ℕ) (low : base u 14≤lo) (high : hi≤base u 18) :
      x<lo ∨ hi≤x:=safe.scratch_range low (by omega) (.inl high)
  have seedOff : x<J.seed ∨ J.seed+9≤x:=by rw [loc.seed];apply pre <;> omega
  have cursor : (build J node a b mem).control.val=J.seed+7 := Fin.val_cast_of_lt (by
    change J.seed+7<2^W₀
    rw [loc.seed]
    omega)
  refine ⟨⟨seedOff,?_,?_,by rw [cursor];omega,?_⟩,?_⟩
  · rw [loc.commands];apply pre <;> omega
  · rw [loc.arguments];apply pre <;> omega
  · intro job member
    obtain ⟨i,h⟩:=job_choices J node L R id job member
    have place:=job_endpoints J node L R i
    rcases h with h|h
    · have off:=maps_outside loc safe _ pins
      omega
    · have off:=safe.page 2 0 (by decide) (by decide) _ rows
      change x<root 0 ∨ root 0+4*(L.rows+R.rows)≤x at off
      omega
  · unfold HistoryPartyPair.hub
    rw [loc.seed];apply pre <;> omega

end PhysicalPair

section LiveArm
open private liveCheckJobs livePayloadJobs from OAI.ThreeFlat.RAM.HistoryRefreshElectedJobs

open Diagonal Diagonal.MotifOrderedCells Diagonal.MotifOuterTerms Diagonal.MotifSelectorChecks
open HistoryPartySpecialization
variable {K : Type} [CommRing K] [Fintype K] {H : Type*} {r s e k b d B ar : ℕ}
  (tile : Tile K H e d b) (good : (Fin (e*k)→Bool)→Prop) (letter : (Fin (e*k)→Bool)→Fin s)
  (tp : b+(e*d+e*d)≤ar) (sp : e*k+s≤ar) (A : HistoryPartyBatch.Layout) (node : ℕ)
  (input : Memory (16*u^10)) (t : Fin (B+1)) (z : Histogram (Fin s) r)
local notation "lib" => HistoryStaticArchive.all K ar
local notation "X" => electedBatch tile good letter tp sp A input true
variable (readC : Reads (electedBatch tile good letter tp sp A input true).regs
  (numeric (electedBatch tile good letter tp sp A input true).bootImage) (HistoryStaticArchive.all K ar) r t)
local notation "SC" => MotifNativeCompactors.partialInput K r t.val
local notation "PC" => MotifNativeCompactors.partialInput K (r*d) t.val
local notation "L" => admission good letter SC z
local notation "R" => tiled tile PC
local notation "a₀" => r*(e*k)
local notation "b₀" => r*b+e*(r*d)
local notation "dimsC" => checks_fields tile good letter tp sp (X).regs (numeric (X).bootImage) t readC
local notation "compsC" => components good letter SC z
local notation "idxC" => Fin.cast (congrArg₂ Nat.add (dimsC).1 (dimsC).2.1)
local notation "jobsC" => liveCheckJobs tile good letter tp sp A input t z readC
local notation "postC" => (X).published jobsC
local notation "Y" => electedBatch tile good letter tp sp A postC false
variable (readP : Reads (electedBatch tile good letter tp sp A ((electedBatch tile good letter tp sp A input true).published (liveCheckJobs tile good letter tp sp A input t z readC)) false).regs
  (numeric (electedBatch tile good letter tp sp A ((electedBatch tile good letter tp sp A input true).published (liveCheckJobs tile good letter tp sp A input t z readC)) false).bootImage) (HistoryStaticArchive.all K ar) r t)
local notation "dimsP" => payload_fields tile good letter tp sp (Y).regs (numeric (Y).bootImage) t readP
local notation "compsP" => pieces (checkedTile tile.rule tile.table) PC
local notation "idxP" => Fin.cast (congrArg₂ Nat.add (dimsP).1 (dimsP).2.1)
local notation "jobsP" => livePayloadJobs tile good letter tp sp A postC t readP
local notation "postP" => (Y).published jobsP
local notation "builder" => HistoryPartyPairExec.build A node a₀ b₀ postP
local notation "pairJobs" => HistoryPartyPairExec.steps (w:=W₀) A node L R tag


/-- Both batch passes and the actual selected pair preserve every physical word outside
the node. All job endpoints are derived from the emitted typed tapes and page bounds. -/
theorem elected_pair_away (room : ElectedRoom tile good letter tp sp A node input t z readC readP)
    (loc : PartyWindow u A)
    (checksCount : (X).count≤V) (checkRows : 8*HistoryPartyTapeRun.batchRows (X).table≤V)
    (checkPins : HistoryPartyTapeRun.batchPins (X).table≤V)
    (payloadCount : (Y).count≤V) (payloadRows : 8*HistoryPartyTapeRun.batchRows (Y).table≤V)
    (payloadPins : HistoryPartyTapeRun.batchPins (Y).table≤V)
    (pairPins : a₀+b₀≤V) (pairRows : 4*((L).rows+(R).rows)≤V) :
    ∀ x, PartyAway u A node x → electedOutput tile good letter tp sp A node input t z readC readP x=input x := by
  intro x safe
  have sc : (X).table.stream=dest A true node 0 := by
    change dest A true (numeric input A.cursor-1) 0=_
    rw [room.before]
  have sy : (Y).table.stream=dest A false node 0 := by
    change dest A false (numeric postC A.cursor-1) 0=_
    rw [room.middle]
  have cc : BatchAway X jobsC x:=batch_away X loc safe _ _ _ room.before sc rfl checksCount checkRows checkPins
  have pc : BatchAway Y jobsP x:=batch_away Y loc safe _ _ _ room.middle sy rfl payloadCount payloadRows payloadPins
  have rest:=pair_keeps_windows A node L R tag postP loc x safe pairPins pairRows
  have result : (builder).outputBase=HistoryPartyPair.atPair A node 1:=by
    have row : HistoryPartyPair.word A (numeric postP) 6=HistoryPartyPair.atPair A node 1:=by
      change HistoryPartyPair.atPair A (numeric postP A.cursor-1) 1=_
      rw [room.pair.cursor]
    have cap : HistoryPartyPair.atPair A node 1<2^W₀:=room.pair.cap 6
    change (HistoryPartyPairExec.prepared A postP (HistoryPartyPair.hub A+6)).val=_
    have actual : HistoryPartyPairExec.prepared A postP (HistoryPartyPair.hub A+6)=
        (HistoryPartyPair.word A (numeric postP) (6 : Fin 25) : Word W₀) :=
      HistoryPartyPairExec.hub_read A postP (6 : Fin 25)
    rw [actual,row,Fin.val_cast_of_lt cap]
  apply elected_output_away tile good letter tp sp A node input t z readC readP x loc.seed_room loc.seed_room cc pc rest.1 rest.2
  rw [result]
  exact safe.page 2 1 (by decide) (by decide) 4 (by have:=loc.age;have:=(window_bounds loc).1;omega)


theorem elected_pair_outside (room : ElectedRoom tile good letter tp sp A node input t z readC readP)
    (loc : PartyWindow u A)
    (checksCount : (X).count≤V) (checkRows : 8*HistoryPartyTapeRun.batchRows (X).table≤V)
    (checkPins : HistoryPartyTapeRun.batchPins (X).table≤V)
    (payloadCount : (Y).count≤V) (payloadRows : 8*HistoryPartyTapeRun.batchRows (Y).table≤V)
    (payloadPins : HistoryPartyTapeRun.batchPins (Y).table≤V)
    (pairPins : a₀+b₀≤V) (pairRows : 4*((L).rows+(R).rows)≤V) :
    ∀ x, OutsideNode u node x → electedOutput tile good letter tp sp A node input t z readC readP x=input x :=
  fun x safe=>elected_pair_away tile good letter tp sp A node input t z readC readP room loc checksCount checkRows checkPins
    payloadCount payloadRows payloadPins pairPins pairRows x (.of_outside loc safe)

/-- The elected frame uses three numerical page budgets: maximum number of batch jobs,
total compiled child rows and the total input slots of the LUTs and both compactors. -/
theorem elected_room_away
    (room : ElectedRoom tile good letter tp sp A node input t z readC readP) (loc : PartyWindow u A)
    (count : r+max s e≤V) (gates : 8*((L).rows+(R).rows)≤V)
    (pins : (r*(e*k+s)+s*(r+(r+r)))+
      (r*(b+(e*d+e*d))+e*(r*d+(r*d+r*d)))≤V) :
    ∀ x, PartyAway u A node x → electedOutput tile good letter tp sp A node input t z readC readP x=input x := by
  have rc := batch_info X _ (fun i=>(compsC i).net) (fun i=>(compsC i).wire) (dimsC).1 (dimsC).2.1
    (checks_dimensions tile good letter tp sp (X).regs (numeric (X).bootImage) t readC z) (dimsC).2.2.1 (dimsC).2.2.2.1
  have shared : (Y).table.shared=e*(r*d)+e*(r*d) := (dimsP).2.2.2.1.trans (two_mul _)
  have rp := batch_info Y _ (fun i=>(compsP i).N) (fun i=>(compsP i).wire) (dimsP).1 (dimsP).2.1
    (payload_dimensions tile good letter tp sp (Y).regs (numeric (Y).bootImage) t readP) (dimsP).2.2.1 shared
  have checks : (L).rows=HistoryPartyTapeRun.batchRows (X).table:=(congrArg Info.factors rc).symm
  have payload : (R).rows=HistoryPartyTapeRun.batchRows (Y).table:=(congrArg Info.factors rp).symm
  have checkR : (X).table.r=r := (dimsC).1
  have checkS : (X).table.s=s := (dimsC).2.1
  have payR : (Y).table.r=r := (dimsP).1
  have payS : (Y).table.s=e := (dimsP).2.1
  have checkLeft : (X).table.left.arity=e*k+s :=
    congrArg Diagonal.HistoryContraction.Tree.BatchRows.Size.arity (dimsC).2.2.2.2.1
  have checkRight : (X).table.right.arity=r+(r+r) :=
    congrArg Diagonal.HistoryContraction.Tree.BatchRows.Size.arity (dimsC).2.2.2.2.2
  have payLeft : (Y).table.left.arity=b+(e*d+e*d) :=
    congrArg Diagonal.HistoryContraction.Tree.BatchRows.Size.arity (dimsP).2.2.2.2.1
  have payRight : (Y).table.right.arity=r*d+(r*d+r*d) :=
    congrArg Diagonal.HistoryContraction.Tree.BatchRows.Size.arity (dimsP).2.2.2.2.2
  have checksPins : HistoryPartyTapeRun.batchPins (X).table=r*(e*k+s)+s*(r+(r+r)) := by
    rw [HistoryPartyTapeRun.batchPins,checkR,checkS,checkLeft,checkRight]
  have payloadPins : HistoryPartyTapeRun.batchPins (Y).table=r*(b+(e*d+e*d))+e*(r*d+(r*d+r*d)) := by
    rw [HistoryPartyTapeRun.batchPins,payR,payS,payLeft,payRight]
  apply elected_pair_away tile good letter tp sp A node input t z readC readP room loc
  · rw [←room.checks.count,checkR,checkS]
    exact (Nat.add_le_add_left (le_max_left s e) _).trans count
  · rw [←checks];omega
  · rw [checksPins];omega
  · rw [←room.payload.count,payR,payS]
    exact (Nat.add_le_add_left (le_max_right s e) _).trans count
  · rw [←payload];omega
  · rw [payloadPins];omega
  · have a:=Nat.mul_le_mul_left r (show e*k≤e*k+s by omega)
    have b₁:=Nat.mul_le_mul_left r (show b≤b+(e*d+e*d) by omega)
    have b₂:=Nat.mul_le_mul_left e (show r*d≤r*d+(r*d+r*d) by omega)
    omega
  · omega

theorem elected_room_outside
    (room : ElectedRoom tile good letter tp sp A node input t z readC readP) (loc : PartyWindow u A)
    (count : r+max s e≤V) (gates : 8*((L).rows+(R).rows)≤V)
    (pins : (r*(e*k+s)+s*(r+(r+r)))+
      (r*(b+(e*d+e*d))+e*(r*d+(r*d+r*d)))≤V) :
    ∀ x, OutsideNode u node x → electedOutput tile good letter tp sp A node input t z readC readP x=input x :=
  fun x safe=>elected_room_away tile good letter tp sp A node input t z readC readP room loc count gates pins x (.of_outside loc safe)

end LiveArm
end
end ThreeFlat.RAM.HistoryRefreshEmitter

namespace ThreeFlat.RAM.HistoryRefreshEmitter
open Computability.VPVNP.BurstRAM PrivateRAM HistoryStageBody.Physical Diagonal.TickWorkspace HistoryScratch
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryPartyBatchExec
open HistoryBoundedJoin HistoryMotifJoin HistoryPartyBatch HistoryBoundedBody BitNetwork.Ordered
open HistoryPartyTapeRun
open scoped BigOperators Classical Fin.CommRing
noncomputable section
section PhysicalElected
open private liveCheckJobs livePayloadJobs from OAI.ThreeFlat.RAM.HistoryRefreshElectedJobs

open Diagonal Diagonal.MotifOrderedCells Diagonal.MotifOuterTerms Diagonal.MotifSelectorChecks
open HistoryPartySpecialization
variable {K : Type} [CommRing K] [Fintype K] {H : Type*} {r s e k b d B ar : ℕ}
  (tile : Tile K H e d b) (good : (Fin (e*k)→Bool)→Prop) (letter : (Fin (e*k)→Bool)→Fin s)
  (tp : b+(e*d+e*d)≤ar) (sp : e*k+s≤ar) (u : ℕ) (arch:HistoryStageBody.Physical.Archive)
  (f:Family) (g:ℕ) (j:Fin f.parties) (node:ℕ)
local notation "V" => volume u
local notation "W" => 16*u^10
local notation "A" => (rawParty (layout u arch f) g j.val).party
variable (input : Memory (16*u^10)) (t : Fin (B+1)) (z : Histogram (Fin s) r)
local notation "lib" => HistoryStaticArchive.all K ar
local notation "X" => electedBatch tile good letter tp sp A input true
variable (readC : Reads (electedBatch tile good letter tp sp ((rawParty (layout u arch f) g j.val).party) input true).regs
  (numeric (electedBatch tile good letter tp sp ((rawParty (layout u arch f) g j.val).party) input true).bootImage) (HistoryStaticArchive.all K ar) r t)
local notation "SC" => MotifNativeCompactors.partialInput K r t.val
local notation "PC" => MotifNativeCompactors.partialInput K (r*d) t.val
local notation "L" => admission good letter SC z
local notation "R" => tiled tile PC
local notation "a₀" => r*(e*k)
local notation "b₀" => r*b+e*(r*d)
local notation "dimsC" => checks_fields tile good letter tp sp (X).regs (numeric (X).bootImage) t readC
local notation "compsC" => components good letter SC z
local notation "idxC" => Fin.cast (congrArg₂ Nat.add (dimsC).1 (dimsC).2.1)
local notation "jobsC" => liveCheckJobs tile good letter tp sp A input t z readC
local notation "postC" => (X).published jobsC
local notation "Y" => electedBatch tile good letter tp sp A postC false
variable (readP : Reads (electedBatch tile good letter tp sp ((rawParty (layout u arch f) g j.val).party) ((electedBatch tile good letter tp sp ((rawParty (layout u arch f) g j.val).party) input true).published (liveCheckJobs tile good letter tp sp ((rawParty (layout u arch f) g j.val).party) input t z readC)) false).regs
  (numeric (electedBatch tile good letter tp sp ((rawParty (layout u arch f) g j.val).party) ((electedBatch tile good letter tp sp ((rawParty (layout u arch f) g j.val).party) input true).published (liveCheckJobs tile good letter tp sp ((rawParty (layout u arch f) g j.val).party) input t z readC)) false).bootImage) (HistoryStaticArchive.all K ar) r t)
local notation "dimsP" => payload_fields tile good letter tp sp (Y).regs (numeric (Y).bootImage) t readP
local notation "compsP" => pieces (checkedTile tile.rule tile.table) PC
local notation "idxP" => Fin.cast (congrArg₂ Nat.add (dimsP).1 (dimsP).2.1)
local notation "jobsP" => livePayloadJobs tile good letter tp sp A postC t readP
local notation "postP" => (Y).published jobsP

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
/-- The complete elected room from the two physical tape boots, the mounted ROM
and the real two-child tree sizes. The motif and party are arbitrary valid slots. -/
theorem physical_elected_room (age:16≤u) (nr:node<V^2) (motifs:g<f.motifs)
    (cap:(f.motifs+2)*(f.parties+2)*8*32≤V) (mask:2^f.parties<2^W)
    (cursor:numeric input (A).cursor-1=node)
    (lut:arch.lut+HistoryStaticArchive.size (HistoryStaticArchive.count K ar) ar<2^W ∧
      (arch.lut+HistoryStaticArchive.size (HistoryStaticArchive.count K ar) ar≤base u 12 ∨ base u 19≤arch.lut))
    (compact:arch.pages+StableCompactROMNative.size B<2^W ∧
      (arch.pages+StableCompactROMNative.size B≤base u 12 ∨ base u 19≤arch.pages))
    (library:HistoryPartyTapeRun.Archive (D:=B) tag lib arch.lut arch.pages input)
    (lutStep:arch.lutStride=HistoryStaticArchive.stride ar) (romStep:arch.pageStride=StableCompactROMPool.page B 12)
    (level:t.val=HistogramTileNetwork.siteHeight r d) (work:StableCompactNativeBudget.budget t.val<2^W)
    (quota:∀ a:Fin s,numeric (X).bootImage (numeric (X).bootImage ((X).regs.incident+1)+a.val)=(z.val a).val)
    (seedC:ElectedSeed u X) (seedP:ElectedSeed u Y)
    (rows:8*((L).rows+(R).rows)≤V)
    (mapRoom:(r*(e*k+s)+s*(r+(r+r)))+(r*(b+(e*d+e*d))+e*(r*d+(r*d+r*d)))≤V)
    (countRoom:23*(r+max s e)≤V) (hidden:(L).bits+(R).bits≤V)
    (tags:∀ a:(Fin 3→Bool)→K,tag a<2^W) (bank:e*d<2^W) (stripe:r*d<2^W) :
    ElectedRoom tile good letter tp sp A node input t z readC readP := by
  let nC:=fun i=>(compsC i).net
  let wC:=fun i=>(compsC i).wire
  let nP:=fun i=>(compsP i).N
  let wP:=fun i=>(compsP i).wire
  have rc : (X).table.r = r := (dimsC).1
  have sc : (X).table.s = s := (dimsC).2.1
  have rp : (Y).table.r = r := (dimsP).1
  have spRows : (Y).table.s = e := (dimsP).2.1
  have sizesC:=checks_dimensions tile good letter tp sp (X).regs (numeric (X).bootImage) t readC z
  have sizesP:=payload_dimensions tile good letter tp sp (Y).regs (numeric (Y).bootImage) t readP
  have sharedP : (Y).table.shared = e*(r*d)+e*(r*d) :=
    (dimsP).2.2.2.1.trans (two_mul _)
  have shC:=shape_of_sizes (X).table (dimsC).1 (dimsC).2.1 nC wC sizesC (dimsC).2.2.1 (dimsC).2.2.2.1
  have shP:=shape_of_sizes (Y).table (dimsP).1 (dimsP).2.1 nP wP sizesP (dimsP).2.2.1 sharedP
  have srC:batchRows (X).table=(L).rows:=congrArg Info.factors
    (batch_info X _ nC wC (dimsC).1 (dimsC).2.1 sizesC (dimsC).2.2.1 (dimsC).2.2.2.1)
  have srP:batchRows (Y).table=(R).rows:=congrArg Info.factors
    (batch_info Y _ nP wP (dimsP).1 (dimsP).2.1 sizesP (dimsP).2.2.1 sharedP)
  have cutC:23*((X).table.r+(X).table.s)≤V:=by
    rw [rc,sc]
    exact (Nat.mul_le_mul_left 23 (Nat.add_le_add_left (Nat.le_max_left s e) r)).trans countRoom
  have cutP:23*((Y).table.r+(Y).table.s)≤V:=by
    rw [rp,spRows]
    exact (Nat.mul_le_mul_left 23 (Nat.add_le_add_left (Nat.le_max_right s e) r)).trans countRoom
  have cc:8*batchRows (X).table≤V:=by omega
  have cp:8*batchRows (Y).table≤V:=by omega
  have loc:PartyWindow u A:=PartyWindow.of_layout arch f g j.val age motifs j.isLt cap
  obtain ⟨vbig,scale,s14,s15,s16,s18,word⟩:=window_bounds loc
  have words:2+V+((L).bits+(R).bits)<2^W:=by
    have large:=Diagonal.TickWorkspace.word_space (u:=u) (i:=0) (by omega:1≤u) (by change 0<V^4;positivity)
    change base u 0+V^4<2^W at large;omega
  have mc:batchPins (X).table=r*(e*k+s)+s*(r+(r+r)):=by
    have left : (X).table.left.arity = e*k+s :=
      congrArg Diagonal.HistoryContraction.Tree.BatchRows.Size.arity (dimsC).2.2.2.2.1
    have right : (X).table.right.arity = r+(r+r) :=
      congrArg Diagonal.HistoryContraction.Tree.BatchRows.Size.arity (dimsC).2.2.2.2.2
    rw [batchPins, rc, sc, left, right]
  have mp:batchPins (Y).table=r*(b+(e*d+e*d))+e*(r*d+(r*d+r*d)):=by
    have left : (Y).table.left.arity = b+(e*d+e*d) :=
      congrArg Diagonal.HistoryContraction.Tree.BatchRows.Size.arity (dimsP).2.2.2.2.1
    have right : (Y).table.right.arity = r*d+(r*d+r*d) :=
      congrArg Diagonal.HistoryContraction.Tree.BatchRows.Size.arity (dimsP).2.2.2.2.2
    rw [batchPins, rp, spRows, left, right]
  have checkPins:batchPins (X).table≤V:=by omega
  have payPins:batchPins (Y).table≤V:=by omega
  have pairPins:a₀+b₀≤V:=by
    simp only [Nat.mul_add] at mapRoom
    omega
  have boundC:2+batchPins (X).table+(Tree.batch nC wC).bits<2^W:=by change 2+batchPins (X).table+(L).bits<_;omega
  have boundP:2+batchPins (Y).table+(Tree.batch nP wP).bits<2^W:=by change 2+batchPins (Y).table+(R).bits<_;omega
  have wsizeC:=child_width_from_batch u X _ nC wC (dimsC).1 (dimsC).2.1 sizesC boundC
  have wsizeP:=child_width_from_batch u Y _ nP wP (dimsP).1 (dimsP).2.1 sizesP boundP
  have bC:(X).table.e*(X).table.d<2^W:=bank
  have bP:(Y).table.e*(Y).table.d<2^W:=bank
  have stC:(X).table.r*(X).table.d<2^W:=by rw [rc];exact stripe
  have stP:(Y).table.r*(Y).table.d<2^W:=by rw [rp];exact stripe
  have afterMaps : base u 18 + 6*V ≤ base u 19 :=
    (Nat.add_le_add_left ((Nat.mul_le_mul_right V (by decide : 6 ≤ 30)).trans scale) _).trans s18
  have lutSpan := And.intro lut.1 (lut.2.imp_right afterMaps.trans)
  have compSpan := And.intro compact.1 (compact.2.imp_right afterMaps.trans)
  have left:=elected_batch_room_at u arch f node g j true X _ nC wC tag lib t (dimsC).1 (dimsC).2.1
    rfl rfl age nr motifs cap cursor mask seedC cc checkPins cutC lutSpan compSpan library work shC wsizeC tags bC stC
  have safe:OutsideNode u node (A).cursor:=outside_of_region node age nr (Or.inr (Or.inr (Or.inl rfl)))
  have lc: (X).table.stream=dest A true node 0:=by change dest A true (numeric input (A).cursor-1) 0=_;rw [cursor]
  have keepC (x:ℕ) (safe:OutsideNode u node x) : postC x=input x:=
    (batch_outside_node X loc safe (fun i=>nC (idxC i)) (fun i=>wC (idxC i)) tag cursor lc rfl
      (by have:=seedC.count;omega) cc checkPins).keeps left.seed.seedRoom
  have atC:numeric postC (A).cursor-1=node:=by unfold numeric;rw [keepC _ safe];exact cursor
  have archivePass (b size:ℕ) (span:b+size≤base u 12 ∨ base u 19≤b) (q:Fin size) :
      postC (b+q.val)=input (b+q.val):=by
    have bound:=q.isLt
    exact keepC _ (outside_of_region node age nr (by omega))
  have libraryP:HistoryPartyTapeRun.Archive (D:=B) tag lib arch.lut arch.pages postC:=
    ⟨fun q=>(archivePass _ _ lut.2 q).trans (library.fixed q),
      fun q=>(archivePass _ _ compact.2 q).trans (library.compact q)⟩
  have right:=elected_batch_room_at u arch f node g j false Y _ nP wP tag lib t (dimsP).1 (dimsP).2.1
    rfl rfl age nr motifs cap atC mask seedP cp payPins cutP lutSpan compSpan libraryP work shP wsizeP tags bP stP
  have lp:(Y).table.stream=dest A false node 0:=by change dest A false (numeric postC (A).cursor-1) 0=_;rw [atC]
  have keptP:postP (A).cursor=postC (A).cursor:=
    (batch_outside_node Y loc safe (fun i=>nP (idxP i)) (fun i=>wP (idxP i)) tag atC lp rfl
      (by have:=seedP.count;omega) cp payPins).keeps right.seed.seedRoom
  have atP:numeric postP (A).cursor-1=node:=by unfold numeric;rw [keptP];exact atC
  have maxle:=HistogramTileNetwork.siteHeight_room r d
  rw [←level] at maxle
  have «meta»:(∀ i a k,HistoryCompiledRows.metadata tag (pairNetwork L R i) a k<2^W):=by
    intro i
    apply HistoryCompiledRows.metadata_fits tag _ _ tags
    fin_cases i
    · change 2+a₀+(L).compile.internal≤2^W;rw [compiled_bits];omega
    · change 2+b₀+(R).compile.internal≤2^W;rw [compiled_bits];omega
  have keepAt (bankIndex : Fin 2) (delta : ℕ) (within : delta<V) :
      BatchAway Y jobsP (dest A true node bankIndex.val+delta) := by
    apply physical_payload_retains u arch f node g j Y _ nP wP tag (dimsP).1 (dimsP).2.1
      rfl rfl age nr motifs cap atC seedP.count lp rfl cp payPins cutP bankIndex delta
    exact within
  refine ⟨(Nat.le_max_left ..).trans maxle,(Nat.le_max_right ..).trans maxle,lutStep,lutStep,romStep,romStep,
    quota,cursor,atC,left,right,?_,?_,physical_pair_room_at u arch f node g j L R tag postP age nr motifs cap
      pairPins rows (by omega) «meta» atP⟩
  · intro a
    apply keepAt (1:Fin 2) a.val
    have vb:16≤V:=age.trans ((Nat.le_self_pow (by decide:10≠0) u).trans Nat.lt_two_pow_self.le)
    have:=a.isLt;omega
  · intro i a
    let offset := 4*(L).rows + (4*i.val+a.val)
    have offsetRoom : offset<V := by
      dsimp [offset]
      have h : i.val < (L).rows := lt_of_lt_of_eq i.isLt (compiled_rows (L))
      have digit:=a.isLt
      omega
    rw [Nat.add_assoc (dest A true node 0) (4*(L).rows) (4*i.val+a.val)]
    exact keepAt (0:Fin 2) offset offsetRoom

end PhysicalElected
end
end ThreeFlat.RAM.HistoryRefreshEmitter

namespace ThreeFlat.RAM.HistoryRefreshEmitter


end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
