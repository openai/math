import OAI.ThreeFlat.RAM.HistoryRefreshPhysicalOrder

namespace OAI
/-! # Physical placement of elected refresh batches -/
set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryRefreshEmitter

set_option maxRecDepth 6000

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryPartyBatchExec
open HistoryBoundedJoin HistoryMotifJoin HistoryPartyBatch HistoryBoundedBody BitNetwork.Ordered
open scoped BigOperators Classical Fin.CommRing

noncomputable section
variable {W p a b : ℕ} {F : Type*}
variable [CommRing F]

open private sum_blocks from OAI.ThreeFlat.RAM.HistoryRefreshBatch

section PhysicalOrder
open HistoryStageBody.Physical Diagonal.TickWorkspace HistoryScratch
variable (u : ℕ) (arch : HistoryStageBody.Physical.Archive) (f : Family) (node : ℕ) (winner : Fin f.parties)
local notation "A" => layout u arch f
local notation "V" => volume u
local notation "W₀" => 16*u^10

section ElectedPlacement
open HistoryPartyTapeRun
variable (g : ℕ) (j : Fin f.parties) (ck : Bool) (T : HistoryBatchTape.Header) {h z ar d : ℕ}
  {arity : Fin (T.r+T.s)→ℕ} (nets : (i:Fin (T.r+T.s))→BitNetwork F (arity i))
  (wire : ∀ i,Fin (arity i)→BitSource h p) (tag : ((Fin 3→Bool)→F)→ℕ)
local notation "J" => (rawParty A g j.val).party

omit [CommRing F] in
/-- The actual checks or payload tape occupies one fixed S12 local window plus the
S18 map area. The LUT and the compactor lie independently outside both write areas. -/
theorem physical_batch_windows_at [Fintype F] (age : 16≤u) (count : node<V^2) (motifs : g<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V)
    (stream : T.stream=dest J ck node 0) (maps : T.maps=(J).maps) (args : T.args=(J).arguments)
    (rows : 8*batchRows T≤V) (pins : batchPins T≤V) (children : 23*(T.r+T.s)≤V)
    (lut : arch.lut+HistoryStaticArchive.size z ar≤2^W₀) (compact : arch.pages+StableCompactROMNative.size d≤2^W₀)
    (lutArea : arch.lut+HistoryStaticArchive.size z ar≤base u 12 ∨ base u 18+6*V≤arch.lut)
    (compArea : arch.pages+StableCompactROMNative.size d≤base u 12 ∨ base u 18+6*V≤arch.pages) :
    HistoryPartyTapeRun.Space (z:=z) (B:=ar) (D:=d) T nets wire tag arch.lut arch.pages
      (((J).seed+33:ℕ):Word W₀) (J).commands := by
  let block:Local:=⟨g+2,j.val+2,ck.toNat,0⟩
  have ok : block.Valid f.motifs f.parties:=by
    change g+2 < f.motifs+2 ∧ j.val+2 < f.parties+2 ∧ ck.toNat < 8 ∧ 0 < 32
    refine ⟨Nat.add_lt_add_right motifs 2, Nat.add_lt_add_right j.isLt 2, ?_, by decide⟩
    cases ck <;> decide
  have win:=local_window u f node age count capacity block ok
  change base u 12≤dest J ck node 0 ∧ dest J ck node 0+V≤base u 12+Diagonal.TickWorkspace.stride u ∧ _ at win
  rw [←stream] at win
  have big : 1024≤V:=Nat.pow_le_pow_right (by decide : 0<2)
    ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have scale : 10*V≤V^4:=calc
    _≤V*V:=Nat.mul_le_mul_right _ (by omega)
    _=V^2:=(pow_two V).symm
    _≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have s12:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 12<14)
  have s14:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 14<15)
  have s15:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 15<16)
  have s16:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 16<18)
  have words:=word_space (i:=18) (by omega : 1≤u) (by change 18<V^4;omega)
  change base u 14+V^4≤base u 15 at s14
  change base u 15+V^4≤base u 16 at s15
  change base u 16+V^4≤base u 18 at s16
  change base u 18+V^4<2^W₀ at words
  change T.maps=base u 18+5*V at maps
  change T.args=base u 16 at args
  have ctrlRoom : base u 14+V+33 < 2^W₀ := by omega
  have control : (((J).seed+33:ℕ):Word W₀).val=base u 14+V+33 :=
    Fin.val_cast_of_lt ctrlRoom
  apply space_of_windows T nets wire tag arch.lut arch.pages (((J).seed+33:ℕ):Word W₀) (J).commands
    (by change base u 15+21*(T.r+T.s)≤_;omega) (by omega) lut compact (by omega) (by omega) (.inl (by omega))
    (.inr (by rw [control];omega)) (.inl (by rw [control];omega))
  intro x valid
  rw [control]
  change ((base u 15≤x ∧ x<base u 15+21*(T.r+T.s)) ∨ _ ∨ _ ∨ _) at valid
  rcases valid with c|a|l|p <;> omega

/-- The numeric rooms for the four immutable tables the elected batch header really reads.
The two seed groups lie in S14 and are handled by the procedure itself. -/
def archiveWindow (u start width:ℕ) := start+width<2^(16*u^10) ∧
  (start+width≤base u 12 ∨ base u 18 ≤ start)

theorem archiveWindow.sub {u b n d l:ℕ} (full : archiveWindow u b n)
    (lo:b≤d) (hi:d+l≤b+n) : archiveWindow u d l:=by
  rcases full with ⟨word,low|high⟩
  · exact ⟨by omega,.inl (by omega)⟩
  · exact ⟨by omega,.inr (by omega)⟩

section SelectedPages
open HistoryStageBody.Physical
variable {K:Type} [Field K] [Fintype K] (B:Diagonal.PhysicalStage.Block K)
  {height start n parties:ℕ} {grid:Grid K} {pre tail:List (Grid K)} {cells:Fin n→Fin parties→Party K}
  (gridAt:grids B=pre++grid::tail) (rowsAt:grid.rows=HistoryStageBody.Physical.grid cells)
  (i:Fin n) (j:Fin parties)
local notation "lib0" => start+StableCompactROMNative.size height
local notation "cnt0" => start+StableCompactROMNative.size height+staticSize B
local notation "grid0" => (grid.family (Mounted.base B height start pre)).kinds
local notation "ar" => HistoryStageBody.Physical.arity B

include gridAt rowsAt in
/-- All variable lookups of the elected seed and batch lie inside the one mounted
region. The dimensions are obtained from the genuine fixed program and row number. -/
theorem selected_archive_windows (whole:archiveWindow u start (libraryWords B height)) :
    archiveWindow u start (StableCompactROMNative.size height) ∧
    archiveWindow u lib0 (staticSize B) ∧ archiveWindow u cnt0 (HistoryCompactorCounts.size height) ∧
    archiveWindow u (grid0+7*(i.val*parties+j.val)) 7 ∧
    (∀ l:Fin (HistoryStaticArchive.count K ar),
      archiveWindow u (lib0+HistoryStaticArchive.stride ar*l.val) 2) ∧
    (∀ t:Fin (height+1),archiveWindow u (cnt0+2*t.val) 2 ∧
      start+StableCompactROMPool.page height 12*t.val<2^W₀) := by
  have total : libraryWords B height=StableCompactROMNative.size height+staticSize B+
      HistoryCompactorCounts.size height+gridSize B:=rfl
  have l0:archiveWindow u start (StableCompactROMNative.size height):=whole.sub le_rfl (by rw [total];omega)
  have l1:archiveWindow u lib0 (staticSize B):=whole.sub (by omega) (by rw [total];omega)
  have l2:archiveWindow u cnt0 (HistoryCompactorCounts.size height):=whole.sub (by omega) (by rw [total];omega)
  have cut : (pre.map Grid.size).sum+grid.size≤gridSize B:=by
    rw [gridSize,gridAt,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    omega
  have get:grid.rows[i.val*parties+j.val]?=some (cells i j):=by
    rw [rowsAt,Nat.mul_comm i.val parties]
    exact grid_row cells i j
  obtain ⟨hr,_⟩:=List.getElem?_eq_some_iff.mp get
  have row:=Nat.mul_le_mul_left 7 hr
  rw [Nat.mul_succ] at row
  have gw:7*grid.rows.length≤grid.size:=Nat.mul_le_mul_right _ (by omega:7≤7+grid.stride)
  have gd:archiveWindow u (grid0+7*(i.val*parties+j.val)) 7:=by
    apply whole.sub
    · change start≤cnt0+HistoryCompactorCounts.size height+(pre.map Grid.size).sum+7*(i.val*parties+j.val);omega
    · change cnt0+HistoryCompactorCounts.size height+(pre.map Grid.size).sum+7*(i.val*parties+j.val)+7≤_
      rw [total];omega
  refine ⟨l0,l1,l2,gd,?_,?_⟩
  · intro l
    have h:=Nat.mul_le_mul_left (HistoryStaticArchive.stride ar) l.isLt
    rw [Nat.mul_succ,Nat.mul_comm (HistoryStaticArchive.stride ar) (HistoryStaticArchive.count K ar)] at h
    have min : 2≤HistoryStaticArchive.stride ar:=by unfold HistoryStaticArchive.stride;omega
    apply l1.sub (by omega)
    change _≤lib0+HistoryStaticArchive.count K ar*HistoryStaticArchive.stride ar;omega
  · intro t
    constructor
    · apply l2.sub (by omega)
      change _≤cnt0+2*(height+1);have:=t.isLt;omega
    · have h:=Nat.mul_le_mul_left (StableCompactROMPool.page height 12) t.isLt
      rw [Nat.mul_succ,Nat.mul_comm (StableCompactROMPool.page height 12) (height+1)] at h
      have max:=l0.1
      change start+(height+1)*StableCompactROMPool.page height 12<2^W₀ at max
      omega
/-- The native seed's public strides, together with the three catalogue bases,
fit as consequences of the complete image fitting. -/
theorem mounted_arch_registers (whole:archiveWindow u start (libraryWords B height)) :
    lib0<2^W₀ ∧ HistoryStaticArchive.stride ar<2^W₀ ∧ start<2^W₀ ∧
    StableCompactROMPool.page height 12<2^W₀ ∧ cnt0<2^W₀ := by
  have boundAll : start+libraryWords B height < 2^W₀ := whole.1
  change start+(((height+1)*StableCompactROMPool.page height 12+staticSize B)+HistoryCompactorCounts.size height+gridSize B)<2^W₀ at boundAll
  have page : StableCompactROMPool.page height 12 ≤
      (height+1)*StableCompactROMPool.page height 12 :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos height)
  have npos : 0 < HistoryStaticArchive.count K ar := by
    change 0 < Fintype.card (HistoryStaticArchive.Entry K ar)
    exact Fintype.card_pos_iff.mpr ⟨⟨0, fun _ => 0⟩⟩
  have strideBound : HistoryStaticArchive.stride ar ≤ staticSize B :=
    Nat.le_mul_of_pos_left _ npos
  change start+(height+1)*StableCompactROMPool.page height 12<2^W₀ ∧ _ ∧ _ ∧ _ ∧
    start+(height+1)*StableCompactROMPool.page height 12+staticSize B<2^W₀
  omega

end SelectedPages

/-- All eleven raw seed registers and its physical branch count are computed
from the actual incident, the marked kind page, and the public layout. -/
theorem elected_registers_at (X : HistoryPartyBatchExec.Build W₀)
    (same:X.layout=J) (side:X.checks=ck) (age:16≤u) (nr:node<V^2) (motifs:g<f.motifs)
    (cap:(f.motifs+2)*(f.parties+2)*8*32≤V) (atNode:numeric X.input (J).cursor-1=node)
    (active:occupied J (numeric X.input)) (r:ℕ) (copiesAt:numeric X.input (incident J (numeric X.input)+3)=r)
    (kind:∀ a:Fin 7,numeric X.input (shape J (numeric X.input)+a.val)=X.kind.words a)
    (ir:archiveWindow u (incident J (numeric X.input)) 4) (gr:archiveWindow u (shape J (numeric X.input)) 7)
    (catalog:(J).lutBase<2^W₀ ∧ (J).lutStride<2^W₀ ∧ (J).compBase<2^W₀ ∧ (J).compStride<2^W₀ ∧ (J).countBase<2^W₀) :
    (∀ a:Fin 11,X.regs.words a<2^W₀) ∧ X.count=r+(if ck then X.kind.letters else X.kind.ports) ∧
      X.regs.streams=dest J ck node 0 ∧ X.regs.maps=(J).maps ∧ X.regs.arguments=(J).arguments := by
  let page:Local:=⟨g+2,j.val+2,ck.toNat,0⟩
  have ok:page.Valid f.motifs f.parties:=by
    change g+2 < f.motifs+2 ∧ j.val+2 < f.parties+2 ∧ ck.toNat < 8 ∧ 0 < 32
    refine ⟨Nat.add_lt_add_right motifs 2,Nat.add_lt_add_right j.isLt 2,?_,by decide⟩
    cases ck <;> decide
  have localRoom:=local_window u f node age nr cap page ok
  change _ ∧ _ ∧ dest J ck node 0+V<2^W₀ at localRoom
  have vbig:1024≤V:=Nat.pow_le_pow_right (by decide:0<2) ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) u))
  have grow:V ≤ Diagonal.TickWorkspace.stride u:=Nat.le_self_pow (by decide:4≠0) V
  have cube:10*V ≤ Diagonal.TickWorkspace.stride u:=calc
    _≤V*V:=Nat.mul_le_mul_right _ (by omega)
    _=V^2:=(pow_two V).symm
    _≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have word:=word_space (u:=u) (i:=18) (by omega:1≤u) ((by decide : 18<1024).trans_le (vbig.trans grow))
  have seed:=Diagonal.TickWorkspace.apart (u:=u) (by decide:14<18)
  have args:=Diagonal.TickWorkspace.apart (u:=u) (by decide:16<18)
  have streamFit : dest J ck node 0<2^W₀ := (Nat.le_add_right ..).trans_lt localRoom.2.2
  have incidentFit : incident J (numeric X.input) < 2^W₀ :=
    (Nat.le_add_right _ 4).trans_lt ir.1
  have kindFit : shape J (numeric X.input) < 2^W₀ :=
    (Nat.le_add_right _ 7).trans_lt gr.1
  obtain ⟨c₀,c₁,c₂,c₃,c₄⟩:=catalog
  have eq:X.regs=registers J ck (numeric X.input):=by unfold HistoryPartyBatchExec.Build.regs;rw [same,side]
  rw [eq]
  have why (a:Fin 11) : (registers J ck (numeric X.input)).words a<2^W₀:=by
    fin_cases a <;> simp only [HistoryPartyHeader.Registers.words,registers,ite_eq_left active,atNode,
      Matrix.cons_val_zero,Fin.reduceFinMk]
    all_goals first | exact incidentFit | exact kindFit | assumption | (change base u 16<2^W₀;omega) | (change base u 18+5*V<2^W₀;omega) |
      (change base u 14+V+1<2^W₀;omega)
  refine ⟨why,?_,?_,rfl,rfl⟩
  · change children X.layout X.checks (numeric X.input)=_
    rw [same,side];cases ck <;> simp only [children,HistoryPartyBatch.copies,kinds,ite_eq_left active,copiesAt]
    · exact congrArg (r+·) (kind 0)
    · exact congrArg (r+·) (kind 1)
  · change dest J ck (numeric X.input (J).cursor-1) 0=_
    rw [atNode]

omit [CommRing F] in
theorem physical_batch_source_at [Fintype F] (X : HistoryPartyBatchExec.Build W₀)
    (context : X.layout=J) (side : X.checks=ck) (table : X.table=T)
    (age : 16≤u) (count : node<V^2) (motifs : g<f.motifs) (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V)
    (cursor : numeric X.input (J).cursor-1=node) (mask : 2^f.parties<2^W₀)
    (probes : ∀ x,HistoryPartyBootExec.SeedRead J ck (numeric X.input) x→
      (x<base u 12 ∨ base u 18≤x) ∧ x<2^W₀)
    (power : 2^Nat.clog 2 (HistoryPartyBootExec.extent J (numeric X.input))<2^W₀)
    (registers : ∀ j,X.regs.words j<2^W₀) (grid : ∀ j:Fin 7,numeric X.bootImage (X.regs.grid+j.val)=X.kind.words j)
    (gridRoom : archiveWindow u X.regs.grid 7) (incidentRoom : archiveWindow u X.regs.incident 4)
    (lutRoom : archiveWindow u (X.regs.lutBase+X.regs.lutStride*(if ck then X.kind.selectorPage else X.kind.tilePage)) 2)
    (countRoom : archiveWindow u (X.regs.countBase+2*numeric X.bootImage (X.regs.dyadic+1)) 2)
    (quota : T.checks=true→0<T.s→archiveWindow u T.hist T.s)
    (header : ∀ t:Fin 26,T.words t<2^W₀) (length : T.r+T.s=X.count)
    (stream : T.stream=dest J ck node 0) (maps : T.maps=(J).maps)
    (rows : 8*batchRows T≤V) (_pins : batchPins T≤V) (nwords : 23*(T.r+T.s)≤V) :
    X.Source (jobs T nets wire tag) ∧
      (X.table.checks=true→0<X.table.s→X.table.hist+X.table.s≤X.layout.batch ∨
        X.layout.commands+21*X.count≤X.table.hist) := by
  let loc:=fun k=>(⟨g+2,j.val+2,ck.toNat,k⟩:Local)
  have ok (k:ℕ) (bound:k<32) : (loc k).Valid f.motifs f.parties:=by
    change g+2 < f.motifs+2 ∧ j.val+2 < f.parties+2 ∧ ck.toNat < 8 ∧ k < 32
    refine ⟨Nat.add_lt_add_right motifs 2, Nat.add_lt_add_right j.isLt 2, ?_, bound⟩
    cases ck <;> decide
  have win (k:ℕ) (bound:k<32) : base u 12≤dest J ck node k ∧ dest J ck node k+V≤base u 12+Diagonal.TickWorkspace.stride u:=
    ⟨(local_window u f node age count capacity _ (ok k bound)).1,(local_window u f node age count capacity _ (ok k bound)).2.1⟩
  have big : 1024≤V:=Nat.pow_le_pow_right (by decide : 0<2)
    ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have scale : 10*V≤V^4:=calc
    _≤V*V:=Nat.mul_le_mul_right _ (by omega)
    _=V^2:=(pow_two V).symm
    _≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have s12:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 12<14)
  have s14:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 14<15)
  have s15:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 15<16)
  have s16:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 16<18)
  have words:=word_space (i:=18) (by omega : 1≤u) (by change 18<V^4;omega)
  change base u 14+V^4≤base u 15 at s14
  change base u 15+V^4≤base u 16 at s15
  change base u 16+V^4≤base u 18 at s16
  change base u 18+V^4<2^W₀ at words
  have pSeed : X.layout.seed=base u 14+V := congrArg (fun L : HistoryPartyBatch.Layout => L.seed) context
  have pHeader : X.layout.batch=base u 14+2*V := congrArg (fun L : HistoryPartyBatch.Layout => L.batch) context
  have pCmd : X.layout.commands=base u 15 := congrArg (fun L : HistoryPartyBatch.Layout => L.commands) context
  have pArgs : X.layout.arguments=base u 16 := congrArg (fun L : HistoryPartyBatch.Layout => L.arguments) context
  have pDyadic : X.regs.dyadic=base u 14+V+1:=by
    change X.layout.seed+1=_;rw [pSeed]
  have pTarget : X.target=dest J ck node 1:=by
    change dest X.layout X.checks (numeric X.input X.layout.cursor-1) 1=_
    rw [context,side,cursor]
  have pCtrl : X.ctrl.val=base u 14+V+33:=by
    change ((X.layout.seed+33:ℕ):Word W₀).val=_;rw [pSeed];exact Fin.val_cast_of_lt (by omega)
  have later (s n t:ℕ) (h:archiveWindow u s n) (lt:t<n) :
      s+t<X.layout.batch ∨ X.layout.batch+26 ≤ s+t:=by
    have z:=h.2;rw [pHeader];omega
  have prep : HeaderProtected X.layout X.regs X.kind X.checks X.bootImage:=by
    refine ⟨?_,fun j=>later _ _ _ gridRoom j.isLt,fun j=>later _ _ _ incidentRoom j.isLt,?_,?_,
      fun j=>later _ _ _ countRoom j.isLt⟩
    · intro t;left;rw [pSeed,pHeader];have:=t.isLt;omega
    · intro t;left;rw [pDyadic,pHeader];have:=t.isLt;omega
    · intro t;dsimp only;rw [side];exact later _ _ _ lutRoom t.isLt
  have read : HistoryPartyHeader.ReadRoom W₀ X.regs X.kind X.checks (numeric X.bootImage):=by
    refine ⟨by have:=gridRoom.1;omega,by have:=incidentRoom.1;omega,by rw [pDyadic];omega,
      by rw [side];have:=lutRoom.1;omega,by have:=countRoom.1;omega⟩
  have mt : T.maps = base u 18 + 5*V := maps
  have streamEnd : T.stream + 8*batchRows T ≤ base u 14 := by
    rw [stream]
    exact (Nat.add_le_add_left rows _).trans ((win 0 (by decide)).2.trans s12)
  have targetEnd : X.target + 4 ≤ base u 14 := by
    rw [pTarget]
    exact (Nat.add_le_add_left (by omega : 4 ≤ V) _).trans ((win 1 (by decide)).2.trans s12)
  have high (z y : ℕ) (lo : base u 14 ≤ z) (hi : z+y ≤ base u 18) :
      HistoryReadyTape.Away z y (jobs (w:=W₀) T nets wire tag) := by
    intro job member
    rcases job_placement T nets wire tag job member with ⟨_, finish⟩ | ⟨start, _⟩
    · exact Or.inl (finish.trans (streamEnd.trans lo))
    · rw [mt] at start
      exact Or.inr (hi.trans ((Nat.le_add_right _ _).trans start))
  have countWords : 23*X.count ≤ V := by simpa only [length] using nwords
  have lowToSeed : base u 12 ≤ base u 14 := (Nat.le_add_right _ _).trans s12
  have qSmall : X.table.checks=true → ∀ i : Fin X.count, X.table.r ≤ i.val →
      X.table.hist+(i.val-X.table.r)<2^W₀ ∧ (X.table.hist+(i.val-X.table.r)<X.layout.arguments ∨
      X.layout.arguments+23*X.count≤X.table.hist+(i.val-X.table.r)) := by
    rw [table, pArgs]
    intro c i r
    have bound := i.isLt
    have index : i.val-T.r < T.s := by omega
    obtain ⟨fit, low | upper⟩ := quota c (by omega : 0 < T.s)
    · exact ⟨by omega, Or.inl (by omega)⟩
    · exact ⟨by omega, Or.inr (by omega)⟩
  constructor
  · refine {
      seedRoom := by rw [pSeed]; omega
      seedAway := ?_
      motifRoom := ?_
      seedProbeRoom := ?_
      partyRoom := ?_
      power := by simpa only [context] using power
      registerRoom := registers
      gridRead := grid
      headerRoom := by rw [pHeader]; omega
      headerProtected := prep
      headerReadRoom := read
      wordSize := by omega
      commandRoom := by rw [pCmd]; omega
      argumentRoom := by rw [pArgs]; omega
      headerBound := by simpa only [table] using header
      order := ⟨by rw [pSeed, pHeader]; omega, by rw [pHeader, pCmd]; omega,
        by rw [pCmd, pArgs]; omega⟩
      quotaRoom := qSmall
      awaySeed := high _ _ (by rw [pSeed]; omega) (by rw [pSeed]; omega)
      awayHeader := high _ _ (by rw [pHeader]; omega) (by rw [pHeader]; omega)
      awayCtrl := high _ _ (by rw [pCtrl]; omega) (by rw [pCtrl]; omega)
      awayCmd := high _ _ (by rw [pCmd]; omega) (by rw [pCmd, jobs_length]; omega)
      resultRoom := by omega
      resultBefore := Or.inl (by rw [pSeed]; omega) }
    · intro x hx
      rw [context, side] at hx
      rw [pSeed]
      rcases (probes x hx).1 with low | upper
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · rw [context]
      change g < 2^W₀
      have wide := Nat.le_mul_of_pos_right (f.motifs+2) (by omega : 0 < f.parties+2)
      omega
    · intro x hx
      rw [context, side] at hx
      exact (probes x hx).2
    · intro _
      rw [context]
      exact (Nat.pow_le_pow_right (by decide : 0 < 2) j.isLt.le).trans_lt mask
  · rw [table, pHeader, pCmd]
    intro c pos
    rcases (quota c pos).2 with low | upper
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

end ElectedPlacement

section BatchPlacement
open HistoryPartyTapeRun BitLayout
variable [Fintype F] (g : ℕ) (j : Fin f.parties) (ck : Bool) (X : HistoryPartyBatchExec.Build (16*u^10))
  {r s H z d ar : ℕ} (arity : Fin (r+s)→ℕ) (N : ∀ i,BitNetwork F (arity i))
  (wire : ∀ i,Fin (arity i)→BitSource H p) (tag : ((Fin 3→Bool)→F)→ℕ)
  (lib : HistoryStaticArchive.Catalog F z ar) (pow : Fin (d+1)) (hl : X.table.r=r) (hr : X.table.s=s)
local notation "J" => (rawParty A g j.val).party
local notation "T" => X.table
local notation "ix" => Fin.cast (congrArg₂ Nat.add hl hr)
local notation "N₀" => fun i=>N (ix i)
local notation "Wires" => fun i=>wire (ix i)
local notation "jobs" => HistoryPartyTapeRun.jobs (w:=W₀) T N₀ Wires tag

/-- Produce the complete regular-batch room on the real physical layout. The output
pointer is at the beginning of bank one, beyond both staged and translated rows. -/
theorem physical_batch_room (same : X.layout=(rawParty (layout u arch f) g j.val).party) (side : X.checks=ck)
    (age:16≤u) (nr:node<V^2) (motifs:g<f.motifs) (cap:(f.motifs+2)*(f.parties+2)*8*32≤V)
    (atNode:numeric X.input (J).cursor-1=node) (n:(T).r+(T).s=X.count)
    (room : X.Source jobs ∧ ((T).checks=true→0<(T).s→(T).hist+(T).s≤X.layout.batch ∨
      X.layout.commands+21*X.count≤(T).hist))
    (st : (T).stream=dest J ck node 0) (ma:(T).maps=(J).maps) (args:(T).args=(J).arguments)
    (gates:8*batchRows T≤V) (keys:batchPins T≤V) (children:23*((T).r+(T).s)≤V)
    (lut:arch.lut+HistoryStaticArchive.size z ar≤2^W₀) (compact:arch.pages+StableCompactROMNative.size d≤2^W₀)
    (lutZone:arch.lut+HistoryStaticArchive.size z ar≤base u 12 ∨ base u 18+6*V≤arch.lut)
    (romZone:arch.pages+StableCompactROMNative.size d≤base u 12 ∨ base u 18+6*V≤arch.pages)
    (archive : HistoryPartyTapeRun.Archive (D:=d) tag lib arch.lut arch.pages X.input)
    (budget:StableCompactNativeBudget.budget pow<2^W₀) (shape:HistoryPartyTapeRun.Shape (p:=p) (h:=H) T N₀)
    (bits:∀ i,2+arity (ix i)+(N (ix i)).internal≤2^W₀) (ids:∀ k,tag k<2^W₀)
    (arityFit:∀ i,2+arity (ix i)<2^W₀) (bank:(T).e*(T).d<2^W₀) (stripe:(T).r*(T).d<2^W₀) :
    BatchRoom X arity N wire tag lib pow arch.lut arch.pages hl hr := by
  have window:=physical_batch_windows_at u arch f node g j ck T N₀ Wires tag age nr motifs cap
    st ma args gates keys children lut compact lutZone romZone
  have ctrl:X.ctrl=(((J).seed+33:ℕ):Word W₀):=by change ((X.layout.seed+33:ℕ):Word W₀)=_;rw [same]
  have space:HistoryPartyTapeRun.Space (z:=z) (B:=ar) (D:=d) T N₀ Wires tag arch.lut arch.pages X.ctrl X.layout.commands:=by
    rw [ctrl,same];exact window
  have howMany (i:Fin ((T).r+(T).s)) : (N (ix i)).cells=(if i.val<(T).r then (T).left.rows else (T).right.rows):=by
    have h:=shape.count i
    change 4*(if i.val<(T).r then (T).left.rows else (T).right.rows)=4*(N (ix i)).cells at h;omega
  have sum : (glue N₀ Wires).cells=batchRows T:=by
    exact sum_blocks (fun i : Fin ((T).r+(T).s) => (N (ix i)).cells) _ _ howMany
  have target:X.target=dest J ck node 1:=by
    change dest X.layout X.checks (numeric X.input X.layout.cursor-1) 1=_;rw [same,side,atNode]
  have step : dest J ck node 1=dest J ck node 0+V:=by
    let start := (((g+2)*(f.parties+2)+(j.val+2))*8+ck.toNat)*32
    change base u 12+(node*V+(start+1))*V+0 =
      base u 12+(node*V+(start+0))*V+0+V
    ring
  have s12:=Diagonal.TickWorkspace.apart (u:=u) (by decide:12<14)
  have s16:=Diagonal.TickWorkspace.apart (u:=u) (by decide:16<18)
  have positive:0<V:=Nat.two_pow_pos _
  have grow : V ≤ Diagonal.TickWorkspace.stride u := Nat.le_self_pow (by decide : 4≠0) V
  have ls : arch.lut+HistoryStaticArchive.size z ar≤X.layout.seed ∨ X.layout.arguments+23*X.count≤arch.lut:=by
    rw [same];change _≤base u 14+V ∨ base u 16+23*X.count≤_;omega
  have rs : arch.pages+StableCompactROMNative.size d≤X.layout.seed ∨ X.layout.arguments+23*X.count≤arch.pages:=by
    rw [same];change _≤base u 14+V ∨ base u 16+23*X.count≤_;omega
  refine ⟨room.1,n,room.2,space,archive,ls,rs,budget,arityFit,
    fun i=>HistoryCompiledRows.metadata_fits tag (N (ix i)) (bits i) ids,bank,stripe,.inr ?_⟩
  change (T).stream+4*batchRows T+4*(glue N₀ Wires).cells≤X.target
  rw [sum,st,target,step];omega

omit [CommRing F] [Fintype F] in
/-- A payload pass retains both already-written checks banks of the same party,
including the translated stream at offset four times the checks row count. -/
theorem physical_payload_retains
    (same:X.layout=(rawParty (layout u arch f) g j.val).party) (side:X.checks=false) (age:16≤u) (nr:node<V^2)
    (motifs:g<f.motifs) (cap:(f.motifs+2)*(f.parties+2)*8*32≤V)
    (atNode:numeric X.input (J).cursor-1=node) (_n:(T).r+(T).s=X.count)
    (st:(T).stream=dest J false node 0) (ma:(T).maps=(J).maps)
    (gates:8*batchRows T≤V) (_keys:batchPins T≤V) (_children:23*((T).r+(T).s)≤V)
    (bank:Fin 2) (offset:ℕ) (offsetRoom:offset<V) :
    BatchAway X (HistoryPartyTapeRun.jobs (w:=16*u^10) X.table
      (fun i=>N (Fin.cast (congrArg₂ Nat.add hl hr) i))
      (fun i=>wire (Fin.cast (congrArg₂ Nat.add hl hr) i)) tag) (dest J true node bank.val+offset) := by
  let page:Bool→ℕ→Local:=fun side b=>⟨g+2,j.val+2,side.toNat,b⟩
  have ok (b:Fin 2) (k:Bool) : (page k b.val).Valid f.motifs f.parties:=by
    refine ⟨by dsimp [page];omega,by dsimp [page];have:=j.isLt;omega,?_,by dsimp [page];have:=b.isLt;omega⟩
    change k.toNat < 8
    cases k <;> decide
  have below:=local_window u f node age nr cap _ (ok bank true)
  change base u 12≤dest J true node bank.val ∧
    dest J true node bank.val+V≤base u 12+Diagonal.TickWorkspace.stride u ∧ _ at below
  have apart (b:Fin 2) : dest J false node b.val+V≤dest J true node bank.val ∨
      dest J true node bank.val+V≤dest J false node b.val :=
    local_apart (base:=base u 12) (n:=node) (Nat.two_pow_pos _) cap (ok b false) (ok bank true)
      (fun e=>by have eq:=congrArg Local.family e;change 0=1 at eq;omega)
  have apart0:=apart 0
  have apart1:=apart 1
  have S12:=Diagonal.TickWorkspace.apart (u:=u) (by decide:12<14)
  have S14:=Diagonal.TickWorkspace.apart (u:=u) (by decide:14<15)
  have S15:=Diagonal.TickWorkspace.apart (u:=u) (by decide:15<16)
  have S16:=Diagonal.TickWorkspace.apart (u:=u) (by decide:16<18)
  have vbig:1024≤V:=Nat.pow_le_pow_right (by decide:0<2)
    ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) u))
  have grow : V ≤ Diagonal.TickWorkspace.stride u := Nat.le_self_pow (by decide : 4≠0) V
  have word:=Diagonal.TickWorkspace.word_space (u:=u) (i:=18) (by omega:1≤u) (by omega)
  have seed:X.layout.seed=base u 14+V:=by rw [same];rfl
  have ctrl:X.ctrl.val=X.layout.seed+33:=Fin.val_cast_of_lt (by rw [seed];omega)
  have tgt:X.target=dest J false node 1:=by
    change dest X.layout X.checks (numeric X.input X.layout.cursor-1) 1=_;rw [same,side,atNode]
  refine ⟨by rw [ctrl,seed];omega,.inl (by rw [seed];omega),.inl ?_,.inl ?_,.inl ?_,?_,?_⟩
  · rw [same];change _<base u 14+2*V;omega
  · rw [same];change _<base u 15;omega
  · rw [same];change _<base u 16;omega
  · intro op member
    have span:=HistoryPartyTapeRun.job_placement T N₀ Wires tag op member
    rw [st,ma] at span
    rcases span with rows|maps
    · change dest J false node 0+V≤dest J true node bank.val ∨
        dest J true node bank.val+V≤dest J false node 0 at apart0
      omega
    · change base u 18+5*V≤op.start ∧ _ at maps
      omega
  · change dest J false node 1+V≤_ ∨ _≤dest J false node 1 at apart1
    rw [tgt];omega

/-- Literal scalar reads and address spans consumed by an elected boot/tape.
The geometry, register tuple, variable table, and dyadic extent here are all the
ones computed by the running layout. -/
structure ElectedSeed (X:HistoryPartyBatchExec.Build (16*u^10)) : Prop where
  probes : ∀ x,HistoryPartyBootExec.SeedRead X.layout X.checks (numeric X.input) x→
    (x<base u 12 ∨ base u 18≤x) ∧ x<2^W₀
  power : 2^Nat.clog 2 (HistoryPartyBootExec.extent X.layout (numeric X.input))<2^W₀
  registers : ∀ i,X.regs.words i<2^W₀
  grid : ∀ i:Fin 7,numeric X.bootImage (X.regs.grid+i.val)=X.kind.words i
  gridRoom : archiveWindow u X.regs.grid 7
  incident : archiveWindow u X.regs.incident 4
  lut : archiveWindow u (X.regs.lutBase+X.regs.lutStride*(if X.checks then X.kind.selectorPage else X.kind.tilePage)) 2
  counts : archiveWindow u (X.regs.countBase+2*numeric X.bootImage (X.regs.dyadic+1)) 2
  quota : X.table.checks=true→0<X.table.s→archiveWindow u X.table.hist X.table.s
  header : ∀ i:Fin 26,X.table.words i<2^W₀
  count : X.table.r+X.table.s=X.count

section ObservedSeed
open HistoryPartySpecialization
variable {K:Type} [CommRing K] [Fintype K] {n arity₀ height:ℕ}
  (catalogue:HistoryStaticArchive.Catalog K n arity₀) (t:Fin (height+1)) (copies₀:ℕ)

/-- Build the elected tape certificate from the genuine admission/state readback and
the sizes of its mounted finite pages. No initialized seed or interpreted header is supplied. -/
theorem elected_seed_of_reads
    (same:X.layout=J) (side:X.checks=ck) (age:16≤u) (nr:node<V^2) (motifs:g<f.motifs)
    (cap:(f.motifs+2)*(f.parties+2)*8*32≤V) (atNode:numeric X.input (J).cursor-1=node)
    (live:occupied J (numeric X.input)) (copiesAt:numeric X.input (incident J (numeric X.input)+3)=copies₀)
    (kind:∀ a:Fin 7,numeric X.input (shape J (numeric X.input)+a.val)=X.kind.words a)
    (read:Reads X.regs (numeric X.bootImage) catalogue copies₀ t)
    (gridRead:∀ a:Fin 7,numeric X.bootImage (X.regs.grid+a.val)=X.kind.words a)
    (scan:∀ x,HistoryPartyBootExec.SeedRead J ck (numeric X.input) x→
      (x<base u 12 ∨ base u 18≤x) ∧ x<2^W₀)
    (ir:archiveWindow u (incident J (numeric X.input)) 4)
    (gr:archiveWindow u (shape J (numeric X.input)) 7)
    (lut:archiveWindow u ((J).lutBase+(J).lutStride*(if ck then X.kind.selectorPage else X.kind.tilePage)) 2)
    (cnt:archiveWindow u ((J).countBase+2*t.val) 2)
    (quota:archiveWindow u (numeric X.input (incident J (numeric X.input)+1)) X.kind.letters)
    (bounds:(J).lutBase<2^W₀ ∧ (J).lutStride<2^W₀ ∧ (J).compBase<2^W₀ ∧ (J).compStride<2^W₀ ∧ (J).countBase<2^W₀)
    (comp:(J).compBase+(J).compStride*t.val<2^W₀)
    (small:copies₀≤V) (kindBounds:∀ a:Fin 7,X.kind.words a≤V)
    (size:2^t.val≤V) (work:StableCompactNativeBudget.budget t.val≤V)
    (level:t.val=Diagonal.HistogramTileNetwork.siteHeight copies₀ X.kind.digit) : ElectedSeed u X := by
  have vb : 1024 ≤ V := by
    change 2^10 ≤ 2^(u^10)
    exact Nat.pow_le_pow_right (by decide : 0 < 2)
      ((show 10 ≤ u by omega).trans (Nat.le_self_pow (by decide : 10 ≠ 0) u))
  have grow : V ≤ Diagonal.TickWorkspace.stride u := Nat.le_self_pow (by decide : 4 ≠ 0) V
  have word := Diagonal.TickWorkspace.word_space (u := u) (i := 18) (by omega) (by omega)
  have strideFits : Diagonal.TickWorkspace.stride u < 2^W₀ := by omega
  have cubic : 40 * V^3 < 2^W₀ := calc
    40 * V^3 ≤ V * V^3 := Nat.mul_le_mul_right _ (by omega)
    _ = V^4 := by ring
    _ < 2^W₀ := strideFits
  have reg := elected_registers_at u arch f node g j ck X same side age nr motifs cap atNode
    live copies₀ copiesAt kind ir gr bounds
  have regs : X.regs = registers J ck (numeric X.input) := by
    simp only [HistoryPartyBatchExec.Build.regs, same, side]
  have inc : X.regs.incident = incident J (numeric X.input) := by
    simp only [regs, registers, ite_eq_left live]
  have grid : X.regs.grid = shape J (numeric X.input) := by
    simp only [regs, registers, ite_eq_left live]
  have page : X.regs.compBase + X.regs.compStride * numeric X.bootImage (X.regs.dyadic+1) < 2^W₀ := by
    rw [read.exponent]
    simpa only [regs, registers] using comp
  have digit : numeric X.input (shape J (numeric X.input)+4) = X.kind.digit := kind 4
  have power : Nat.clog 2 (HistoryPartyBootExec.extent J (numeric X.input)) = t.val := by
    simpa only [HistoryPartyBootExec.extent, HistoryPartyBatch.copies, HistoryPartyBatch.digit, ite_eq_left live,
      copiesAt, digit, Diagonal.HistogramTileNetwork.siteHeight] using level.symm
  have seed : X.layout.seed = base u 14 + V := congrArg HistoryPartyBatch.Layout.seed same
  have s12 := Diagonal.TickWorkspace.apart (u := u) (by decide : 12 < 14)
  have s14 := Diagonal.TickWorkspace.apart (u := u) (by decide : 14 < 15)
  have s15 := Diagonal.TickWorkspace.apart (u := u) (by decide : 15 < 18)
  have seedRoom : X.layout.seed + 37 < 2^W₀ := by omega
  have origin : numeric X.bootImage (X.regs.incident+1) = numeric X.input (incident J (numeric X.input)+1) := by
    rw [inc]
    have incidentZone := ir.2
    exact congrArg Fin.val (HistoryPartyBootExec.output_outside X.layout X.checks X.input seedRoom
      (incident J (numeric X.input)+1) (by omega))
  refine ⟨by simpa only [same, side] using scan, ?_, reg.1, gridRead, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [same, power]
    exact size.trans_lt (grow.trans_lt strideFits)
  · simpa only [grid] using gr
  · simpa only [inc] using ir
  · simpa only [side, regs, registers] using lut
  · rw [read.exponent]
    simpa only [regs, registers] using cnt
  · intro active _
    change X.checks = true at active
    change archiveWindow u (numeric X.bootImage (X.regs.incident+1)) (if X.checks then X.kind.letters else X.kind.ports)
    simpa only [active, ite_true, origin] using quota
  · intro a
    refine elected_header_fits X.regs X.kind X.bootImage X.checks V (by omega) cubic
      ?_ kindBounds ?_ ?_ reg.1 page a
    · simpa only [read.copies] using small
    · simpa only [read.dyadic] using size
    · intro lane
      simpa only [read.exponent, read.counts lane] using (compactor_counts_le K t lane).trans work
  · change numeric X.bootImage (X.regs.incident+3) + (if X.checks then X.kind.letters else X.kind.ports) = X.count
    simpa only [read.copies, side] using reg.2.1.symm

end ObservedSeed

theorem elected_batch_room_at
    (same:X.layout=(rawParty (layout u arch f) g j.val).party) (side:X.checks=ck) (age:16≤u) (nr:node<V^2)
    (motifs:g<f.motifs) (cap:(f.motifs+2)*(f.parties+2)*8*32≤V)
    (atNode:numeric X.input (J).cursor-1=node) (mask:2^f.parties<2^W₀) (seed:ElectedSeed u X)
    (gates:8*batchRows T≤V) (keys:batchPins T≤V) (children:23*((T).r+(T).s)≤V)
    (lut : arch.lut+HistoryStaticArchive.size z ar<2^W₀ ∧
      (arch.lut+HistoryStaticArchive.size z ar≤base u 12 ∨ base u 18+6*V≤arch.lut))
    (compact : arch.pages+StableCompactROMNative.size d<2^W₀ ∧
      (arch.pages+StableCompactROMNative.size d≤base u 12 ∨ base u 18+6*V≤arch.pages))
    (archive:HistoryPartyTapeRun.Archive (D:=d) tag lib arch.lut arch.pages X.input)
    (budget:StableCompactNativeBudget.budget pow<2^W₀) (shape:HistoryPartyTapeRun.Shape (p:=p) (h:=H) T N₀)
    (width:∀ i,2+arity (ix i)+(N (ix i)).internal<2^W₀)
    (ids:∀ k,tag k<2^W₀) (bank:(T).e*(T).d<2^W₀) (stripe:(T).r*(T).d<2^W₀) :
    BatchRoom X arity N wire tag lib pow arch.lut arch.pages hl hr := by
  have st:(T).stream=dest J ck node 0:=by
    change dest X.layout X.checks (numeric X.input X.layout.cursor-1) 0=_;rw [same,side,atNode]
  have ma:(T).maps=(J).maps:=by change X.layout.maps=_;rw [same]
  have args:(T).args=(J).arguments:=by change X.layout.arguments=_;rw [same]
  have ready:=physical_batch_source_at u arch f node g j ck T N₀ Wires tag X same side rfl age nr
    motifs cap atNode mask (by simpa only [←same,←side] using seed.probes)
    (by simpa only [←same] using seed.power) seed.registers seed.grid seed.gridRoom seed.incident
    (by simpa only [←side] using seed.lut) seed.counts seed.quota seed.header seed.count st ma gates keys children
  exact physical_batch_room u arch f node g j ck X arity N wire tag lib pow hl hr same side age nr motifs cap
    atNode seed.count ready st ma args gates keys children lut.1.le compact.1.le lut.2 compact.2 archive budget shape
    (fun i=>(width i).le) ids (fun i=>by have:=width i;omega) bank stripe

omit [CommRing F] [Fintype F] in
theorem child_width_from_batch
    (sizes : Diagonal.HistoryContraction.Tree.BatchRows.Sizes N (T).left (T).right)
    (room:2+batchPins T+(Tree.batch N wire).bits<2^W₀) :
    ∀ i,2+arity (Fin.cast (congrArg₂ Nat.add hl hr) i)+
      (N (Fin.cast (congrArg₂ Nat.add hl hr) i)).internal<2^(16*u^10) := by
  have val:=sum_blocks arity (T).left.arity (T).right.arity sizes.arities
  have total:(∑ i,arity i)=batchPins T:=by simpa [batchPins,hl,hr] using val
  have total' (i:Fin (r+s)) : arity i≤batchPins T:=by
    rw [←total]
    exact Finset.single_le_sum (f:=arity) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  have hidden (i:Fin (r+s)) : (N i).internal≤(Tree.batch N wire).bits:=by
    change _≤H+∑ j,(N j).internal
    exact (Finset.single_le_sum (f:=fun j=>(N j).internal) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans (Nat.le_add_left ..)
  intro i;have:=total' (ix i);have:=hidden (ix i);omega

end BatchPlacement


section SingleElectedPlacement
open HistoryPartyTapeRun
variable (j : Fin f.parties) (ck : Bool) (T : HistoryBatchTape.Header) {h z ar d : ℕ}
  {arity : Fin (T.r+T.s)→ℕ} (nets : (i:Fin (T.r+T.s))→BitNetwork F (arity i))
  (wire : ∀ i,Fin (arity i)→BitSource h p) (tag : ((Fin 3→Bool)→F)→ℕ)
local notation "J" => (rawArm A j.val).party

omit [CommRing F] in
theorem physical_batch_windows [Fintype F] (age : 16≤u) (count : node<V^2) (motifs : 0<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V)
    (stream : T.stream=dest J ck node 0) (maps : T.maps=(J).maps) (args : T.args=(J).arguments)
    (rows : 8*batchRows T≤V) (pins : batchPins T≤V) (children : 23*(T.r+T.s)≤V)
    (lut : arch.lut+HistoryStaticArchive.size z ar≤2^W₀) (compact : arch.pages+StableCompactROMNative.size d≤2^W₀)
    (lutArea : arch.lut+HistoryStaticArchive.size z ar≤base u 12 ∨ base u 18+6*V≤arch.lut)
    (compArea : arch.pages+StableCompactROMNative.size d≤base u 12 ∨ base u 18+6*V≤arch.pages) :
    HistoryPartyTapeRun.Space (z:=z) (B:=ar) (D:=d) T nets wire tag arch.lut arch.pages
      (((J).seed+33:ℕ):Word W₀) (J).commands :=
  physical_batch_windows_at u arch f node 0 j ck T nets wire tag age count motifs capacity stream maps args rows pins children lut compact lutArea compArea

omit [CommRing F] in
theorem physical_batch_source [Fintype F] (X : HistoryPartyBatchExec.Build W₀)
    (context : X.layout=J) (side : X.checks=ck) (table : X.table=T)
    (age : 16≤u) (count : node<V^2) (motifs : 0<f.motifs) (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V)
    (cursor : numeric X.input (J).cursor-1=node) (mask : 2^f.parties<2^W₀)
    (probes : ∀ x,HistoryPartyBootExec.SeedRead J ck (numeric X.input) x→
      (x<base u 12 ∨ base u 18≤x) ∧ x<2^W₀)
    (power : 2^Nat.clog 2 (HistoryPartyBootExec.extent J (numeric X.input))<2^W₀)
    (registers : ∀ j,X.regs.words j<2^W₀) (grid : ∀ j:Fin 7,numeric X.bootImage (X.regs.grid+j.val)=X.kind.words j)
    (gridRoom : archiveWindow u X.regs.grid 7) (incidentRoom : archiveWindow u X.regs.incident 4)
    (lutRoom : archiveWindow u (X.regs.lutBase+X.regs.lutStride*(if ck then X.kind.selectorPage else X.kind.tilePage)) 2)
    (countRoom : archiveWindow u (X.regs.countBase+2*numeric X.bootImage (X.regs.dyadic+1)) 2)
    (quota : T.checks=true→0<T.s→archiveWindow u T.hist T.s)
    (header : ∀ t:Fin 26,T.words t<2^W₀) (length : T.r+T.s=X.count)
    (stream : T.stream=dest J ck node 0) (maps : T.maps=(J).maps)
    (rows : 8*batchRows T≤V) (pins : batchPins T≤V) (nwords : 23*(T.r+T.s)≤V) :
    X.Source (jobs T nets wire tag) ∧
      (X.table.checks=true→0<X.table.s→X.table.hist+X.table.s≤X.layout.batch ∨
        X.layout.commands+21*X.count≤X.table.hist) :=
  physical_batch_source_at u arch f node 0 j ck T nets wire tag X context side table age count motifs capacity cursor mask probes power registers grid gridRoom incidentRoom lutRoom countRoom quota header length stream maps rows pins nwords

end SingleElectedPlacement

end PhysicalOrder


end
end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
