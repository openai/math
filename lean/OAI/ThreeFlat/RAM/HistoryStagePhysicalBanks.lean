import OAI.ThreeFlat.RAM.HistoryStageBankArena

namespace OAI
/-! # Publication of the actual selected stage into its S13 cache row -/

namespace ThreeFlat.RAM.HistoryStageBankArena

set_option quotPrecheck false

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickWorkspace HistoryStageRoot HistoryStageBody
open HistoryStageSetup HistoryStageResult HistoryStageSnapshots HistoryPartyBatchExec
open HistoryBoundedBody HistoryReadyTape HistoryStageBody.Physical
open scoped BigOperators Fin.CommRing
noncomputable section
variable {W : ℕ} (u idx : ℕ) (archive : Archive) (family : Family) (m : Memory W)
local notation "A" => Physical.layout u archive family
local notation "cap" => family.childBound
local notation "T" => numInput A cap (numeric m)
local notation "X" => HistoryStageSetup.run A cap m
local notation "B" => (X).compiled
local notation "Y" => HistoryStageRoot.childCount T (numeric m)
local notation "S" => Diagonal.TickWorkspace.stride u
local notation "V" => volume u
variable {F : Type*} {n p h : ℕ} {ar : Fin n→ℕ} (N : ∀ k,BitNetwork F (ar k))
    (wire : ∀ k,Fin (ar k)→BitSource h p) (id : ((Fin 3→Bool)→F)→ℕ)
    (q : Fin n→HistoryJoinScan.Header ℕ)
local notation "ops" => Tape.tape N wire id q

private theorem late_boot {x : ℕ} (cell : BootCell A cap m x) (secure : (B).protectedAt N q x) :
    LateWrites X ops x := by
  refine ⟨cell.counter,endpoints_outside X x cell.endpoints,cell.seed,cell.commands,cell.arguments,secure.1,?_⟩
  intro job member
  obtain ⟨k,_,hk⟩:=List.mem_flatMap.mp member
  rcases (by simpa only [Tape.jobs,List.mem_cons,List.not_mem_nil,or_false] using hk :
    job=⟨(q k).pins,ar k,_⟩ ∨ job=⟨(q k).dest,4*(N k).cells,_⟩) with rfl|rfl
  · exact (secure.2 k).1
  · exact (secure.2 k).2

set_option maxRecDepth 18000 in
/-- The join and cache writes finish below protected navigation words, including
those in an archive above the workspace. -/
theorem Ranges.resultSpace_above (r : Ranges u idx archive family m N q)
    (earlier : ∀ k,k<Y→numeric m (numeric m (HistoryStageRoot.node T+3)+k)<(T).id)
    (listCells : ∀ k,k<Y→base u 20≤numeric m (HistoryStageRoot.node T+3)+k)
    (incident : ∀ j : Fin 2, base u 20≤numeric m (HistoryStageRoot.node T+6)+j.val)
    (last : 0<numeric m (numeric m (HistoryStageRoot.node T+6))→∀ j,2≤j→j≤3→
      base u 20≤HistoryStageBounds.lastIncident T (numeric m)+j) : ResultSpace A cap m ops := by
  let cache:=(T).resultBase+8*(T).id
  have cacheEq : cache=base u 13+8*idx:=by change base u 13+8*(T).id=_;rw [r.join.index]
  have limit : 20*S<2^W:=r.join.words
  have room : V+400+32*(cap+1)≤S:=r.join.scratch
  have cnt : Y≤cap:=r.join.childCount
  have arena : base u 12+(idx+1)*V^2≤14*S:=r.join.arena
  have cEnd : cache+8≤15*S:=by rw [cacheEq];exact r.join.cache
  have starts : base u 12+idx*V^2≤base u 12+(idx+1)*V^2 := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  have extLimit : (T).ext+V≤14*S:=r.extEnd
  have ctlBound : loc A 22<2^W:=by change 15*S+V+64+22<_;omega
  have bControl : (B).control.val=15*S+V+7:=r.scalar.cursor
  let safe (x : ℕ) := HistoryStageResult.apart cache 6 x ∧ LateWrites X ops x
  have exterior (x : ℕ) (outside : OutsideNode u idx x) : safe x := by
    refine ⟨?_,join_late_writes u idx archive family m N wire id q r.join outside⟩
    change x<cache ∨ cache+6≤x
    rw [cacheEq];rcases outside.cache with t|t <;> omega
  have nav (x : ℕ) (lower : 20*S≤x) : safe x := by
    apply exterior
    exact ⟨.inr (by omega),.inr (by rw [←cacheEq];omega),.inr (.inl (by change 20*S≤x;omega))⟩
  have cursor : safe (A).nodePorts.cursor := by
    apply exterior
    change OutsideNode u idx (19*S)
    exact ⟨.inr (by omega),.inr (by rw [←cacheEq];omega),.inr (.inr (.inl rfl))⟩
  have core (j : Fin 6) : safe ((T).kernel+j.val) := by
    let x:=(T).kernel+j.val
    let zero : Fin (Y+1):=⟨0,by omega⟩
    have low : (T).kernel+6≤cache := by rw [cacheEq];exact r.rootBelow zero
    have separate : (T).kernel+6≤(T).stream ∨ (T).ext+V≤(T).kernel:=r.rootSep zero
    have small:=j.isLt
    have prior : x<cache:=by dsimp [x];omega
    have under : x<base u 14 := by change x<15*S;omega
    have split : x<(T).stream ∨ (T).ext+V≤x := by rcases separate with h|h <;> dsimp [x] <;> omega
    have cell:=r.lowCell under split
    have tape : (B).protectedAt N q x := by
      refine ⟨by change x<15*S at under;omega,fun k=>⟨?_,?_⟩⟩
      · left;have p:=(r.join.pins k).1;change 19*S+2≤_ at p;change x<15*S at under;omega
      · have mask:=r.dest k
        rcases split with l|l
        · exact .inl (l.trans_le mask.1)
        · exact .inr (mask.2.trans ((Nat.le_add_right ..).trans l))
    exact ⟨Or.inl prior,late_boot u archive family m N wire id q cell tape⟩
  have controls (j : ℕ) (alive : j≤11 ∨ j=24 ∨ j=25) : safe (args A+j) := by
    let x:=args A+j
    have loc : x=15*S+V+64+j:=by change 15*S+V+64+0+j=_;omega
    have upper : x<16*S:=by omega
    have lower : 15*S+V+9≤x:=by omega
    have cell : BootCell A cap m x := by
      refine ⟨?_,.inr ?_,.inr ?_,.inl ?_,.inl ?_⟩
      · rw [Fin.val_cast_of_lt ctlBound];change x≠15*S+V+64+22;omega
      · exact r.endpoints.trans (extLimit.trans (by omega))
      · exact lower
      · exact upper
      · change x<17*S;omega
    have tape : (B).protectedAt N q x := by
      refine ⟨by omega,fun k=>⟨.inl ?_,.inr ?_⟩⟩
      · have bound:=(r.join.pins k).1;change 19*S+2≤_ at bound;omega
      · have bound:=(r.dest k).2;omega
    exact ⟨.inr (by omega),late_boot u archive family m N wire id q cell tape⟩
  have old (k : ℕ) (hk : k<Y) (j : Fin 6) : safe (childPtr T (numeric m) k+j.val) := by
    let x:=childPtr T (numeric m) k+j.val
    have prec:=earlier k hk
    have small:=j.isLt
    have loc : x=14*S+8*numeric m (numeric m (HistoryStageRoot.node T+3)+k)+j.val:=rfl
    have high : x<cache := by rw [cacheEq];change x<14*S+8*idx;rw [r.join.index] at prec;omega
    apply exterior
    refine ⟨.inr (by omega),.inl (by rw [←cacheEq];exact high),.inl (by change x<15*S;omega)⟩
  have node (j : Fin 8) : safe (HistoryStageRoot.node T+j.val) := by
    apply nav
    change 20*S≤45*S+8*(T).id+j.val;omega
  have proof (x : ℕ) (read : SourceAt A T (numeric m) x) : safe x := by
    cases read with
    | control j h => exact controls j h
    | cursor => exact cursor
    | node j => exact node j
    | child k h => exact nav _ (le_trans (by change 20*S≤21*S;omega) (listCells k h))
    | kernel j=>exact core j
    | old k h j=>exact old k h j
    | incident j=>exact nav _ (le_trans (by change 20*S≤21*S;omega) (incident j))
    | last h j l hi=>exact nav _ (le_trans (by change 20*S≤21*S;omega) (last h j l hi))
  have ptrLow : (T).ext+V≤HistoryStageBody.hub A+6 := extLimit.trans (by change 14*S≤15*S+V+64+48+6;omega)
  refine ⟨?_,earlier,fun j h=>(controls j h).1,cursor.1,fun j=>(node j).1,fun i h=>(proof _ (.child i h)).1,
    fun j=>(core j).1,fun j=>(proof _ (.incident j)).1,fun h j l hi=>(proof _ (.last h j l hi)).1,?_,?_,fun x a=>(proof x a).2⟩
  · change cache+6<2^W;rw [cacheEq];exact r.scalar.cacheRoom
  · rw [Fin.val_cast_of_lt ctlBound];change 15*S+V+64+48+6≠15*S+V+64+22;omega
  · exact endpoints_outside X _ (.inr (r.endpoints.trans ptrLow))


set_option maxRecDepth 18000 in
/-- Only true S44 list members, actual incident fields and the earlier child IDs are
needed beyond the fixed sector bounds of the selected compiled stage. -/
theorem Ranges.resultSpace (r : Ranges u idx archive family m N q)
    (earlier : ∀ k,k<Y→numeric m (numeric m (HistoryStageRoot.node T+3)+k)<(T).id)
    (listCells : ∀ k,k<Y→NavigationCell u (numeric m (HistoryStageRoot.node T+3)+k))
    (incident : ∀ j : Fin 2, NavigationCell u (numeric m (HistoryStageRoot.node T+6)+j.val))
    (last : 0<numeric m (numeric m (HistoryStageRoot.node T+6))→∀ j,2≤j→j≤3→
      NavigationCell u (HistoryStageBounds.lastIncident T (numeric m)+j)) : ResultSpace A cap m ops :=
  Ranges.resultSpace_above u idx archive family m N wire id q r earlier
    (fun k hk=>(listCells k hk).1) (fun j=>(incident j).1) (fun h j l r=>(last h j l r).1)


end
end ThreeFlat.RAM.HistoryStageBankArena

end OAI
