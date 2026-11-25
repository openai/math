import OAI.ThreeFlat.RAM.HistoryShrinkArms

namespace OAI
set_option quotPrecheck false
set_option maxErrors 600

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open private out from OAI.ThreeFlat.RAM.HistoryShrinkGroups
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr
open Diagonal.TickWorkspace HistoryStageBody.Physical HistoryMotifJoin HistoryScratch
open HistoryBoundedBody HistoryBoundedJoin HistoryJoinScan Diagonal.HistoryContraction BitNetwork.Ordered
open scoped BigOperators Classical Fin.CommRing

noncomputable section
variable {W n h p u node : ℕ} {F : Type} {arity : Fin n → ℕ} {A : HistoryGatherBody.Layout}

/-- The addresses of the shrink emitter are unchanged when mounting a party or a motif. -/
structure PhysicalBanks (u : ℕ) (A : HistoryGatherBody.Layout) : Prop where
  arena : A.party.arena=base u 12
  wordCount : A.party.V=volume u
  seed : A.party.seed=base u 14+volume u
  batch : A.party.batch=base u 14+2*volume u
  gather : A.temp=base u 17
  commands : A.party.commands=base u 15
  arguments : A.party.arguments=base u 16
  privateStarts : A.privateStarts=base u 18+4*volume u
  childStarts : A.nodePorts.starts=base u 18+3*volume u

theorem PhysicalBanks.layout (u : ℕ) (arch : Archive) (f : Family) :
    PhysicalBanks u (HistoryStageBody.Physical.layout u arch f) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem PhysicalBanks.withMotif (b : PhysicalBanks u A) (j : ℕ) :
    PhysicalBanks u (HistoryMotifJoin.withMotif A j) :=
  ⟨b.arena,b.wordCount,b.seed,b.batch,b.gather,b.commands,b.arguments,b.privateStarts,b.childStarts⟩

/-- On the S12/S14/S15/S16 physical layout both local join modes satisfy their
entire cache and controller charts from the tree dimensions and actual port/mask reads. -/
theorem Chart.of_layout (b : PhysicalBanks u A) (age : 16≤u) (g : Bool)
    (m : Memory (16*u^10)) (N : ∀ i,BitNetwork F (arity i))
    (wire : ∀ i,Fin (arity i)→BitSource h p) (id : ((Fin 3→Bool)→F)→ℕ)
    (smallNode : node<(volume u)^2)
    (static : (A.party.motifs+2)*(A.party.parties+2)*8*32≤volume u)
    (motif : g=true→A.party.motif<A.party.motifs)
    (cap : n≤ if g then A.party.parties else A.party.motifs)
    (arities : ∀ i,arity i≤volume u) (gates : 4*(∑ i,(N i).cells)≤volume u)
    (dim : p<2^(16*u^10) ∧ h<2^(16*u^10) ∧ ∀ i,(N i).internal<2^(16*u^10))
    (tag : ∀ i r j,HistoryCompiledRows.metadata id (N i) r j<2^(16*u^10))
    (safe : HistoryPartyBatchExec.Protected (joinHeader A (16*u^10) g) m
      (A.party.seed+64) (HistoryMotifJoin.rows A (16*u^10) g).length)
    (cursor : (HistoryNodePorts.id A.nodePorts).value (fun _=>0) m (fun _=>0)=(node:Word (16*u^10)))
    (ports : let R:=HistoryGatherBody.selected A m; R.oldBits+R.newBits=(p:Word (16*u^10)))
    (free : g=true→m (((A.privateStarts+8:ℕ):Word (16*u^10)).val)=(h:Word (16*u^10)))
    (active : g=true→n=Fintype.card {j : Fin A.party.parties // selectedBit A m j.val})
    (dense : g=false→HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).kernel 3=(n:Word (16*u^10)))
    (mask : 2^A.party.parties<2^(16*u^10)) : Chart A g node m N wire id := by
  let V:=volume u
  have ex : 10≤u^10:=(by omega : 10≤u).trans (Nat.le_self_pow (by decide) _)
  have big : 1024≤V:=Nat.pow_le_pow_right (by decide : 0<2) ex
  let k:=if g then A.party.parties else A.party.motifs
  have scale : k≤V:=by
    have aa:=Nat.le_mul_of_pos_left (A.party.parties+2) (show 0<A.party.motifs+2 by omega)
    have bb:=Nat.le_mul_of_pos_right (A.party.motifs+2) (show 0<A.party.parties+2 by omega)
    dsimp [k];split <;> omega
  have pp : 32*V≤ stride u := calc
    32*V ≤ V*V := Nat.mul_le_mul_right _ (by omega)
    _=V^2 := (pow_two V).symm
    _≤V^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have ca:=apart (u:=u) (by decide : 12<14)
  have hd:=apart (u:=u) (by decide : 14<15)
  have cm:=apart (u:=u) (by decide : 15<16)
  have hi:=word_space (i:=16) (by omega : 1≤u) (by omega : 16<stride u)
  have bounds₀ : A.party.arena+A.party.V^4≤A.party.seed:=by
    rw [b.arena,b.wordCount,b.seed];exact ca.trans (by omega)
  have bounds₁ : A.party.seed+64+7+7*k+4≤A.party.commands:=by rw [b.seed,b.commands];omega
  have bounds₂ : A.party.commands+14*n≤A.party.arguments:=by rw [b.commands,b.arguments];omega
  have bounds₃ : A.party.arguments+7*n<2^(16*u^10):=by rw [b.arguments];omega
  have ctl : (build A g node m (h:=h) (p:=p) (n:=n)).control.val=A.party.seed+7:=by
    apply Fin.val_cast_of_lt
    change A.party.seed+7<2^(16*u^10)
    rw [b.seed]
    omega
  have C : Capacity A g node m N id (h:=h) (p:=p) := by
    refine ⟨by simpa only [b.wordCount] using smallNode,by simpa only [b.wordCount] using static,
      motif,?_,?_,by simpa only [b.wordCount] using arities,by simpa only [b.wordCount] using gates,
      by rw [ctl];omega,?_,tag⟩
    · intro gg;simpa [gg] using cap
    · intro i gg
      have live : i.val<Fintype.card {j : Fin A.party.parties // selectedBit A m j.val}:=i.isLt.trans_eq (active gg)
      unfold role
      dsimp only
      rw [dite_eq_left live]
      exact (Diagonal.HistoryMaskOrder.order (fun j : Fin A.party.parties => selectedBit A m j.val) ⟨i.val,live⟩).val.isLt
    · rw [ctl,b.wordCount,b.seed]
      omega
  exact of_windows A g node m N wire id C (by rw [b.wordCount];omega)
    bounds₀ ctl cap bounds₁ bounds₂ bounds₃ dim safe cursor ports free active dense mask

private theorem sector_window (b : PhysicalBanks u A)
    {s : Local} (fit : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V)
    (valid : s.Valid A.party.motifs A.party.parties) :
    let addr := atWord A.party.arena A.party.V A.party.motifs A.party.parties node s 0
    base u 12+node*(volume u)^2≤addr ∧ addr+A.party.V≤base u 12+(node+1)*(volume u)^2 := by
  simp only [atWord,Nat.add_zero,b.arena,b.wordCount]
  have lt := (sector_lt valid).trans_le fit
  rw [b.wordCount] at lt
  let V:=volume u
  let sidx:=HistoryScratch.sector A.party.motifs A.party.parties s
  have start : node*V≤node*V+sidx := Nat.le_add_right _ _
  have stop : node*V+sidx+1≤node*V+V := by dsimp [V,sidx];omega
  have a:=Nat.mul_le_mul_right V start
  have z:=Nat.mul_le_mul_right V stop
  change base u 12+node*V^2≤base u 12+(node*V+sidx)*V ∧
    base u 12+(node*V+sidx)*V+V≤base u 12+(node+1)*V^2
  rw [Nat.add_one_mul] at z
  constructor
  · calc
      _=base u 12+(node*V)*V := by ring
      _≤_ := Nat.add_le_add_left a _
  · calc
      _=base u 12+((node*V+sidx)*V+V) := by omega
      _≤base u 12+(node*V+V)*V := Nat.add_le_add_left z _
      _=_ := by ring

private theorem large_stride {V : ℕ} (big : 16≤V) : 10*V≤V^4 := by
  calc
    _ ≤ V*V := Nat.mul_le_mul_right _ (by omega)
    _ = V^2 := (pow_two V).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

variable (A) (group : Bool) (node : ℕ) (m : Memory W)
  (N : ∀ i, BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
  (id : ((Fin 3→Bool)→F)→ℕ)

/-- The tape's actual map and copy jobs stay inside one S12 node. Only S14--S16
carry the generated scalar tables, and the four published words return to S12. -/
theorem finish_away (banks : PhysicalBanks u A)
    (C : Chart A group node m N wire id) (x : ℕ)
    (scratch : x<base u 14 ∨ base u 18≤x)
    (roots : ∀ j : Fin 4,x< resultBank A node group j.val ∨ resultBank A node group j.val+A.party.V≤x)
    (pins : ∀ i : Fin n,x<sector A group node m i 3 ∨ sector A group node m i 3+A.party.V≤x) :
    finish A group node m N wire id x=m x := by
  let B:=build A group node m (p:=p) (h:=h) (n:=n)
  let q:=copy A group node m N (p:=p) (h:=h)
  let cap:=if group then A.party.parties else A.party.motifs
  let V:=volume u
  have fit:=C.capacity.sectors
  have both : 14*A.party.parties+14*A.party.motifs+128≤A.party.V := by
    nlinarith only [fit,Nat.zero_le (A.party.parties*A.party.motifs)]
  have charge : 14*cap+128≤V := by
    rw [banks.wordCount] at both
    cases group <;> dsimp [cap,V] <;> omega
  have size : n≤cap:=C.size
  have big : 16≤V:=by omega
  have width : 10*V≤ stride u:=large_stride big
  have past:=apart (u:=u) (by decide : 14<15)
  have past':=apart (u:=u) (by decide : 15<16)
  have before:=apart (u:=u) (by decide : 16<18)
  have edge:=apart (u:=u) (by decide : 18<19)
  have away (lo hi : ℕ) (start : base u 14≤lo) (stop : hi≤base u 18) :
      x<lo ∨ hi≤x := by omega
  have aseed:=away (A.party.seed) (A.party.seed+9) (by rw [banks.seed];omega)
    (by rw [banks.seed];change base u 14+V+9≤_;omega)
  have prep : HistoryRefreshEmitter.PrepAway B x := by
    refine ⟨aseed,?_,?_⟩
    · change x<A.party.commands ∨ A.party.commands+14*n≤x
      rw [banks.commands]
      exact away _ _ (by omega) (by omega)
    · change x<A.party.arguments ∨ A.party.arguments+7*n≤x
      rw [banks.arguments]
      exact away _ _ (by omega) (by omega)
  have hub:=away (A.party.seed+64) (A.party.seed+64+(HistoryMotifJoin.rows A W group).length)
    (by rw [banks.seed];omega) (by
      rw [banks.seed,rows_len]
      change base u 14+V+64+(7+7*cap)≤base u 18
      omega)
  have init : B.input x=m x := by
    have out : ¬(A.party.seed+64≤x ∧ x<A.party.seed+64+(HistoryMotifJoin.rows A W group).length) := by omega
    change headerImage _ (A.party.seed+64) (HistoryMotifJoin.rows A W group).length m x=_
    simp [headerImage,fillSegment,out]
  have safe : B.protectedAt N q x := by
    constructor
    · have room : A.party.seed+7<2^W := by
        have bound:=C.source.seed
        change A.party.seed+9<2^W at bound
        omega
      change x≠((A.party.seed+7:ℕ):Word W).val
      rw [Fin.val_cast_of_lt room]
      omega
    · intro i
      have small:=C.capacity.demand i
      have cells:=C.capacity.cells
      have offset:=Tree.prefix_next_le (fun j=>(N j).cells) i
      have old:=pins i
      have root:=roots 0
      change x< resultBank A node group 0 ∨ resultBank A node group 0+A.party.V≤x at root
      constructor
      · change x<sector A group node m i 3 ∨ sector A group node m i 3+arity i≤x
        omega
      · change x< resultBank A node group 0+4*Tree.before (fun j=>(N j).cells) i ∨
          resultBank A node group 0+4*Tree.before (fun j=>(N j).cells) i+4*(N i).cells≤x
        omega
  let G:=GroupRead.of_values A group m node p h n C.cursor C.ports C.free C.active C.dense C.size
    C.maskRoom (by have:=C.source.wide;omega) C.infoRoom
  have addr : B.outputBase=resultBank A node group 1 := by
    have val: B.input (B.layout.hub+6)=(resultBank A node group 1:Word W):=
      (GroupRead.group_image A G C.layout.hubRoom).2.1
    change (B.input (B.layout.hub+6)).val=_
    have room : resultBank A node group 1+4<2^W := C.source.result
    rw [val,Fin.val_cast_of_lt (show resultBank A node group 1<2^W by omega)]
  have res:=roots 1
  change x< resultBank A node group 1 ∨ resultBank A node group 1+A.party.V≤x at res
  have four : 4≤A.party.V:=by omega
  have notResult : ¬(B.outputBase≤x ∧ x<B.outputBase+4) := by rw [addr];omega
  change fillSegment B.outputBase 4 _ (B.reached (Tape.tape N wire id q)) x=m x
  simp only [fillSegment,ite_eq_right notResult]
  exact (B.prefix_keeps N wire id q (List.finRange n) safe).trans ((prep.keeps).2.2.trans init)

theorem finish_outsideNode (banks : PhysicalBanks u A)
    (C : Chart A group node m N wire id) (x : ℕ) (outside : OutsideNode u node x) :
    finish A group node m N wire id x=m x := by
  have above:=apart (u:=u) (by decide : 18<19)
  apply finish_away A group node m N wire id banks C x (by have:=outside.scratch;omega)
  · intro j
    change x<out A group node j.val ∨ out A group node j.val+A.party.V≤x
    rw [rootLoc A group node j.val]
    have z:=sector_window (node:=node) banks C.capacity.sectors (parentLocal_valid A group node m N id C.capacity j)
    exact outside.arena_range z.1 z.2
  · intro i
    rw [childLoc A group node m i 3]
    have z:=sector_window (node:=node) banks C.capacity.sectors (childLocal_valid A group node m N id C.capacity i 3)
    exact outside.arena_range z.1 z.2

end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr Diagonal.TickWorkspace
open HistoryStageBody.Physical HistoryScratch HistoryRefreshEmitter HistoryMotifJoin
open HistoryPartyBatch HistoryPartyBatchExec HistoryGatherBody HistoryBoundedBody
open Diagonal.HistoryContraction BitNetwork.Ordered
open scoped BigOperators Fin.CommRing

noncomputable section
variable {u node W p : ℕ} {F : Type} {A : HistoryGatherBody.Layout}

theorem PhysicalBanks.withParty (b : PhysicalBanks u A) (j : ℕ) :
    PhysicalBanks u (HistoryMotifJoin.withParty A j) :=
  ⟨b.arena,b.wordCount,b.seed,b.batch,b.gather,b.commands,b.arguments,b.privateStarts,b.childStarts⟩

/-- Zero-child batches still write their two headers, three roots and control words.
All these writes are confined even for a motif containing several elected raw parties. -/
theorem vacant_away (banks : PhysicalBanks u A) (id : ((Fin 3→Bool)→F)→ℕ)
    (input : Memory W) (chart : VacantRoom A node id input)
    (capacity : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V)
    (_motif : A.party.motif<A.party.motifs) (_party : A.party.party<A.party.parties)
    (x : ℕ) (away : HistoryRefreshEmitter.PartyAway u A.party node x) : vacantPass A node id input x=input x := by
  let X:=vacantChecks A.party input
  let Y:=vacantPayload A.party input
  let B:=HistoryPartyPairExec.build A.party node 0 0 (Y.published [])
  let loc (k : ℕ) : Local:=⟨A.party.motif+2,A.party.party+2,k,1⟩
  let page (k : ℕ):=atWord A.party.arena A.party.V A.party.motifs A.party.parties node (loc k) 0
  let V:=volume u
  have big : 128≤V:=by rw [banks.wordCount] at capacity;nlinarith only [capacity,Nat.zero_le (A.party.motifs*A.party.parties)]
  have width : 10 * V ≤ Diagonal.TickWorkspace.stride u :=
    large_stride (V := V) ((by decide : 16 ≤ 128).trans big)
  have s14:=apart (u:=u) (by decide : 14<15)
  have s15:=apart (u:=u) (by decide : 15<16)
  have s16:=apart (u:=u) (by decide : 16<17)
  have s17:=apart (u:=u) (by decide : 17<18)
  have s18:=apart (u:=u) (by decide : 18<19)
  have side (lo hi : ℕ) (start : base u 14≤lo) (stop : hi≤base u 18) : x<lo ∨ hi≤x :=
    by have:=away.scratch;omega
  have first:=side A.party.seed (A.party.seed+37) (by rw [banks.seed];omega)
    (by rw [banks.seed];change base u 14+V+37≤_;omega)
  have second:=side A.party.batch (A.party.batch+26) (by rw [banks.batch];omega)
    (by rw [banks.batch];change base u 14+2*V+26≤_;omega)
  have size : A.party.seed+37<2^W:=chart.checks.seedRoom
  have pages (k : ℕ) (limit : k<8) : x<page k ∨ page k+4≤x := by
    exact away.page k 1 limit (by decide) 4 (by change 4≤V;omega)
  have xloc : X.target=page 1 :=
    congrArg (fun cursor => dest A.party true cursor 1) chart.before
  have yloc : Y.target=page 0 :=
    congrArg (fun cursor => dest A.party false cursor 1) chart.between
  have bloc : B.outputBase = page 2 := by
    let m := Y.published []
    have row : HistoryPartyPair.word A.party (numeric m) 6 = HistoryPartyPair.atPair A.party node 1 := by
      change HistoryPartyPair.atPair A.party (numeric m A.party.cursor-1) 1 = _
      rw [chart.pair.cursor]
    have cap : HistoryPartyPair.atPair A.party node 1 < 2^W := chart.pair.cap 6
    change (HistoryPartyPairExec.prepared A.party m (HistoryPartyPair.hub A.party+6)).val =
      HistoryPartyPair.atPair A.party node 1
    have saved : HistoryPartyPairExec.prepared A.party m (HistoryPartyPair.hub A.party+6) =
        (HistoryPartyPair.word A.party (numeric m) 6 : Word W) := HistoryPartyPairExec.hub_read A.party m 6
    rw [saved, row, Fin.val_cast_of_lt cap]
  have batchFrame (Z : HistoryPartyBatchExec.Build W) (same : Z.layout=A.party)
      (off : ¬occupied A.party (numeric Z.input)) (target : x<Z.target ∨ Z.target+4≤x) :
      BatchAway Z [] x := by
    have count : Z.count=0:=by simp [HistoryPartyBatchExec.Build.count,same,children,copies,kinds,off]
    refine ⟨?_,by simpa [same] using first,by simpa [same] using second,?_,?_,by simp,target⟩
    · change x≠((Z.layout.seed+33:ℕ):Word W).val
      rw [same,Fin.val_cast_of_lt (by omega)]
      omega
    · rw [count];omega
    · rw [count];omega
  have pair : HistoryPartyPairExec.Retained A.party node (nullTree F) (nullTree F) id (Y.published []) x := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · omega
    · rw [banks.commands]
      exact side _ _ (by omega) (by omega)
    · rw [banks.arguments]
      exact side _ _ (by omega) (by omega)
    · change x≠((A.party.seed+7:ℕ):Word W).val
      rw [Fin.val_cast_of_lt (by omega)]
      omega
    · intro job member
      have zero : job.count = 0 := by
        have both : List.finRange 2 = [0,1] := by decide
        simp only [HistoryPartyPairExec.steps, Tape.tape, both, List.flatMap_cons, List.flatMap_nil,
          Tape.jobs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl
        · rfl
        · change 4 * (nullTree F).compile.cells = 0
          rw [Tree.compiled_rows, null_rows, Nat.mul_zero]
        · rfl
        · change 4 * (nullTree F).compile.cells = 0
          rw [Tree.compiled_rows, null_rows, Nat.mul_zero]
      change x<job.start ∨ job.start+job.count≤x
      omega
  have gather : x < A.temp ∨ A.temp+(HistoryGatherBody.fields (W:=W) A).length ≤ x := by
    rw [HistoryGatherExecution.header_size,banks.gather]
    have header:=chart.headerBound
    rw [banks.wordCount] at header
    apply side <;> omega
  have header : x < HistoryPartyPair.hub A.party ∨ HistoryPartyPair.hub A.party+25 ≤ x := by
    change x<A.party.seed+64 ∨ A.party.seed+64+25≤x
    rw [banks.seed]
    exact side _ _ (by omega) (by change base u 14+V+64+25≤_;omega)
  have checked : X.published [] x = input x :=
    (batchFrame X rfl chart.unusedC (by simpa only [xloc] using pages 1 (by decide))).keeps size
  have payload : Y.published [] x = X.published [] x :=
    (batchFrame Y rfl chart.unusedP (by simpa only [yloc] using pages 0 (by decide))).keeps size
  let ops := HistoryPartyPairExec.steps (w:=W) A.party node (nullTree F) (nullTree F) id
  have prep : HistoryRefreshEmitter.PrepAway B x := ⟨pair.seed,pair.commands,pair.arguments⟩
  have run : B.reached ops x = B.input x :=
    (HistoryReadyTape.after_away B.control ops B.entered x pair.cursor pair.jobs).trans prep.keeps.2.2
  have root : ¬(B.outputBase ≤ x ∧ x < B.outputBase+4) := by
    rw [bloc]
    have outside := pages 2 (by decide)
    omega
  have off : ¬(A.temp ≤ x ∧ x < A.temp+(HistoryGatherBody.fields (W:=W) A).length) := by omega
  calc
    vacantPass A node id input x = afterVacantPair A.party node id input x := by
      simp only [vacantPass,vacantMap,HistoryGatherExecution.headerImage,fillSegment,ite_eq_right off]
    _ = B.reached ops x := by
      change B.output ops x = _
      simp only [HistoryBoundedBody.Build.output,fillSegment,ite_eq_right root]
    _ = B.input x := run
    _ = Y.published [] x := HistoryPartyPairExec.prepared_outside A.party (Y.published []) x header
    _ = X.published [] x := payload
    _ = input x := checked

theorem PhysicalBanks.partyAway (banks : PhysicalBanks u A)
    (capacity : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V)
    (motif : A.party.motif<A.party.motifs) (party : A.party.party<A.party.parties)
    (x : ℕ) (away : OutsideNode u node x) : HistoryRefreshEmitter.PartyAway u A.party node x := by
  have pos : 0<volume u:=Nat.two_pow_pos _
  refine ⟨by have off:=away.scratch;omega,?_⟩
  intro k bank klt blt len small
  have valid : (⟨A.party.motif+2,A.party.party+2,k,bank⟩:Local).Valid A.party.motifs A.party.parties :=
    ⟨Nat.add_lt_add_right motif 2, Nat.add_lt_add_right party 2, klt, blt⟩
  have bound:=sector_window (node:=node) banks capacity valid
  rw [←banks.wordCount] at small
  exact away.arena_range bound.1 ((Nat.add_le_add_left small _).trans bound.2)

theorem vacant_outsideNode (banks : PhysicalBanks u A) (id : ((Fin 3→Bool)→F)→ℕ)
    (input : Memory W) (chart : VacantRoom A node id input)
    (capacity : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V)
    (motif : A.party.motif<A.party.motifs) (party : A.party.party<A.party.parties)
    (x : ℕ) (away : OutsideNode u node x) : vacantPass A node id input x=input x := by
  apply vacant_away banks id input chart capacity motif party x
  exact banks.partyAway capacity motif party x away

end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr Diagonal.TickWorkspace
open HistoryStageBody.Physical HistoryMotifJoin HistoryScratch
open HistoryGatherBody Diagonal.HistoryContraction BitNetwork.Ordered
open scoped BigOperators Fin.CommRing

noncomputable section
variable {F : Type} [Field F] [Fintype F] {W p u : ℕ} {A : HistoryGatherBody.Layout}
variable (node : ℕ) (id : ((Fin 3→Bool)→F)→ℕ)

namespace SiteSlot
variable (Z : SiteSlot F W p A) (input : Memory W)
local notation "first" => Z.init input
local notation "atArm" => Z.arms.entry node id first

/-- Sizes of the actual elected gather rows and their physical output page. The
pair word equality is supplied by the native checks/payload-and-pair publisher. -/
structure ArmSpace (u : ℕ) : Prop where
  header : 3+5*A.demandCap+4*A.supplyCap≤A.party.V
  width : ∀ (j : Fin A.party.parties) (i : Fin Z.count), Z.arms.select j.val=some i →
    ∀ q k,k<HistoryGatherExecution.cap A q → (Z.arms.plan i).width q k≤A.party.V
  result : ∀ (j : Fin A.party.parties) (i : Fin Z.count), Z.arms.select j.val=some i →
    (Z.arms.plan i).gatherBase=HistoryPartyPair.atPair (withParty A j.val).party node 2
  size : ∀ (j : Fin A.party.parties) (i : Fin Z.count), Z.arms.select j.val=some i →
    (Z.arms.plan i).gatherCount≤A.party.V
  pair : ∀ (j : Fin A.party.parties) (i : Fin Z.count), Z.arms.select j.val=some i →
    ∀ x, HistoryRefreshEmitter.PartyAway u (withParty A j.val).party node x → Z.arms.pairOut i x=atArm j.val x

omit [Field F] [Fintype F] in
theorem endState_outsideNode (banks : PhysicalBanks u A) (live : Z.Live node id input)
    (arms : Z.ArmSpace node id input u) (x : ℕ) (safe : OutsideNode u node x) :
    Z.endState node id input x=input x := by
  have capacity:=live.geometry.capacity.sectors
  have motif:=live.geometry.capacity.motif rfl
  have vbig : 128≤A.party.V:=by nlinarith only [capacity,Nat.zero_le (A.party.motifs*A.party.parties)]
  have big : 128≤volume u:=banks.wordCount ▸ vbig
  have growth : 10*volume u≤ stride u:=large_stride (by omega)
  have s14:=apart (u:=u) (by decide : 14<18)
  have s18:=apart (u:=u) (by decide : 18<19)
  have privateOff := safe.scratch_range (lo:=A.privateStarts) (hi:=A.privateStarts+9)
    (by rw [banks.privateStarts];omega) (by rw [banks.privateStarts];omega)
    (.inr (by rw [banks.privateStarts];omega))
  have begin_ : first x=input x := by
    have off : ¬(A.privateStarts≤x ∧ x<A.privateStarts+9) := by omega
    change HistoryMotifJoin.headerImage _ A.privateStarts 9 input x=_
    simp [HistoryMotifJoin.headerImage,fillSegment,off]
  have priorArms (j : ℕ) (bound : j≤A.party.parties) : atArm j x=input x := by
    induction j with
    | zero=>exact begin_
    | succ j ih=>
      let t : Fin A.party.parties:=⟨j,by omega⟩
      have previous:=ih (by omega)
      have next : atArm (j+1)=Z.arms.advance node id (atArm j) j := by
        simp only [ArmRows.entry,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rw [next]
      cases e:Z.arms.select j with
      | none=>
        have declined:=vacant_outsideNode (banks.withParty j) id (atArm j) (live.vacant t e) capacity
          motif t.isLt x safe
        simpa only [ArmRows.advance,ArmRows.mapOutAt,ArmRows.pairOutAt,e,HistoryRefreshEmitter.vacantPass]
          using declined.trans previous
      | some i=>
        let J:=withParty A j
        let loc : Local:=⟨A.party.motif+2,j+2,2,2⟩
        have valid : loc.Valid A.party.motifs A.party.parties :=
          ⟨Nat.add_lt_add_right motif 2, Nat.add_lt_add_right t.isLt 2,
            (by decide : 2 < 8), (by decide : 2 < 32)⟩
        have same := arms.result t i e
        have page : (Z.arms.plan i).gatherBase=
            atWord (base u 12) (volume u) A.party.motifs A.party.parties node loc 0 := by
          rw [same]
          change atWord A.party.arena A.party.V A.party.motifs A.party.parties node loc 0=_
          rw [banks.arena,banks.wordCount]
        have mapped:=gather_outside_node J (Z.arms.plan i) (Z.arms.pairOut i) safe banks.gather banks.wordCount
          (banks.wordCount ▸ arms.header) (fun q k lim=>banks.wordCount ▸ arms.width t i e q k lim)
          loc valid (banks.wordCount ▸ capacity) page (banks.wordCount ▸ arms.size t i e)
        exact (by
          simpa only [ArmRows.advance,ArmRows.mapOutAt,ArmRows.pairOutAt,e] using
            mapped.trans ((arms.pair t i e x ((banks.withParty j).partyAway capacity motif t.isLt x safe)).trans previous))
  exact (finish_outsideNode A true node (atArm A.party.parties) Z.children Z.wire id banks live.geometry x safe).trans
    (priorArms A.party.parties le_rfl)

end SiteSlot

namespace SiteRun
variable (Z : SiteRun F W p A) (first : Memory W) {n : ℕ} (pieces : Fin n→BitNetwork F p)
local notation "atSlot" => Z.entry node id first
local notation "final" => atSlot A.party.motifs
local notation "pins" => fun (_ : Fin n) (j : Fin p)=>(BitSource.pin j : BitSource 0 p)

omit [Field F] [Fintype F] in
/-- Global old-tree and ledger retention by the same native image as `SiteRun.emit_site`.
The node-start scan and all raw party, motif, and final site transitions are included. -/
theorem endState_outsideNode (banks : PhysicalBanks u A) (oldCap : ℕ) (input : Memory W)
    (oldBound : oldCap≤A.party.V)
    (initial : first=fillSegment A.nodePorts.starts (oldCap+1)
       (fun i=>(childWidth A.nodePorts oldCap (HistoryPartyBatchExec.numeric input) i:Word W)) input)
    (live : ∀ j : Fin A.party.motifs,(Z.slot j.val (atSlot j.val)).Live node id (atSlot j.val))
    (arms : ∀ j : Fin A.party.motifs,(Z.slot j.val (atSlot j.val)).ArmSpace node id (atSlot j.val) u)
    (geometry : Chart A false node final pieces pins id) (x : ℕ) (safe : OutsideNode u node x) :
    Z.endState node id first pieces x=input x := by
  have cap:=geometry.capacity.sectors
  have vbig : 128≤A.party.V:=by nlinarith only [cap,Nat.zero_le (A.party.motifs*A.party.parties)]
  rw [banks.wordCount] at oldBound vbig
  have growth : 10*volume u≤ stride u:=large_stride (by omega)
  have s14:=apart (u:=u) (by decide : 14<18)
  have s18:=apart (u:=u) (by decide : 18<19)
  have childOff:=safe.scratch_range (lo:=A.nodePorts.starts) (hi:=A.nodePorts.starts+(oldCap+1))
    (by rw [banks.childStarts];omega) (by rw [banks.childStarts];omega) (.inr (by rw [banks.childStarts];omega))
  have begin_ : first x=input x := by
    have off : ¬(A.nodePorts.starts≤x ∧ x<A.nodePorts.starts+(oldCap+1)) := by omega
    rw [initial];simp only [fillSegment,ite_eq_right off]
  have priorSlots (j : ℕ) (bound : j≤A.party.motifs) : atSlot j x=input x := by
    induction j with
    | zero=>exact begin_
    | succ j ih=>
      let i : Fin A.party.motifs:=⟨j,by omega⟩
      have step : atSlot (j+1)=Z.takeSlot node id (atSlot j) j := by
        simp only [entry,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rw [step]
      exact ((Z.slot j (atSlot j)).endState_outsideNode node id (atSlot j) (banks.withMotif j) (live i)
        (arms i) x safe).trans (ih (by omega))
  exact (finish_outsideNode A false node final pieces pins id banks geometry x safe).trans (priorSlots _ le_rfl)

end SiteRun
end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr Diagonal.TickWorkspace
open HistoryStageBody.Physical HistoryMotifJoin HistoryScratch HistoryGatherBody
open Diagonal.HistoryContraction BitNetwork.Ordered HistoryRefreshEmitter
open scoped BigOperators Fin.CommRing

noncomputable section
variable {F : Type} {W p u n node x : ℕ} {A : HistoryGatherBody.Layout} {arity : Fin n→ℕ}
  {loc : Local}

private abbrev pageStart (A : HistoryGatherBody.Layout) (node : ℕ) (loc : Local) :=
  atWord A.party.arena A.party.V A.party.motifs A.party.parties node loc 0

/-- One persisted S12 row of an earlier party or motif in the selected node. -/
structure PageRead (A : HistoryGatherBody.Layout) (node x : ℕ) (loc : Local) : Prop where
  valid : loc.Valid A.party.motifs A.party.parties
  lower : pageStart A node loc≤x
  upper : x<pageStart A node loc+A.party.V

theorem PageRead.apart (read : PageRead A node x loc)
    (cap : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V)
    (other : Local) (ok : other.Valid A.party.motifs A.party.parties) (ne : loc≠other) :
    x<pageStart A node other ∨ pageStart A node other+A.party.V≤x := by
  have small : 0<A.party.V:=by have:=read.lower;have:=read.upper;omega
  have bounds:=local_apart (base:=A.party.arena) (n:=node) small cap read.valid ok ne
  have bot:=read.lower
  have top:=read.upper
  change pageStart A node loc+A.party.V≤pageStart A node other ∨
    pageStart A node other+A.party.V≤pageStart A node loc at bounds
  omega

theorem PageRead.below (read : PageRead A node x loc) (banks : PhysicalBanks u A)
    (count : node<A.party.V^2) (cap : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V) :
    x<base u 14 := by
  have pos : 0<A.party.V:=by have:=read.lower;have:=read.upper;omega
  have hi:=HistoryScratch.fits (base:=A.party.arena) count cap read.valid (show A.party.V-1<A.party.V by omega)
  have top:=read.upper
  change pageStart A node loc+(A.party.V-1)<A.party.arena+A.party.V^4 at hi
  have end_ : x<A.party.arena+A.party.V^4 := by omega
  rw [banks.arena,banks.wordCount] at end_
  exact end_.trans_le (Diagonal.TickWorkspace.apart (u:=u) (by decide : 12<14))

theorem PageRead.partyAway (read : PageRead A node x loc) (banks : PhysicalBanks u A)
    (count : node<A.party.V^2) (cap : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V)
    (motif : A.party.motif<A.party.motifs) (party : A.party.party<A.party.parties)
    (prior : loc.motif≠A.party.motif+2 ∨ loc.party≠A.party.party+2) :
    PartyAway u A.party node x := by
  refine ⟨.inl (read.below banks count cap),?_⟩
  intro k bank klt blt len small
  let target : Local:=⟨A.party.motif+2,A.party.party+2,k,bank⟩
  have good : target.Valid A.party.motifs A.party.parties :=
    ⟨Nat.add_lt_add_right motif 2, Nat.add_lt_add_right party 2, klt, blt⟩
  have distinct : loc≠target := by
    intro same
    rcases prior with h|h
    · exact h (congrArg Local.motif same)
    · exact h (congrArg Local.party same)
  have frame:=read.apart cap target good distinct
  change x<pageStart A node target ∨ pageStart A node target+len≤x
  rw [←banks.wordCount] at small
  omega

private def oldLocal (A : HistoryGatherBody.Layout) (group : Bool) (slot role bank : ℕ) : Local :=
  if group then ⟨A.party.motif+2,role+2,2,bank⟩ else ⟨slot+2,0,3,bank⟩

private theorem previous_page (A : HistoryGatherBody.Layout) (group : Bool) (node : ℕ)
    (N : ∀ i,BitNetwork F (arity i)) (i : Fin n) (r x : ℕ) (word : childAddress A group node N i r x)
    (motif : group=true→A.party.motif<A.party.motifs) (role : group=true→ r<A.party.parties)
    (slot : group=false→i.val<A.party.motifs) (rows : 4*(N i).cells≤A.party.V)
    (pins : arity i≤A.party.V) (four : 4≤A.party.V) :
    ∃ col : Fin 3,PageRead A node x (oldLocal A group i.val r col.val) := by
  have valid (col : Fin 3) : (oldLocal A group i.val r col.val).Valid A.party.motifs A.party.parties := by
    cases h:group
    · exact ⟨Nat.add_lt_add_right (slot h) 2, Nat.zero_lt_succ _,
        (by decide : 3 < 8), col.isLt.trans (by decide : 3 < 32)⟩
    · exact ⟨Nat.add_lt_add_right (motif h) 2, Nat.add_lt_add_right (role h) 2,
        (by decide : 2 < 8), col.isLt.trans (by decide : 3 < 32)⟩
  have addr (col : ℕ) : cache A group node i.val r col=pageStart A node (oldLocal A group i.val r col) := by
    cases group <;> rfl
  rcases word with r₀|r₁|⟨_,r₂⟩
  · have h:=r₀
    change cache A group node i.val r 0≤x ∧ x<cache A group node i.val r 0+4*(N i).cells at h
    rw [addr] at h
    refine ⟨0,valid 0,h.1,?_⟩
    exact h.2.trans_le (Nat.add_le_add_left rows _)
  · have h:=r₁
    change cache A group node i.val r 1≤x ∧ x<cache A group node i.val r 1+4 at h
    rw [addr] at h
    exact ⟨1,valid 1,h.1,h.2.trans_le (Nat.add_le_add_left four _)⟩
  · have h:=r₂
    change cache A group node i.val r 2≤x ∧ x<cache A group node i.val r 2+arity i at h
    rw [addr] at h
    exact ⟨2,valid 2,h.1,h.2.trans_le (Nat.add_le_add_left pins _)⟩

private theorem rows_fit (N : ∀ i,BitNetwork F (arity i)) (total : 4*(∑ i,(N i).cells)≤A.party.V)
    (i : Fin n) : 4*(N i).cells≤A.party.V := by
  have offset:=Tree.prefix_next_le (fun j=>(N j).cells) i
  omega

variable [Field F] [Fintype F]
namespace SiteSlot
variable (Z : SiteSlot F W p A) (node : ℕ) (id : ((Fin 3→Bool)→F)→ℕ) (input : Memory W)
local notation "first" => Z.init input
local notation "atArm" => Z.arms.entry node id first
local notation "C" => Capacity A true node (atArm A.party.parties) Z.children id (h:=Z.shared) (p:=p)

omit [Field F] [Fintype F] in
theorem advance_previous (banks : PhysicalBanks u A) (bounds : C) (arms : Z.ArmSpace node id input u)
    (j : Fin A.party.parties)
    (vacant : Z.arms.select j.val=none→VacantRoom (withParty A j.val) node id (atArm j.val))
    {x : ℕ} {loc : Local} (old : PageRead A node x loc)
    (prior : loc.motif≠A.party.motif+2 ∨ loc.party≠j.val+2) :
    Z.arms.advance node id (atArm j.val) j.val x=atArm j.val x := by
  let J:=withParty A j.val
  have resident : PageRead J node x loc:=⟨old.valid,old.lower,old.upper⟩
  have clear:=resident.partyAway (banks.withParty j.val) bounds.nodeBound bounds.sectors
    (bounds.motif rfl) j.isLt prior
  cases on:Z.arms.select j.val with
  | none=>
    have keep:=vacant_away (banks.withParty j.val) id (atArm j.val) (vacant on) bounds.sectors
      (bounds.motif rfl) j.isLt x clear
    simpa only [ArmRows.advance,ArmRows.pairOutAt,ArmRows.mapOutAt,on,vacantPass] using keep
  | some i=>
    have lower:=old.below banks bounds.nodeBound bounds.sectors
    have pages:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 14<17)
    have temp : x<J.temp := by change x<A.temp;rw [banks.gather];omega
    have keep : HistoryGatherExecution.output J (Z.arms.plan i) (Z.arms.pairOut i) x=Z.arms.pairOut i x := by
      apply HistoryGatherExecution.output_away
      · exact Or.inl temp
      · intro q k hk
        exact .inl (temp.trans_le ((Nat.le_add_right _ _).trans (HistoryGatherExecution.aperture J q k hk).1))
      · rw [arms.result j i on]
        exact clear.page 2 2 (by decide) (by decide) _ (banks.wordCount ▸ arms.size j i on)
    simpa only [ArmRows.advance,ArmRows.pairOutAt,ArmRows.mapOutAt,on] using
      keep.trans (arms.pair j i on x clear)

omit [Field F] [Fintype F] in
/-- Subsequent elected or vacant arms cannot change the earlier raw party's true
gate stream, four-word header, or gathered input map. -/
theorem later (banks : PhysicalBanks u A) (bounds : C) (arms : Z.ArmSpace node id input u)
    (vacant : ∀ j : Fin A.party.parties,Z.arms.select j.val=none→VacantRoom (withParty A j.val) node id (atArm j.val))
    (i : Fin Z.count) (j : Fin A.party.parties) (lt : (Z.arms.index i).val<j.val) (x : ℕ)
    (word : childAddress A true node Z.children i (Z.arms.index i).val x) :
    Z.arms.advance node id (atArm j.val) j.val x=atArm j.val x := by
  have four : 4≤A.party.V := by
    have c:=bounds.sectors
    nlinarith only [c,Nat.zero_le (A.party.motifs*A.party.parties)]
  obtain ⟨col,page⟩:=previous_page A true node Z.children i (Z.arms.index i).val x word
    (fun _=>bounds.motif rfl) (fun _=>(Z.arms.index i).isLt) (by simp)
    (rows_fit (A:=A) Z.children bounds.cells i) (bounds.demand i) four
  apply Z.advance_previous node id input banks bounds arms j (vacant j) page (.inr ?_)
  change (Z.arms.index i).val+2≠j.val+2
  omega

end SiteSlot
end
end ThreeFlat.RAM.HistoryShrinkEmitter

end OAI
