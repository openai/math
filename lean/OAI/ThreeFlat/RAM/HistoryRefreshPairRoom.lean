import OAI.ThreeFlat.RAM.HistoryRefreshBatch

namespace OAI
/-! # Physical reads and execution of a refresh party pair -/
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

section ElectedPair
open HistoryPartyPairExec
variable (A : HistoryPartyBatch.Layout) (n : ℕ) (L : Tree F a) (R : Tree F b)
  (id : ((Fin 3→Bool)→F)→ℕ) (post : Memory W)
local notation "B" => HistoryPartyPairExec.build A n a b post
local notation "q" => HistoryPartyPairExec.copyHeader A n L R
local notation "ops" => HistoryPartyPairExec.steps (w:=W) A n L R id
local notation "left" => (Info.mk (dest A true n 0+4*L.rows) a L.rows L.bits)
local notation "right" => (Info.mk (dest A false n 0+4*R.rows) b R.rows R.bits)

/-- Widths and separation of the pair's actual scratch writes. -/
structure PairSourceRoom : Prop where
  seed : A.seed+9<2^W
  order : A.seed+9≤A.commands ∧ A.commands+28≤A.arguments
  commands : A.commands+28<2^W
  arguments : A.arguments+14<2^W
  children : ∀ i,(link A n a i).node+3<2^W
  result : HistoryPartyPair.atPair A n 1+4<2^W
  headerApart : HistoryPartyPair.hub A+25≤HistoryPartyPair.atPair A n 1 ∨
    HistoryPartyPair.atPair A n 1+4≤HistoryPartyPair.hub A
  rootsApart : ∀ i,(link A n a i).node+4≤HistoryPartyPair.atPair A n 1 ∨
    HistoryPartyPair.atPair A n 1+4≤(link A n a i).node
  jobsAway : HistoryReadyTape.Away A.seed 9 ops ∧ HistoryReadyTape.Away A.commands 28 ops
  limits : ∀ j∈ops,j.finish<2^W

/-- Separation of the elected batch outputs from the pair's generated scratch words and jobs. -/
structure PairRoom : Prop where
  cursor : numeric post A.cursor-1=n
  boot : BootRoom A post n
  source : PairSourceRoom A n L R id (W:=W)
  space : Space A n L R id post
  frozen : Frozen A n L R post
  cap : ∀ j,fields A n a b j<2^W
  hubRoom : HistoryPartyPair.hub A+25<2^W
  roots : ∀ i j,let x:=(link A n a i).node+(j:Fin 4).val
    x<HistoryPartyPair.hub A ∨ HistoryPartyPair.hub A+25≤x
  seedLink : (header A n a b).children+8≤A.seed ∨ A.seed+9≤(header A n a b).children
  seedRoot : ∀ i,(link A n a i).node+4≤A.seed ∨ A.seed+9≤(link A n a i).node
  commandLink : (header A n a b).children+8≤A.commands ∨ A.commands+28≤(header A n a b).children
  commandRoot : ∀ i,(link A n a i).node+4≤A.commands ∨ A.commands+28≤(link A n a i).node
  operands : ∀ i,∀ j : Fin 5,Outside A ((HistoryPartyPairExec.rows A a b i).arg+j.val)
  rows : ∀ (i : Fin 2) (k : Fin (pairNetwork L R i).cells) (j : Fin 4),
    let x:=(q i).source+(4*k.val+j.val)
    Outside A x ∧ (x<HistoryPartyPair.hub A ∨ HistoryPartyPair.hub A+25≤x)
  hubStay : ∀ j : Fin 25,Retained A n L R id post (HistoryPartyPair.hub A+j.val)
  rootsStay : ∀ (i : Fin 2) (j : Fin 4),Retained A n L R id post ((link A n a i).node+j.val)
  leftFit : ∀ j,(left).words j<2^W
  rightFit : ∀ j,(right).words j<2^W

omit [CommRing F] in
/-- The two emitted jobs per child are loaded by the pair's own command generator. All
three uses of the child-link table follow the literal addresses in the prepared header. -/
theorem pair_source (layout : PairRoom A n L R id post) (c : Children A post n a b)
    (first : InputRows A n L R (numeric (B).input))
    (seedRows : InputRows A n L R (numeric (B).seeded))
    (commandRows : InputRows A n L R (numeric (B).commands)) : (B).Source ops := by
  let K:=header A n a b
  let hub:=HistoryPartyPair.hub A
  let out:=HistoryPartyPair.atPair A n 1
  let raw:=numeric ((B).reached ops)
  have skip (j : Fin 7) : Retained A n L R id post (hub+j.val):=layout.hubStay ⟨j.val,j.isLt.trans (by decide)⟩
  have linkPos (i : Fin 2) (j : Fin 4) : 7+4*i.val+j.val<25:=by have:=i.isLt;have:=j.isLt;omega
  have linkOff (i : Fin 2) (j : Fin 4) : K.children+4*i.val+j.val=hub+(7+4*i.val+j.val):=by
    change (hub+7)+4*i.val+j.val=_;omega
  have origin:=stored_hub A post n a b c layout.cap
  have reachHub (j : Fin 7) : raw (hub+j.val)=numeric (B).input (hub+j.val):=
    congrArg Fin.val (HistoryPartyPairExec.keep A n L R id post _ (skip j))
  have reachLink (i : Fin 2) (j : Fin 4) : raw (K.children+4*i.val+j.val)=numeric (B).input (K.children+4*i.val+j.val):=by
    rw [linkOff]
    exact congrArg Fin.val (HistoryPartyPairExec.keep A n L R id post _ (layout.hubStay ⟨_,linkPos i j⟩))
  have finalRows : InputRows A n L R raw:=
    ⟨fun i j=>(reachLink i j).trans (first.links i j),fun i j=>
      (congrArg Fin.val (HistoryPartyPairExec.keep A n L R id post _ (layout.rootsStay i j))).trans (first.info i j)⟩
  have finalHub (j:Fin 6) : raw (hub+j.val)=K.words j:=(reachHub j.castSucc).trans (origin j)
  have loadedHub : HistoryBoundedBody.readHub (B).layout raw=K:=by
    have z : raw hub=K.stream:=by simpa [Hub.words] using finalHub 0
    have pins : raw (hub+1)=K.pins := finalHub 1
    have shared : raw (hub+2)=K.shared := finalHub 2
    have argc : raw (hub+3)=K.argc := finalHub 3
    have links : raw (hub+4)=K.children := finalHub 4
    have arguments : raw (hub+5)=K.arguments := finalHub 5
    change Hub.mk (raw hub) (raw (hub+1)) (raw (hub+2)) (raw (hub+3)) (raw (hub+4)) (raw (hub+5)) = K
    rw [z,pins,shared,argc,links,arguments]
  have base : (B).outputBase=out:=stored_fields A post n a b c 6 (layout.cap 6)
  have frame {μ:Memory W} {lo len:ℕ} (inputs : InputRows A n L R (numeric μ))
      (headerFree : ∀ j:Fin 7,hub+j.val<lo ∨ lo+len≤hub+j.val)
      (linkFree : ∀ (i:Fin 2) (j:Fin 4),K.children+4*i.val+j.val<lo ∨ lo+len≤K.children+4*i.val+j.val)
      (rootFree : ∀ (i:Fin 2) (j:Fin 4),(link A n a i).node+j.val<lo ∨ lo+len≤(link A n a i).node+j.val) :
      HistoryBoundedBody.Frame (B).layout K μ lo len:=
    ⟨headerFree,linkFree,fun i j => by
      let k : Fin 2 := ⟨i.val,i.isLt⟩
      have seen := loaded_child A n L R inputs k
      change (child (header A n a b) (numeric μ) k.val).node+j.val<lo ∨
        lo+len≤(child (header A n a b) (numeric μ) k.val).node+j.val
      rw [seen]
      exact rootFree k j⟩
  have stable (j:Fin 6) : numeric (B).seeded (hub+j.val)=K.words j ∧ numeric (B).commands (hub+j.val)=K.words j:=by
    have access:=skip j.castSucc
    have ss:=access.seed
    have cc:=access.commands
    change hub+j.val<A.seed ∨ A.seed+9≤hub+j.val at ss
    change hub+j.val<A.commands ∨ A.commands+28≤hub+j.val at cc
    have sf:¬(A.seed≤hub+j.val ∧ hub+j.val<A.seed+9):=by omega
    have cf:¬(A.commands≤hub+j.val ∧ hub+j.val<A.commands+28):=by omega
    have eq₁ : (B).seeded (hub+j.val)=(B).input (hub+j.val):=by
      change fillSegment A.seed 9 _ (B).input (hub+j.val)=_
      simp [fillSegment,sf]
    have eq₂ : (B).commands (hub+j.val)=(B).seeded (hub+j.val):=by
      change fillSegment A.commands 28 _ (B).seeded (hub+j.val)=_
      simp [fillSegment,cf]
    exact ⟨(congrArg Fin.val eq₁).trans (origin j),(congrArg Fin.val (eq₂.trans eq₁)).trans (origin j)⟩
  have small:=layout.source
  have bounds :=layout.hubRoom
  have linksRoom : K.children+4*2≤2^W:=by change hub+7+8≤_;change hub+25<_ at bounds;omega
  have finalCount : raw (hub+3)=2:=finalHub 3
  have finalLinks : raw (hub+4)=K.children:=finalHub 4
  refine ⟨le_rfl,small.seed,by change hub+7<_;change hub+25<_ at bounds;omega,
    .inr (by change A.seed+9≤A.seed+64;omega),small.order,small.commands,small.arguments,origin,stable,
    frame seedRows (fun j=>(skip j).commands) ?_ ?_,frame commandRows (fun j=>(skip j).arguments) ?_ ?_,
    by change hub+25<_ at bounds;omega,by change 2≤2^W;change hub+25<_ at bounds;omega,linksRoom,?_,
    HistoryBoundedBody.Tape.tape_length (pairNetwork L R) (pairWire L R) id q,
    small.jobsAway,small.limits,HistoryPartyPairExec.loaded A n L R id post seedRows (.inl small.order.2),?_,?_,?_,?_,?_⟩
  · intro i j;rw [linkOff];exact (layout.hubStay ⟨_,linkPos i j⟩).commands
  · exact fun i j=>(layout.rootsStay i j).commands
  · intro i j;rw [linkOff];exact (layout.hubStay ⟨_,linkPos i j⟩).arguments
  · exact fun i j=>(layout.rootsStay i j).arguments
  · intro i
    let k : Fin 2 := ⟨i.val,i.isLt⟩
    change (child (header A n a b) (numeric (B).seeded) k.val).node+3<2^W ∧
      (child (header A n a b) (numeric (B).commands) k.val).node+3<2^W
    rw [loaded_child A n L R seedRows k,loaded_child A n L R commandRows k]
    exact ⟨small.children k,small.children k⟩
  · rw [base];exact small.result
  · change HistoryBoundedBody.Frame (B).layout (HistoryBoundedBody.readHub (B).layout raw) _ (B).outputBase 4
    rw [loadedHub,base]
    apply frame finalRows
    · intro j;have apart : hub+25≤out ∨ out+4≤hub:=small.headerApart;have:=j.isLt;omega
    · intro i j
      have apart : hub+25≤out ∨ out+4≤hub:=small.headerApart
      rw [linkOff];have:=linkPos i j;omega
    · intro i j;have apart := small.rootsApart i;have:=j.isLt;change _<out ∨ out+4≤_;omega
  · exact reachHub 6
  · change raw (hub+4)+4*raw (hub+3)≤_
    rw [finalLinks,finalCount];exact linksRoom
  · change ∀ k:Fin (raw (hub+3)),raw (raw (hub+4)+4*k.val)+3<_
    intro k
    let i:Fin 2:=⟨k.val,by have:=k.isLt;omega⟩
    have disk : raw (K.children+4*i.val)=(link A n a i).node:=by
      simpa [Child.words] using finalRows.links i 0
    change raw (raw (hub+4)+4*i.val)+3<_
    rw [finalLinks,disk];exact small.children i

omit [CommRing F] in
/-- Compose the elected batch executions at their actual post-staging offsets. -/
theorem elected_pair (input mid : Memory W) (checksTicks payloadTicks : ℕ)
    (checks : (HistoryPartyBatch.procedure W A true).Exec input mid checksTicks)
    (payload : (HistoryPartyBatch.procedure W A false).Exec mid post payloadTicks)
    (headL : ∀ j : Fin 4,post (dest A true n 1+j.val)=((left).words j:Word W))
    (headR : ∀ j : Fin 4,post (dest A false n 1+j.val)=((right).words j:Word W))
    (rowsL : HistoryCompiledRows.Records id L.compile (left).stream post)
    (rowsR : HistoryCompiledRows.Records id R.compile (right).stream post)
    (layout : PairRoom A n L R id post) :
    (HistoryPartyPair.procedure W A).Exec input ((B).output ops)
        (checksTicks+payloadTicks+overhead A W*(1+a+b+4*(L.rows+R.rows))) ∧
      (∀ j : Fin 4,(B).output ops (HistoryPartyPair.atPair A n 1+j.val)=
        (Info.words ⟨HistoryPartyPair.atPair A n 0,a+b,L.rows+R.rows,L.bits+R.bits⟩ j:Word W)) ∧
      HistoryCompiledRows.Records id (pair L R).compile (HistoryPartyPair.atPair A n 0) ((B).output ops) := by
  have hl (j : Fin 4) : numeric post (dest A true n 1+j.val)=(left).words j := by
    rw [numeric,headL,Fin.val_cast_of_lt (layout.leftFit j)]
  have hr (j : Fin 4) : numeric post (dest A false n 1+j.val)=(right).words j := by
    rw [numeric,headR,Fin.val_cast_of_lt (layout.rightFit j)]
  have children : Children A post n a b := ⟨layout.cursor,hl 1,hr 1⟩
  have first:=inputs_prepared A n L R post children layout.cap layout.roots hl hr
  have seeded:=inputs_seeded A n L R post first layout.seedLink layout.seedRoot
  have cmd:=inputs_commands A n L R post seeded layout.commandLink layout.commandRoot
  have childBank:=child_bank A n L R id post rowsL rowsR layout.rows
  have source:=pair_source A n L R id post layout children first seeded cmd
  have banks:=HistoryPartyPairExec.banks A n L R id post children layout.cap source seeded cmd
    layout.frozen layout.hubRoom layout.operands childBank
  have res:=HistoryPartyPairExec.resident A n L R id post children layout.cap layout.space banks
  obtain ⟨run,records⟩:=HistoryPartyPairExec.complete A n L R id input mid post checksTicks payloadTicks
    checks payload layout.boot source res
  have bound:=ticks_le A n L R id post
  refine ⟨Procedure.Spec.mono run (fun _=>_root_.id) (fun _ _=>_root_.id) (by omega),?_,records⟩
  exact pair_info A n L R id post children layout.cap layout.hubStay layout.rootsStay layout.roots hl hr

end ElectedPair

/-- Physical frame for the party batch at one word, through the static arrays,
the ready tape and its final four-word root publication. -/
structure BatchAway (X : HistoryPartyBatchExec.Build W) (jobs : List (HistoryReadyTape.Job W)) (x : ℕ) : Prop where
  cursor : x≠X.ctrl.val
  seed : x<X.layout.seed ∨ X.layout.seed+37≤x
  header : x<X.layout.batch ∨ X.layout.batch+26≤x
  commands : x<X.layout.commands ∨ X.layout.commands+21*X.count≤x
  arguments : x<X.layout.arguments ∨ X.layout.arguments+23*X.count≤x
  jobs : ∀ J∈jobs,x<J.start ∨ J.finish≤x
  target : x<X.target ∨ X.target+4≤x

theorem BatchAway.keeps {X : HistoryPartyBatchExec.Build W} {jobs : List (HistoryReadyTape.Job W)} {x : ℕ}
    (away : BatchAway X jobs x) (room : X.layout.seed+37<2^W) : X.published jobs x=X.input x :=
  X.published_outside jobs x room away.cursor away.seed away.header away.commands away.arguments away.jobs away.target


end
end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
