import OAI.ThreeFlat.RAM.HistoryRefreshPairRoom

namespace OAI
/-! # Execution and preserved memory cells of a vacant refresh party -/
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

section VacantFrame
variable (A : HistoryPartyBatch.Layout) (n : ℕ) (id : ((Fin 3→Bool)→F)→ℕ) (input : Memory W)
local notation "X" => vacantChecks A input
local notation "Y" => vacantPayload A input
local notation "P" => HistoryPartyPairExec.build A n 0 0 ((Y).published [])
local notation "ops" => HistoryPartyPairExec.steps (w:=W) A n (nullTree F) (nullTree F) id

def afterVacantPair := (P).output ops

omit [CommRing F] in
theorem vacant_pair (sx : (X).Source []) (sy : (Y).Source []) (ix : ¬occupied A (numeric input))
    (iy : ¬occupied A (numeric ((X).published []))) (n₀ : numeric input A.cursor-1=n)
    (n₁ : numeric ((X).published []) A.cursor-1=n)
    (leftHead : ∀ j : Fin 4,BatchAway Y [] (dest A true n 1+j.val))
    (room : PairRoom A n (nullTree F) (nullTree F) id ((Y).published [])) :
    (HistoryPartyPair.procedure W A).Exec input (afterVacantPair A n id input)
      ((X).staticCost+(Y).staticCost+HistoryPartyPairExec.overhead A W) := by
  obtain ⟨checkRun,checkHead⟩:=(X).inactive_exec sx ix
  obtain ⟨payloadRun,payloadHead⟩:=(Y).inactive_exec sy iy
  have hc:=inactive_header A true input sx.seedRoom ix
  have hp:=inactive_header A false ((X).published []) sy.seedRoom iy
  change info (X).table=_ at hc
  change info (Y).table=_ at hp
  rw [hc] at checkHead
  rw [hp] at payloadHead
  have xloc : (X).target=dest A true n 1:=by
    exact congrArg (fun u => dest A true u 1) n₀
  have yloc : (Y).target=dest A false n 1:=by
    exact congrArg (fun u => dest A false u 1) n₁
  rw [xloc,n₀] at checkHead
  rw [yloc,n₁] at payloadHead
  have empty : (nullTree F).compile.cells=0 := (compiled_rows (nullTree F)).trans null_rows
  have run := elected_pair A n (nullTree F) (nullTree F) id ((Y).published []) input ((X).published [])
    (X).staticCost (Y).staticCost checkRun payloadRun
    (fun j => by
      simp only [null_rows, null_bits, Nat.mul_zero, Nat.add_zero]
      exact ((leftHead j).keeps sy.seedRoom).trans (checkHead j))
    (fun j => by simpa only [null_rows, null_bits, Nat.mul_zero, Nat.add_zero] using payloadHead j)
    (fun i => (Fin.cast empty i).elim0) (fun i => (Fin.cast empty i).elim0) room
  intro Pdims Rdims Kdims M pc reg pub exit installed data c m start source
  have reached := run.1 M pc reg pub exit installed data c m start source
  simpa only [afterVacantPair, null_rows, Nat.mul_zero, Nat.add_zero, Nat.mul_one] using reached

omit [CommRing F] in
/-- The empty batch and pair still write their own four-word summaries, which are
disjoint from the occupied party's pair, map and root. -/
theorem vacant_pair_keeps (x : ℕ) (room : A.seed+37<2^W)
    (checks : BatchAway X [] x) (payload : BatchAway Y [] x)
    (pair : HistoryPartyPairExec.Retained A n (nullTree F) (nullTree F) id ((Y).published []) x)
    (header : x<HistoryPartyPair.hub A ∨ HistoryPartyPair.hub A+25≤x)
    (root : x<(P).outputBase ∨ (P).outputBase+4≤x) : afterVacantPair A n id input x=input x := by
  have q:=HistoryPartyPairExec.keep A n (nullTree F) (nullTree F) id ((Y).published []) x pair
  have frame:=HistoryPartyPairExec.prepared_outside A ((Y).published []) x header
  have r : ¬((P).outputBase≤x ∧ x<(P).outputBase+4) := by omega
  simp only [afterVacantPair,HistoryBoundedBody.Build.output,fillSegment,ite_eq_right r]
  exact q.trans (frame.trans ((payload.keeps room).trans (checks.keeps room)))

end VacantFrame

section VacantArm
variable (A : HistoryGatherBody.Layout) (node : ℕ) (id : ((Fin 3→Bool)→F)→ℕ) (input : Memory W)
local notation "X" => vacantChecks A.party input
local notation "Y" => vacantPayload A.party input
local notation "P" => afterVacantPair A.party node id input
local notation "plan" => HistoryGatherExecution.nativePlan A P (fun _ _ _=>0) (fun _=>0)

def vacantMap (A : HistoryGatherBody.Layout) (input : Memory W) :=
  HistoryGatherExecution.headerImage A (HistoryGatherExecution.nativePlan A input (fun _ _ _=>0) (fun _=>0)) input

def vacantPairCost := (X).staticCost+(Y).staticCost+HistoryPartyPairExec.overhead A.party W
def vacantMapCost (A : HistoryGatherBody.Layout) (W : ℕ) :=
  HistoryGatherExecution.headerCharge W A+13*A.demandCap+13*A.supplyCap+13

/-- Locally checkable chart for an absent raw party. Both batch preparations read
their zero seed fields and write their own four-word roots, while the gather is empty. -/
structure VacantRoom : Prop where
  checks : (X).Source []
  payload : (Y).Source []
  unusedC : ¬occupied A.party (numeric input)
  unusedP : ¬occupied A.party (numeric ((X).published []))
  before : numeric input A.party.cursor-1=node
  between : numeric ((X).published []) A.party.cursor-1=node
  saved : ∀ j : Fin 4,BatchAway Y [] (dest A.party true node 1+j.val)
  pair : PairRoom A.party node (nullTree F) (nullTree F) id ((Y).published [])
  unusedMap : ¬HistoryGatherBody.partyActive A P
  headerBound : 3+5*A.demandCap+4*A.supplyCap≤A.party.V
  pages : HistoryGatherExecution.portsEnd A<2^W
  mask : HistoryGatherBody.MaskRoom A P A.temp (A.temp+(HistoryGatherBody.fields (W:=W) A).length)

omit [CommRing F] in
theorem vacant_arm (room : VacantRoom A node id input) :
    (HistoryPartyPair.procedure W A.party).Exec input P (vacantPairCost A input) ∧
    (HistoryGatherBody.procedure W A).Exec P (vacantMap A P) (vacantMapCost A W) :=
  ⟨vacant_pair A.party node id input room.checks room.payload room.unusedC room.unusedP room.before room.between
    room.saved room.pair,
   HistoryGatherExecution.execute_inactive A P room.unusedMap room.headerBound room.pages room.mask⟩

def vacantPass := vacantMap A P

omit [CommRing F] in
theorem vacant_keeps (x : ℕ)
    (area : x<A.temp ∨ A.temp+(HistoryGatherBody.fields (W:=W) A).length≤x)
    (bounds : A.party.seed+37<2^W) (checks : BatchAway X [] x) (payload : BatchAway Y [] x)
    (pair : HistoryPartyPairExec.Retained A.party node (nullTree F) (nullTree F) id ((Y).published []) x)
    (header : x<HistoryPartyPair.hub A.party ∨ HistoryPartyPair.hub A.party+25≤x)
    (root : x<(HistoryPartyPairExec.build A.party node 0 0 ((Y).published [])).outputBase ∨
      (HistoryPartyPairExec.build A.party node 0 0 ((Y).published [])).outputBase+4≤x) :
    vacantPass A node id input x=input x := by
  have off : ¬(A.temp≤x ∧ x<A.temp+(HistoryGatherBody.fields (W:=W) A).length):=by omega
  simp only [vacantPass,vacantMap,HistoryGatherExecution.headerImage,fillSegment,ite_eq_right off]
  exact vacant_pair_keeps A.party node id input x bounds checks payload pair header root

/-- The finite intervals touched by an inactive procedure at one external word. -/
structure VacantAway (x : ℕ) : Prop where
  gather : x<A.temp ∨ A.temp+(HistoryGatherBody.fields (W:=W) A).length≤x
  checks : BatchAway X [] x
  payload : BatchAway Y [] x
  pair : HistoryPartyPairExec.Retained A.party node (nullTree F) (nullTree F) id ((Y).published []) x
  header : x<HistoryPartyPair.hub A.party ∨ HistoryPartyPair.hub A.party+25≤x
  output : let p:=HistoryPartyPairExec.build A.party node 0 0 ((Y).published [])
    x<p.outputBase ∨ p.outputBase+4≤x

omit [CommRing F] in
theorem VacantAway.keeps {x : ℕ} (f : VacantAway A node id input x) (room : A.party.seed+37<2^W) :
    vacantPass A node id input x=input x:=
  vacant_keeps A node id input x f.gather room f.checks f.payload f.pair f.header f.output

omit [CommRing F] in
theorem vacant_output_base (chart : VacantRoom A node id input) :
    (HistoryPartyPairExec.build A.party node 0 0 ((Y).published [])).outputBase=HistoryPartyPair.atPair A.party node 1 := by
  let m:=(Y).published []
  have row : HistoryPartyPair.word A.party (numeric m) 6=HistoryPartyPair.atPair A.party node 1:=by
    change HistoryPartyPair.atPair A.party (numeric m A.party.cursor-1) 1=_
    rw [chart.pair.cursor]
  have cap : HistoryPartyPair.atPair A.party node 1<2^W:=chart.pair.cap 6
  change (HistoryPartyPairExec.prepared A.party m (HistoryPartyPair.hub A.party+6)).val=_
  have saved : HistoryPartyPairExec.prepared A.party m (HistoryPartyPair.hub A.party+6) =
      (HistoryPartyPair.word A.party (numeric m) 6 : Word W) := HistoryPartyPairExec.hub_read A.party m 6
  rw [saved, row, Fin.val_cast_of_lt cap]

omit [CommRing F] in
theorem empty_pair_jobs (job : HistoryReadyTape.Job W)
    (member : job∈HistoryPartyPairExec.steps (w:=W) A.party node (nullTree F) (nullTree F) id) : job.count=0 := by
  have both : List.finRange 2=[0,1]:=by decide
  simp only [HistoryPartyPairExec.steps,Tape.tape,both,List.flatMap_cons,List.flatMap_nil,Tape.jobs,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  · rfl
  · change 4*(nullTree F).compile.cells=0;rw [compiled_rows,null_rows,Nat.mul_zero]
  · rfl
  · change 4*(nullTree F).compile.cells=0;rw [compiled_rows,null_rows,Nat.mul_zero]

end VacantArm


end
end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
