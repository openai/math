import OAI.ThreeFlat.RAM.HistoryStageNumericTape
import OAI.ThreeFlat.RAM.HistoryStageSource
import OAI.ThreeFlat.RAM.HistoryStagePhysicalBanks

namespace OAI
/-! # Native selected-stage evaluator for split-affine chart operands -/
namespace ThreeFlat.RAM.HistoryStageNumericRun
open Computability.VPVNP.BurstRAM PrivateRAM BitLayout Diagonal.HistoryContraction Diagonal.TickWorkspace
open HistoryStageRoot HistoryStageBody HistoryStageSetup HistoryStageResult HistoryStageSnapshots
open HistoryPartyBatchExec HistoryStageBody.Physical HistoryBoundedBody HistoryBoundedJoin
open HistoryStageBankArena HistoryStageNumericTape
open scoped BigOperators Fin.CommRing
noncomputable section
variable {F : Type*} {W h p n : ℕ} {ar : Fin n→ℕ}
    (u idx : ℕ) (archive : Archive) (family : Family) (m : Memory W)
    (N : ∀ k,BitNetwork F (ar k)) (wire : ∀ k,Fin (ar k)→BitSource h p)
    (tag : ((Fin 3→Bool)→F)→ℕ)
local notation "A" => Physical.layout u archive family
local notation "C" => family.childBound
local notation "T" => numInput A C (numeric m)
local notation "X" => HistoryStageSetup.run A C m
local notation "B" => HistoryStageBody.StageRun.compiled X
local notation "S" => Diagonal.TickWorkspace.stride u
local notation "vol" => volume u
open private copyHeader from OAI.ThreeFlat.RAM.HistoryStageNumericTape
local notation "q" => copyHeader T (numeric m) N wire
local notation "row" => fun i : Fin n=>Typed.mapRow T (numeric m) (Fin.val i)
local notation "H" => HistoryStageRoot.hub T (numeric m)
local notation "link" => HistoryStageRoot.link T (numeric m)
local notation "G" => Ranges u idx archive family m N q
local notation "Y" => HistoryStageRoot.childCount T (numeric m)
local notation "ops" => Tape.tape (W:=W) N wire tag q

theorem linkFits (g : G) (shape : Wiring T (numeric m) wire) (i : Fin (n)) (j : Fin 4) : (link i.val).words j<2^W := by
  have live : i.val<Y+1:=by rw [←shape.size];exact i.isLt
  have r:=g.rootBelow ⟨i.val,live⟩
  have c:=g.scalar.cacheRoom;have mfit:=g.scalar.mapRoom
  have wid:=g.scalar.wide
  have z:=(g.join.pins i).2; have high:=g.join.words
  have map : (q i).pins=mapPtr T (numeric m) i.val:=rfl
  fin_cases j
  · change HistoryStageRoot.ptr T (numeric m) i.val<2^W
    change HistoryStageRoot.ptr T (numeric m) i.val+6≤_ at r;omega
  · change mapPtr T (numeric m) i.val<2^W;rw [←map];omega
  · change 8<2^W;omega
  · change mapArgs A C+5*i.val<2^W;omega

theorem banks (g : G) (shape : Wiring T (numeric m) wire) (saved : Stored T (numeric m) N wire tag m) (cells : SourceCells A C T (numeric m) W) :
    Build.Banks B N wire tag q row := by
  obtain ⟨_,seed,cmd,enter⟩:=g.inputSnapshots cells
  obtain ⟨_,s0,c0,_⟩:=g.cacheInfo cells
  have fits:=linkFits u idx archive family m N wire g shape
  have rseed:=readback A C (B).seeded shape seed s0 rfl fits
  have rcmd:=readback A C (B).commands shape cmd c0 rfl fits
  have commands:=commandWords shape saved rseed
  have small:=g.scalar
  have budget : vol+400+32*(C+1)≤S:=g.join.scratch
  have countBound:=g.join.childCount
  have ix (i : Fin n) : i.val<Y+1:=by rw [←shape.size];exact i.isLt
  have midrange (x : ℕ) (lo : HistoryStageBody.hub A≤x) (hi : x<19*S+2) := g.protect lo hi
  refine ⟨by change n=Y+1;exact shape.size,?_,?_,.inl small.commandArgs,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have atSeed:=(B).seeded_word (7 : Fin 9)
    change (B).seeded ((A).party.seed+7)=((A).party.commands:Word W) at atSeed
    rw [small.cursor]
    have fst : ¬((B).layout.commands≤(A).party.seed+7 ∧ (A).party.seed+7<(B).layout.commands+14*(B).hub.argc) :=
      by
        intro placed
        have commandStart : (A).party.commands≤(A).party.seed+7 := placed.1
        have commandAfter : (A).party.seed+9≤(A).party.commands := small.seedCommand
        omega
    have snd : ¬((B).hub.arguments≤(A).party.seed+7 ∧ (A).party.seed+7<(B).hub.arguments+7*(B).hub.argc) :=
      by have a:=small.seedCommand;have b:=small.commandArgs;change _≤(T).copyArguments at b
         change ¬((T).copyArguments≤(A).party.seed+7 ∧ _);omega
    change (B).entered ((A).party.seed+7)=_
    simp only [Build.entered,Build.commands,fillSegment,ite_eq_right fst,ite_eq_right snd];exact atSeed
  · rw [shape.size];exact small.commandRoom.le
  · intro i side j;have hi:=ix i;have col:=j.isLt
    apply midrange
    · change 15*S+vol+64+48≤16*S+(14*i.val+7*side.toNat+j.val);omega
    · change 16*S+(14*i.val+7*side.toNat+j.val)<19*S+2
      cases side <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega
  · intro i;exact congrFun (commands i).1 2
  · intro i;exact congrFun (commands i).1 0
  · intro i;have b:=small.mapRoom;have c:=ix i;change mapArgs A C+5*i.val+4<2^W;omega
  · intro i j _;have live:=ix i;have jj:=j.isLt
    apply midrange
    · change 15*S+vol+64+48≤15*S+vol+64+55+4*(C+1)+5*i.val+j.val;omega
    · change 15*S+vol+64+55+4*(C+1)+5*i.val+j.val<19*S+2;omega
  · intro i j _
    have op:=enter.operand ⟨i.val,ix i⟩ j
    have eq:=mapWords saved i j
    change (B).entered (mapArgs A C+5*i.val+j.val)=_
    simpa only [Nat.add_assoc,eq] using op
  · exact mapValue shape (B).entered
  · intro i h;change 8=10 at h;omega
  · rw [shape.size];exact small.argRoom.le
  · intro i j;have a:=ix i;have c:=j.isLt
    apply midrange
    · change 15*S+vol+64+48≤17*S+(7*i.val+j.val);omega
    · change 17*S+(7*i.val+j.val)<19*S+2;omega
  · exact copyWords shape saved rcmd
  · exact g.rowProtected
  · intro i x j
    rw [g.rowEntered cells i x j]
    exact saved.rows i x j

/-- The ready tape's map and copy operations now consume the genuine native
records. Arity, hidden and LUT bounds refer to the original compiled factors. -/
theorem resident (g : G) (shape : Wiring T (numeric m) wire) (saved : Stored T (numeric m) N wire tag m) (cells : SourceCells A C T (numeric m) W)
    (widths : ∀ k,2+ar k+(N k).internal<2^W) (bits : h<2^W)
    (ids : ∀ tt,tag tt<2^W)
    (cache : (B).outputBase=bankBase A C T .result)
    (allRows : (T).stream+4*(BitNetwork.Ordered.glue N wire).cells≤base u 13) :
    Build.Resident B N wire tag q row (T).stream := by
  have b:=banks u idx archive family m N wire tag g shape saved cells
  have w:=g.scalar.wide;have cursor:=g.scalar.cursor
  change (B).control.val=15*S+vol+7 at cursor
  have high : 20*S<2^W:=g.join.words
  have cacheAt : (B).outputBase=base u 13+8*idx:=by
    change (B).outputBase=base u 13+8*(T).id at cache
    simpa only [g.join.index] using cache
  apply (B).resident_of_banks N wire tag q row b (T).stream (by omega) (fun _=>.inl rfl) ?_ ?_
    (by intro i bad;change 8=10 at bad;omega) ?_ ?_ ?_ ?_ ?_ (fun _=>⟨rfl,rfl,rfl⟩) (fun _=>rfl) ?_ ?_
  · intro i
    by_cases zero : i.val=0
    · change (operands T (numeric m) i.val 2)<2^W
      simpa [operands,zero,shape.shared] using bits
    · change (operands T (numeric m) i.val 2)<2^W
      simp only [operands,zero,ite_false,Matrix.cons_val_two]
      exact (m _).isLt
  · intro i;exact (g.join.pins i).2.trans g.join.words.le
  · intro i j;right;have a:=(g.join.rows i).2.trans g.join.arena
    have b:=(g.join.pins j).1;change _≤14*S at a;change 19*S+2≤_ at b;omega
  · intro i;left;have a:=(g.join.pins i).1;change 19*S+2≤_ at a
    have bud:=g.join.scratch;change vol+400+32*(C+1)≤S at bud;omega
  · intro i;right;have a:=(g.join.rows i).2.trans g.join.arena;change _≤14*S at a;omega
  · intro i;have a:=g.rowLimit i;change _≤14*S at a;omega
  · intro i;have a:=widths i;change 2+ar i<2^W;omega
  · intro i;exact HistoryCompiledRows.metadata_fits tag (N i) (widths i).le ids
  · exact .inr (by rw [cacheAt];omega)


/-- Decode the mounted command/argument arrays and run the native prefix to its real
S13 output. The child scans use the actual pointers of the supplied chart. -/
theorem run_source_above (g : G) (shape : Wiring T (numeric m) wire)
    (saved : Stored T (numeric m) N wire tag m) (head : (X).Header)
    (cells : SourceCells A C T (numeric m) W) (inputs : ∀ j,(T).words j<2^W)
    (earlier : ∀ k,k<Y→numeric m (numeric m (HistoryStageRoot.node T+3)+k)<(T).id)
    (listCells : ∀ k,k<Y→base u 20≤numeric m (HistoryStageRoot.node T+3)+k)
    (incident : ∀ j : Fin 2,base u 20≤numeric m (HistoryStageRoot.node T+6)+j.val)
    (last : 0<numeric m (numeric m (HistoryStageRoot.node T+6))→∀ j,2≤j→j≤3→
      base u 20≤HistoryStageBounds.lastIncident T (numeric m)+j)
    (widths : ∀ k,2+ar k+(N k).internal<2^W) (bits : h<2^W) (pins : p<2^W)
    (ids : ∀ tt,tag tt<2^W) (rowVolume : 4*(∑ i,(N i).cells)≤vol) :
    let out:=adjust A C T .result ((B).output ops)
    ((HistoryStageBody.join A C W).Exec m out ((X).prepareCost+(B).ticks ops+writeCost A C T .result ((B).output ops)) ∧
      HistoryCompiledRows.Records tag (BitNetwork.Ordered.glue N wire) (T).stream out) ∧ HistoryBoundedBody.Build.Source B ops := by
  have budget : vol+400+32*(C+1)≤S:=g.join.scratch
  have w : 20*S<2^W:=g.join.words
  have endSpace:=Ranges.resultSpace_above u idx archive family m N wire tag q g earlier listCells incident last
  have cache:=HistoryStageResult.compiled_base A C m cells g.join.childCount (by have:=g.scalar.wide;omega)
    (by have:=endSpace.cacheRoom;omega) endSpace.pointerCounter endSpace.pointerJobs
  have space : limit A C<2^W:=by change 15*S+vol+64+55+4*(C+1)+5*(C+1)+3*C+7*C<2^W;omega
  have scale:=g.scalar
  have nonempty : 0<n:=by rw [shape.size];omega
  let k : Fin n:=⟨0,nonempty⟩
  have up : (T).stream<2^W:=by have a:=(g.dest k).1;have b:=(g.dest k).2;have e:=g.extEnd;change _≤14*S at e;omega
  have hubFit (j : Fin 6) : (H).words j<2^W:=by
    fin_cases j
    · exact up
    · change outPins T (numeric m)<2^W;rw [shape.pins];exact pins
    · change hidden T (numeric m)<2^W;rw [shape.shared];exact bits
    · have b:=g.join.childCount;change Y+1<2^W;omega
    · have b:=scale.linkRoom;change (T).links<2^W;omega
    · have b:=scale.argRoom;change (T).copyArguments<2^W;omega
  have lk:=linkFits u idx archive family m N wire g shape
  have lf (i : Fin (Y+1)) := lk ⟨i.val,by rw [shape.size];exact i.isLt⟩
  have snap:=(g.inputSnapshots cells).2.1
  have info:=(g.cacheInfo cells).2.1
  have words:=readback A C (B).seeded shape snap info rfl lk
  have cmd:=commandWords shape saved words
  have loaded : HistoryReadyTape.Loaded (B).layout.commands ops (B).entered:=
    (B).loaded N wire tag q shape.size (.inl scale.commandArgs) (fun k=>congrFun (cmd k).1 1)
      (fun k=>congrFun (cmd k).1 6) (fun k=>congrFun (cmd k).2 1) (fun k=>congrFun (cmd k).2 6)
  have source:=HistoryStageSource.of_loaded u idx archive family m N wire tag q g cells shape.size hubFit lf cache loaded
  have endHead:=make_result_bank A C m ops endSpace cells inputs g.join.childCount space
  have beginEnd : (T).stream+vol=(T).ext:=by
    have bankSector (b : ℕ) :
        HistoryScratch.sector family.motifs family.parties ⟨0,0,5,b⟩=160+b := by
      simp [HistoryScratch.sector]
    change base u 12+((T).id*vol+HistoryScratch.sector family.motifs family.parties ⟨0,0,5,0⟩)*vol+0+vol =
      base u 12+((T).id*vol+HistoryScratch.sector family.motifs family.parties ⟨0,0,5,1⟩)*vol+0
    rw [bankSector,bankSector]
    ring
  have area : (T).stream+4*(BitNetwork.Ordered.glue N wire).cells≤base u 13:=by
    change (T).stream+4*(∑ i,(N i).cells)≤base u 13
    have up:=g.extEnd;omega
  have resident:=resident u idx archive family m N wire tag g shape saved cells widths bits ids cache area
  refine ⟨?_,source⟩
  apply (X).join_run N wire tag q row (T).stream head source resident endHead
  right
  exact area.trans (Nat.le_add_right _ _)

/-- Decode the mounted command/argument arrays and run the native prefix to its real
S13 output. The child scans use the actual pointers of the supplied chart. -/
theorem run_source (g : G) (shape : Wiring T (numeric m) wire)
    (saved : Stored T (numeric m) N wire tag m) (head : (X).Header)
    (cells : SourceCells A C T (numeric m) W) (inputs : ∀ j,(T).words j<2^W)
    (earlier : ∀ k,k<Y→numeric m (numeric m (HistoryStageRoot.node T+3)+k)<(T).id)
    (listCells : ∀ k,k<Y→NavigationCell u (numeric m (HistoryStageRoot.node T+3)+k))
    (incident : ∀ j : Fin 2,NavigationCell u (numeric m (HistoryStageRoot.node T+6)+j.val))
    (last : 0<numeric m (numeric m (HistoryStageRoot.node T+6))→∀ j,2≤j→j≤3→
      NavigationCell u (HistoryStageBounds.lastIncident T (numeric m)+j))
    (widths : ∀ k,2+ar k+(N k).internal<2^W) (bits : h<2^W) (pins : p<2^W)
    (ids : ∀ tt,tag tt<2^W) (rowVolume : 4*(∑ i,(N i).cells)≤vol) :
    let out:=adjust A C T .result ((B).output ops)
    ((HistoryStageBody.join A C W).Exec m out ((X).prepareCost+(B).ticks ops+writeCost A C T .result ((B).output ops)) ∧
      HistoryCompiledRows.Records tag (BitNetwork.Ordered.glue N wire) (T).stream out) ∧ HistoryBoundedBody.Build.Source B ops :=
  run_source_above u idx archive family m N wire tag g shape saved head cells inputs earlier
    (fun k hk=>(listCells k hk).1) (fun j=>(incident j).1) (fun h j l r=>(last h j l r).1)
    widths bits pins ids rowVolume

theorem run (g : G) (shape : Wiring T (numeric m) wire)
    (saved : Stored T (numeric m) N wire tag m) (head : (X).Header)
    (cells : SourceCells A C T (numeric m) W) (inputs : ∀ j,(T).words j<2^W)
    (earlier : ∀ k,k<Y→numeric m (numeric m (HistoryStageRoot.node T+3)+k)<(T).id)
    (listCells : ∀ k,k<Y→NavigationCell u (numeric m (HistoryStageRoot.node T+3)+k))
    (incident : ∀ j : Fin 2,NavigationCell u (numeric m (HistoryStageRoot.node T+6)+j.val))
    (last : 0<numeric m (numeric m (HistoryStageRoot.node T+6))→∀ j,2≤j→j≤3→
      NavigationCell u (HistoryStageBounds.lastIncident T (numeric m)+j))
    (widths : ∀ k,2+ar k+(N k).internal<2^W) (bits : h<2^W) (pins : p<2^W)
    (ids : ∀ tt,tag tt<2^W) (rowVolume : 4*(∑ i,(N i).cells)≤vol) :
    let out:=adjust A C T .result ((B).output ops)
    (HistoryStageBody.join A C W).Exec m out ((X).prepareCost+(B).ticks ops+writeCost A C T .result ((B).output ops)) ∧
      HistoryCompiledRows.Records tag (BitNetwork.Ordered.glue N wire) (T).stream out :=
  (run_source u idx archive family m N wire tag g shape saved head cells inputs earlier listCells incident last
    widths bits pins ids rowVolume).1

end

end ThreeFlat.RAM.HistoryStageNumericRun

end OAI
