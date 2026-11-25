import OAI.ThreeFlat.RAM.HistoryStageBankArena
import OAI.ThreeFlat.RAM.HistoryStageBankWords

namespace OAI
/-! # Reaching the result from a selected stage's actual map and copy commands -/

noncomputable section
namespace ThreeFlat.RAM.HistoryStageSource
open Computability.VPVNP.BurstRAM PrivateRAM HistoryStageBody HistoryStageBody.Physical
open HistoryStageRoot HistoryStageSetup HistoryStageSnapshots HistoryStageBankArena
open Diagonal.HistoryContraction Diagonal.TickWorkspace HistoryPartyBatchExec HistoryBoundedBody
open HistoryBoundedJoin HistoryReadyTape

variable {W : ℕ} (u idx : ℕ) (archive : Archive) (family : Family) (m : Memory W)
local notation "A" => Physical.layout u archive family
local notation "cap" => family.childBound
local notation "T" => numInput A cap (numeric m)
local notation "X" => HistoryStageSetup.run A cap m
local notation "B" => HistoryStageBody.StageRun.compiled X
local notation "C" => HistoryStageRoot.childCount T (numeric m)
local notation "S₀" => Diagonal.TickWorkspace.stride u
local notation "V₀" => volume u
local notation "H" => HistoryStageBody.hub A
local notation "rootPtr" => HistoryStageRoot.ptr T (numeric m)
local notation "cache" => base u 13+8*idx
local notation "SnapshotAt" => Snapshot A cap T (numeric m)

variable {F : Type*} {n h p : ℕ} {arity : Fin n→ℕ}
    (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (tag : ((Fin 3→Bool)→F)→ℕ) (q : Fin n→HistoryJoinScan.Header ℕ)
local notation "ops" => Tape.tape (W:=W) N wire tag q
local notation "reached" => HistoryBoundedBody.Build.reached B ops

private theorem job_ranges (ranges : Ranges u idx archive family m N q) (j : Job W) (hj : j∈ops) :
    (base u 18+2≤j.start ∧ j.finish≤base u 19) ∨ j.finish≤base u 13 := by
  obtain ⟨i,_,mem⟩ := List.mem_flatMap.mp hj
  rcases (by simpa only [Tape.jobs,List.mem_cons,List.not_mem_nil,or_false] using mem :
    j=⟨(q i).pins,arity i,_⟩ ∨ j=⟨(q i).dest,4*(N i).cells,_⟩) with rfl|rfl
  · exact .inl (ranges.join.pins i)
  · exact .inr ((ranges.join.rows i).2.trans ranges.join.arena)

/-- The native join reads all six hub words, its actual matching child links
and the stored old results, after all selected map and relocation jobs. -/
theorem of_loaded (ranges : Ranges u idx archive family m N q)
    (cells : SourceCells A cap T (numeric m) W) (arityEq : n=C+1)
    (hubFit : ∀ j,(HistoryStageRoot.hub T (numeric m)).words j<2^W)
    (linkFit : ∀ i : Fin (C+1),∀ j,(HistoryStageRoot.link T (numeric m) i.val).words j<2^W)
    (result : (B).outputBase=bankBase A cap T .result)
    (loaded : Loaded (B).layout.commands ops (B).entered) : Build.Source B ops := by
  let sc := ranges.scalar
  have kfit (j : Fin (C+1)) := ranges.rootBelow j
  have bud : V₀+400+32*(cap+1)≤S₀ := ranges.join.scratch
  have count : C≤cap := ranges.join.childCount
  have big : 20*S₀<2^W := ranges.join.words
  have cached : 14*S₀+8*idx+8≤15*S₀ := ranges.join.cache
  have cacheAt : (B).outputBase=cache := by
    rw [result]; change base u 13+8*(T).id=_; rw [ranges.join.index]
  obtain ⟨inputSnap,seedSnap,cmdSnap,argSnap⟩ := ranges.inputSnapshots cells
  have keep (a : ℕ) (lo : H≤a) (hi : a<base u 18+2) : reached a=(B).entered a :=
    (B).prefix_keeps N wire tag q (List.finRange n) (ranges.protect lo hi)
  have snap : SnapshotAt reached := argSnap.transfer (by
    intro a member
    apply keep
    · cases member with
      | hub j => exact Nat.le_add_right ..
      | link i j => change 15*S₀+V₀+64+48≤15*S₀+V₀+64+55+_;omega
      | operand i j => change 15*S₀+V₀+64+48≤15*S₀+V₀+64+55+4*(cap+1)+_;omega
    · cases member with
      | hub j => have:=j.isLt;change 15*S₀+V₀+64+48+j.val<19*S₀+2;omega
      | link i j => have:=i.isLt;have:=j.isLt;change 15*S₀+V₀+64+55+(4*i.val+j.val)<19*S₀+2;omega
      | operand i j =>
        have row : i.val < C+1 := i.isLt
        have field : j.val < 5 := j.isLt
        change 15*S₀+V₀+64+55+4*(cap+1)+(5*i.val+j.val)<19*S₀+2
        omega)
  have reachedHub : readHub (B).layout (numeric reached)=(B).hub := snap.readHub (B).layout rfl hubFit
  have roots {mem : Memory W} (s : SnapshotAt mem) (i : Fin (B).hub.argc) :
      (child (B).hub (numeric mem) i.val).node=rootPtr i.val :=
    congrArg Child.node (s.readChild rfl i (linkFit i))
  have bounds {mem : Memory W} (s : SnapshotAt mem) (i : Fin (B).hub.argc) :
      (child (B).hub (numeric mem) i.val).node+3<2^W := by
    rw [roots s i]
    have b : rootPtr i.val+6≤14*S₀+8*idx := kfit i
    omega
  have mkFrame {mem : Memory W} (s : SnapshotAt mem) (lo len : ℕ)
      (metadata : lo+len≤H ∨ 16*S₀≤lo) (old : cache≤lo) : Frame (B).layout (B).hub mem lo len := by
    refine ⟨?_,?_,?_⟩
    · intro j
      have h:=j.isLt
      change 15*S₀+V₀+64+48+j.val<lo ∨ lo+len≤15*S₀+V₀+64+48+j.val
      change lo+len≤15*S₀+V₀+64+48 ∨ _ at metadata
      omega
    · intro i j
      have hi : i.val<C+1 := i.isLt
      have hj:=j.isLt
      change 15*S₀+V₀+64+55+4*i.val+j.val<lo ∨ lo+len≤15*S₀+V₀+64+55+4*i.val+j.val
      change lo+len≤15*S₀+V₀+64+48 ∨ _ at metadata
      omega
    · intro i j
      left; rw [roots s i]; have := kfit i; have := j.isLt; omega
  have frozen (a len : ℕ) (lo : base u 13≤a) (hi : a+len≤base u 18+2) : Away a len ops := by
    intro j hj
    rcases job_ranges u idx archive family m N wire tag q ranges j hj with span|endAt
    · exact .inr (hi.trans span.1)
    · exact .inl (endAt.trans lo)
  have cursor : reached (H+6)=(B).input (H+6) := by
    rw [keep _ (Nat.le_add_right ..) (by change 15*S₀+V₀+64+48+6<19*S₀+2;omega)]
    have out (lo len : ℕ) (word : ℕ→Word W) (mem : Memory W) (away : H+6<lo ∨ lo+len≤H+6) :
        fillSegment lo len word mem (H+6)=mem (H+6) :=
      ite_eq_right (by rcases away with h|h <;> omega)
    unfold Build.entered
    rw [out _ _ _ _ (Or.inl (by change 15*S₀+V₀+64+48+6<17*S₀;omega))]
    unfold Build.commands
    rw [out _ _ _ _ (Or.inl (by change 15*S₀+V₀+64+48+6<16*S₀;omega))]
    unfold Build.seeded
    exact out _ _ _ _ (Or.inr (by change 15*S₀+V₀+9≤15*S₀+V₀+64+48+6;omega))
  refine ⟨Nat.succ_le_succ count,sc.seedRoom,sc.hubRoom,.inr sc.seedHub,⟨sc.seedCommand,sc.commandArgs⟩,
    sc.commandRoom,sc.argRoom,(fun j=>inputSnap.hub_value j (hubFit j)),
    (fun j=>⟨seedSnap.hub_value j (hubFit j),cmdSnap.hub_value j (hubFit j)⟩),
    mkFrame seedSnap _ _ (.inr le_rfl) (by change 14*S₀+8*idx≤16*S₀;omega),
    mkFrame cmdSnap _ _ (.inr (by change 16*S₀≤17*S₀;omega)) (by change 14*S₀+8*idx≤17*S₀;omega),
    sc.wide,sc.capRoom,sc.linkRoom,(fun i=>⟨bounds seedSnap i,bounds cmdSnap i⟩),?_,?_,?_,loaded,?_,?_,?_,?_,?_⟩
  · rw [Tape.tape_length,arityEq]; rfl
  · exact ⟨frozen _ _ (by change 14*S₀≤15*S₀+V₀;omega) (by change 15*S₀+V₀+9≤19*S₀+2;omega),
      frozen _ _ (by change 14*S₀≤16*S₀;omega) (by change 16*S₀+14*(C+1)≤19*S₀+2;omega)⟩
  · intro j hj
    rcases job_ranges u idx archive family m N wire tag q ranges j hj with span|endAt
    · exact span.2.trans_lt ranges.join.words
    · change j.finish≤14*S₀ at endAt;omega
  · rw [cacheAt]; have := sc.cacheRoom; omega
  · rw [reachedHub,cacheAt]
    exact mkFrame snap _ _ (.inl (by change 14*S₀+8*idx+4≤15*S₀+V₀+64+48;omega)) le_rfl
  · exact congrArg Fin.val cursor
  · change (readHub (B).layout (numeric reached)).children+4*(readHub (B).layout (numeric reached)).argc≤2^W
    rw [reachedHub]; exact sc.linkRoom
  · change ∀ k : Fin (readHub (B).layout (numeric reached)).argc,
      (child (readHub (B).layout (numeric reached)) (numeric reached) k.val).node+3<2^W
    rw [reachedHub]; exact bounds snap


end ThreeFlat.RAM.HistoryStageSource

namespace ThreeFlat.RAM.HistoryStageSource
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.HistoryContraction Diagonal.TickWorkspace
open HistoryStageRoot HistoryStageBody HistoryStageSnapshots HistoryBoundedBody HistoryBoundedJoin
open HistoryPartyBatchExec HistoryStageRoot.Typed HistoryStageBody.Physical HistoryStageBankArena HistoryStageSetup
open scoped BigOperators Fin.CommRing
section
variable {F Pins : Type} [CommSemiring F] {U : Shape} {R : Rewrite U F} {t : Fin R.count}
  (L : PortLayout U Pins) (V : PortLayout (R.target t) Pins) (count : (R.target t).Site→ℕ)
  (order : ∀ v,Fin (count v)≃{x // R.owner t x=v}) (v : (R.target t).Site)
  (root : ∀ v,Tree F (L.hidden count order v+V.halfBits v))
  (ok : ∀ v (pin : Fin (L.hidden count order v+V.halfBits v)→Bool) x y,
    (∀ z a j,pin (L.stageOld V count order v z a j)=L.binary a.1.1 (x z a) j) →
    (∀ a j,pin (L.stageNew V count order v a j)=V.binary a.1.1 (y a) j) →
    (root v).compile.eval pin=R.kernel t v x y)
  (forest : Forest F L.form) {W : ℕ} (u idx : ℕ) (archive : Archive) (family : Family) (m : Memory W)
  (tag : ((Fin 3→Bool)→F)→ℕ)
local notation "A" => Physical.layout u archive family
local notation "cap" => family.childBound
local notation "T" => numInput A cap (numeric m)
set_option quotPrecheck false in
local notation "Y" => (HistoryStageSetup.run A cap m).compiled
local notation "st" => L.wordsStage V count order root ok
set_option quotPrecheck false in
local notation "ar" => (st).tapeArity forest v
set_option quotPrecheck false in
local notation "N" => fun i=>((st).tapeFactor forest v i).compile
set_option quotPrecheck false in
local notation "wire" => (st).tapePin forest v
local notation "q" => Typed.copy T (numeric m) N wire

local notation "old" => HistoryStageRoot.childCount T (numeric m)

theorem source (ports : HistoryStageRoot.Ports L V count order v T (numeric m))
    (stored : Typed.Stored L V count order v root forest T (numeric m) tag m)
    (ranges : Ranges u idx archive family m N q) (src : SourceCells A cap T (numeric m) W)
    (hubFit : ∀ j,(HistoryStageRoot.hub T (numeric m)).words j<2^W)
    (linkFit : ∀ i : Fin (old+1),∀ j,(HistoryStageRoot.link T (numeric m) i.val).words j<2^W) :
    HistoryBoundedBody.Build.Source Y (Tape.tape N wire tag q) := by
  have ix (i : Fin (count v+1)) : i.val<old+1 := by
    rw [ports.degree]
    exact i.isLt
  have childWord (i : Fin (count v+1)) := linkFit ⟨i.val,ix i⟩
  have cacheAt : (Y).outputBase=bankBase A cap T .result := by
    have small := ranges.scalar
    apply HistoryStageResult.compiled_base A cap m src ranges.join.childCount (by have:=small.wide;omega)
    · change base u 13+8*(T).id<2^W;rw [ranges.join.index];have:=small.cacheRoom;omega
    · have right : loc A 22<2^W := by
        have bud:=ranges.join.scratch;have word:=ranges.join.words
        change 20*Diagonal.TickWorkspace.stride u<2^W at word;change 15*Diagonal.TickWorkspace.stride u+volume u+64+22<2^W;omega
      rw [Fin.val_cast_of_lt right]
      change (A).party.seed+64+48+6≠(A).party.seed+64+22;omega
    · apply HistoryStageResult.endpoints_outside _ _ (.inr ?_)
      have upper : Endpoints.toAddr T (numeric m) old≤base u 13 := ranges.endpoints.trans ranges.extEnd
      exact upper.trans (by change 14*Diagonal.TickWorkspace.stride u≤15*Diagonal.TickWorkspace.stride u+volume u+64+48+6;omega)
  have rd := HistoryStageBankWords.read_words L V count order v A cap m ports (Y).seeded
    (ranges.inputSnapshots src).2.1 (ranges.cacheInfo src).2.1 childWord
  exact of_loaded u idx archive family m N wire tag q ranges src
    (show count v+1=old+1 from congrArg (fun k : ℕ=>k+1) ports.degree.symm) hubFit linkFit cacheAt
    (HistoryStageBankWords.loaded L V count order v root ok forest A cap m tag ports stored rd
      (Or.inl ranges.scalar.commandArgs))

end


end ThreeFlat.RAM.HistoryStageSource

end
end OAI
