import OAI.ThreeFlat.RAM.HistorySelectedFrame
import OAI.ThreeFlat.RAM.HistoryStageSnapshots

namespace OAI
/-! # Fixed addresses and prior stream intervals during the selected history join -/
namespace ThreeFlat.RAM.HistoryStageBankArena
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickWorkspace
open HistoryStageRoot HistoryStageBody HistoryStageSetup HistoryStageResult HistoryStageSnapshots
open HistoryPartyBatchExec HistoryBoundedBody HistoryReadyTape HistoryStageBody.Physical
open scoped BigOperators Fin.CommRing
noncomputable section
variable {W : ℕ} (u idx : ℕ) (archive : Archive) (family : Family) (m : Memory W)
local notation "A" => Physical.layout u archive family
local notation "cap" => family.childBound
local notation "T" => numInput A cap (numeric m)
local notation "X" => HistoryStageSetup.run A cap m
set_option quotPrecheck false in
local notation "B" => (X).compiled
local notation "Y" => HistoryStageRoot.childCount T (numeric m)
local notation "S" => Diagonal.TickWorkspace.stride u
local notation "V" => volume u
variable {F : Type*} {n : ℕ} {ar : Fin n→ℕ} (N : ∀ k,BitNetwork F (ar k))
    (q : Fin n→HistoryJoinScan.Header ℕ)

/-- Sector bounds of the real root and old child rows. A refresh root may be
located after the endpoint and output sectors in the current node. -/
structure Ranges : Prop where
  join : JoinRanges u idx archive family m N q
  endpoints : Endpoints.toAddr T (numeric m) Y≤(T).ext+V
  dest : ∀ k,(T).stream≤(q k).dest ∧ (q k).dest+4*(N k).cells≤(T).ext
  extEnd : (T).ext+V≤base u 13
  rootBelow : ∀ k : Fin (Y+1),ptr T (numeric m) k.val+6≤base u 13+8*idx
  rootSep : ∀ k : Fin (Y+1),ptr T (numeric m) k.val+6≤(T).stream ∨ (T).ext+V≤ptr T (numeric m) k.val
  rowLimit : ∀ k,(q k).source+4*(N k).cells≤base u 13
  rowSep : ∀ k,(q k).source+4*(N k).cells≤(T).stream ∨ (T).ext+V≤(q k).source

/-- Numeric bounds for the actual fixed banks, with the scratch geometry independent
of any guess and the argc obtained from the compact node. -/
structure Scalars : Prop where
  wide : 14<2^W
  capRoom : cap+1≤2^W
  cursor : (B).control.val=(A).party.seed+7
  seedRoom : (A).party.seed+9<2^W
  hubRoom : HistoryStageBody.hub A+7<2^W
  seedHub : (A).party.seed+9≤HistoryStageBody.hub A
  seedCommand : (A).party.seed+9≤(A).party.commands
  commandArgs : (A).party.commands+14*(Y+1)≤(T).copyArguments
  argRoom : (T).copyArguments+7*(Y+1)<2^W
  commandRoom : (A).party.commands+14*(Y+1)<2^W
  linkRoom : (T).links+4*(Y+1)≤2^W
  mapRoom : mapArgs A cap+5*(Y+1)≤2^W
  cacheRoom : base u 13+8*idx+6<2^W

/-- Numerical specialization to the sector written by the actual shrink/refresh kernel
and to earlier S12 rows reached through S44. The only row layout inputs are the
literal kernel output pointer, the older cached ranges, and the typed row offsets. -/
theorem Ranges.of_sectors (r : JoinRanges u idx archive family m N q)
    (large : 162≤V) (capacity : (family.motifs+2)*(family.parties+2)*8*32≤V)
    (refresh : ∀ x y z,family.mode=.refresh x y z→0<family.motifs)
    (earlier : ∀ k,k<Y→numeric m (numeric m (HistoryStageRoot.node T+3)+k)< idx)
    (ends : HistoryStageRoot.prefix T (numeric m) Y Result.extCount≤V)
    (rows : 4*(∑ k,(N k).cells)≤V)
    (rowAt : ∀ k,(q k).dest=(T).stream+4*Diagonal.HistoryContraction.Tree.before (fun j=>(N j).cells) k)
    (kernel : ∀ k : Fin n,k.val=0→(q k).source=kernelBase u idx family 0)
    (old : ∀ k : Fin n,k.val≠0→(q k).source+4*(N k).cells≤base u 12+idx*V^2) :
    Ranges u idx archive family m N q := by
  let start:=base u 12+idx*V^2
  let stop:=base u 12+(idx+1)*V^2
  have bankSector (bank : ℕ) :
      HistoryScratch.sector family.motifs family.parties ⟨0,0,5,bank⟩=160+bank := by
    simp [HistoryScratch.sector]
  have stream : (T).stream=start+160*V := by
    change base u 12+((T).id*V+HistoryScratch.sector family.motifs family.parties ⟨0,0,5,0⟩)*V+0=_
    rw [bankSector,r.index]
    dsimp only [start]
    ring
  have ext : (T).ext=start+161*V := by
    change base u 12+((T).id*V+HistoryScratch.sector family.motifs family.parties ⟨0,0,5,1⟩)*V+0=_
    rw [bankSector,r.index]
    dsimp only [start]
    ring
  have sector : (T).ext+V≤ stop:=by rw [ext];dsimp [start,stop];nlinarith only [Nat.mul_le_mul_right V large]
  have c0:=kernel_sectors u idx archive family m r.index capacity refresh 0 (by decide)
  have c1:=kernel_sectors u idx archive family m r.index capacity refresh 1 (by decide)
  have kr:=kernel_pointer u idx archive family m r.index
  have endRoom : (T).ext+V≤base u 13:=sector.trans r.arena
  have info (k : Fin (Y+1)) : ptr T (numeric m) k.val+6≤base u 13+8*idx ∧
      (ptr T (numeric m) k.val+6≤(T).stream ∨ (T).ext+V≤ptr T (numeric m) k.val) := by
    by_cases h : k.val=0
    · simp only [HistoryStageRoot.ptr,ite_eq_left h,kr]
      exact ⟨by have b:=c1.2.1.trans r.arena;omega,by rcases c1.2.2 with a|b <;> omega⟩
    · simp only [HistoryStageRoot.ptr,ite_eq_right h]
      have smaller:=earlier (k.val-1) (by have:=k.isLt;omega)
      have upper:=previous_cache_before u idx archive family m r.index (k.val-1) smaller
      change _≤base u 13+8*(T).id at upper
      rw [r.index] at upper
      have lower : base u 13≤childPtr T (numeric m) (k.val-1):=Nat.le_add_right _ _
      exact ⟨upper,.inr (endRoom.trans lower)⟩
  have sources (k : Fin n) : (q k).source+4*(N k).cells≤base u 13 ∧
      ((q k).source+4*(N k).cells≤(T).stream ∨ (T).ext+V≤(q k).source) := by
    by_cases h : k.val=0
    · rw [kernel k h]
      have fit : 4*(N k).cells≤V:=(Nat.mul_le_mul_left 4 (Finset.single_le_sum (f:=fun j=>(N j).cells)
        (fun j _=>Nat.zero_le _) (Finset.mem_univ k))).trans rows
      have top:=c0.2.1.trans r.arena
      exact ⟨by omega,by rcases c0.2.2 with a|b <;> omega⟩
    · have a:=old k h
      have st : start≤(T).stream:=by rw [stream];omega
      have hi : start≤ stop:=by dsimp [start,stop];nlinarith only [Nat.zero_le (V^2)]
      exact ⟨a.trans (hi.trans r.arena),.inl (a.trans st)⟩
  refine ⟨r,by unfold Endpoints.toAddr;omega,?_,endRoom,fun k=>(info k).1,
    fun k=>(info k).2,fun k=>(sources k).1,fun k=>(sources k).2⟩
  intro k;rw [rowAt k]
  have next:=Nat.mul_le_mul_left 4 (Diagonal.HistoryContraction.Tree.prefix_next_le (fun j=>(N j).cells) k)
  rw [Nat.mul_add] at next
  rw [ext,stream]
  constructor <;> omega

variable {u idx archive family m N q}
theorem Ranges.scalar (r : Ranges u idx archive family m N q) : Scalars u idx archive family m := by
  have budget : V+400+32*(cap+1)≤S:=r.join.scratch
  have count:=r.join.childCount
  have limit : 20*S<2^W:=r.join.words
  have cache : 14*S+8*idx+8≤15*S:=r.join.cache
  have ctrl : (A).party.seed+7<2^W := by change 15*S+V+7<2^W;omega
  refine ⟨by omega,by omega,Fin.val_cast_of_lt ctrl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change 15*S+V+9<2^W;omega
  · change 15*S+V+64+48+7<2^W;omega
  · change 15*S+V+9≤15*S+V+64+48;omega
  · change 15*S+V+9≤16*S;omega
  · change 16*S+14*(Y+1)≤17*S;omega
  · change 17*S+7*(Y+1)<2^W;omega
  · change 16*S+14*(Y+1)<2^W;omega
  · change 15*S+V+64+55+4*(Y+1)≤2^W;omega
  · change 15*S+V+64+55+4*(cap+1)+5*(Y+1)≤2^W;omega
  · change 14*S+8*idx+6<2^W;omega

theorem Ranges.bootSpace (r : Ranges u idx archive family m N q) : BootSpace A cap m := by
  have budget : V+400+32*(cap+1)≤S:=r.join.scratch
  have word : 20*S<2^W:=r.join.words
  have ends : Endpoints.toAddr T (numeric m) Y≤14*S:=r.endpoints.trans r.extEnd
  apply BootSpace.of_intervals A cap m r.join.childCount
  · change 15*S+V+64+22<2^W;omega
  · left;change _≤15*S+V+64+48;omega
  · right;change 15*S+V+64+55+4*(cap+1)+5*(cap+1)≤16*S;omega
  · right;change 15*S+V+64+55+4*(cap+1)+5*(cap+1)≤17*S;omega

theorem Ranges.lowCell (r : Ranges u idx archive family m N q) {x : ℕ}
    (low : x<base u 14) (sep : x<(T).stream ∨ (T).ext+V≤x) :
    BootCell A cap m x := by
  have endAt:=r.endpoints
  have ordered : (T).stream≤(T).ext := by
    have sector (b : ℕ) : HistoryScratch.sector family.motifs family.parties ⟨0,0,5,b⟩=160+b := by
      simp [HistoryScratch.sector]
    change base u 12+((T).id*V+HistoryScratch.sector family.motifs family.parties ⟨0,0,5,0⟩)*V+0≤
      base u 12+((T).id*V+HistoryScratch.sector family.motifs family.parties ⟨0,0,5,1⟩)*V+0
    rw [sector,sector]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right V (Nat.add_le_add_left (by decide : 160+0≤160+1) _)) _
  have limit : 20*S<2^W:=r.join.words
  have bud : V+400+32*(cap+1)≤S:=r.join.scratch
  change x<15*S at low
  constructor
  · rw [Fin.val_cast_of_lt (show loc A 22<2^W by change 15*S+V+64+22<2^W;omega)]
    change x≠15*S+V+64+22;omega
  · rcases sep with h|h
    · exact .inl (h.trans_le ordered)
    · exact .inr (endAt.trans h)
  · left;change x<15*S+V;omega
  · left;change x<16*S;omega
  · left;change x<17*S;omega

theorem Ranges.rootCell (r : Ranges u idx archive family m N q) (k : Fin (Y+1)) (j : Fin 4) :
    BootCell A cap m (ptr T (numeric m) k.val+j.val) := by
  have b:=r.rootBelow k;have c:=r.join.cache;have h:=j.isLt;have s:=r.rootSep k
  apply r.lowCell <;> omega

theorem Ranges.inputSnapshots (r : Ranges u idx archive family m N q)
    (src : SourceCells A cap T (numeric m) W) :
    Snapshot A cap T (numeric m) (HistoryStageSetup.run A cap m).compiled.input ∧ Snapshot A cap T (numeric m) (HistoryStageSetup.run A cap m).compiled.seeded ∧
      Snapshot A cap T (numeric m) (HistoryStageSetup.run A cap m).compiled.commands ∧ Snapshot A cap T (numeric m) (HistoryStageSetup.run A cap m).compiled.entered :=
  snapshots A cap m src r.join.childCount r.bootSpace

theorem Ranges.cacheInfo (r : Ranges u idx archive family m N q)
    (src : SourceCells A cap T (numeric m) W) :
    CachedInfo T (numeric m) (HistoryStageSetup.run A cap m).compiled.input ∧ CachedInfo T (numeric m) (HistoryStageSetup.run A cap m).compiled.seeded ∧
      CachedInfo T (numeric m) (HistoryStageSetup.run A cap m).compiled.commands ∧ CachedInfo T (numeric m) (HistoryStageSetup.run A cap m).compiled.entered :=
  cache_infos A cap m src r.join.childCount r.rootCell

theorem Ranges.protect (r : Ranges u idx archive family m N q) {x : ℕ}
    (low : HistoryStageBody.hub A≤x) (high : x<base u 18+2) : (B).protectedAt N q x := by
  have cursor := r.scalar.cursor
  change (B).control.val=15*S+V+7 at cursor
  change 15*S+V+64+48≤x at low
  have old : base u 12+(idx+1)*V^2≤14*S:=r.join.arena
  refine ⟨by omega,fun k=>⟨.inl (high.trans_le (r.join.pins k).1),.inr ?_⟩⟩
  have hi:=(r.join.rows k).2;omega

theorem Ranges.rowProtected (r : Ranges u idx archive family m N q) (k : Fin n)
    (j : Fin (N k).cells) (c : Fin 4) : (B).protectedAt N q ((q k).source+(4*j.val+c.val)) := by
  let x:=(q k).source+(4*j.val+c.val)
  have lo : (q k).source≤x:=by dsimp [x];omega
  have hi : x<(q k).source+4*(N k).cells:=by dsimp [x];have:=j.isLt;have:=c.isLt;omega
  have b : x<14*S:=hi.trans_le (r.rowLimit k)
  have cur:=r.scalar.cursor;change (B).control.val=15*S+V+7 at cur
  refine ⟨by change x≠_;omega,fun z=>⟨.inl ?_,?_⟩⟩
  · have hp:=(r.join.pins z).1;change 19*S+2≤_ at hp;change x<_;omega
  · have sep:=r.rowSep k;have d:=r.dest z;change x<_ ∨ _≤x;omega

theorem Ranges.rowEntered (r : Ranges u idx archive family m N q) (src : SourceCells A cap T (numeric m) W)
    (k : Fin n) (j : Fin (N k).cells) (c : Fin 4) :
    (B).entered ((q k).source+(4*j.val+c.val))=m ((q k).source+(4*j.val+c.val)) := by
  let x:=(q k).source+(4*j.val+c.val)
  have lo : (q k).source≤x:=by dsimp [x];omega
  have hi : x<(q k).source+4*(N k).cells:=by dsimp [x];have:=j.isLt;have:=c.isLt;omega
  have b : x<14*S:=hi.trans_le (r.rowLimit k)
  have ksep:=r.rowSep k
  have cell:=r.lowCell (x:=x) (by change x<15*S;omega) (by omega)
  have first:=(boot_cell A cap m x cell).2.2.2
  have more:=(phase_frames A cap m r.join.childCount (src.node 4).2).2.2.2.2.2.2
  exact first.trans (more x (.inl (by change x<15*S+V+64+0;omega)))


end
end ThreeFlat.RAM.HistoryStageBankArena

end OAI
