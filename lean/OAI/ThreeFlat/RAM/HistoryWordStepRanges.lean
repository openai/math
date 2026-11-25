import OAI.ThreeFlat.RAM.HistoryWordStepResult
import OAI.ThreeFlat.RAM.HistoryWordStepStored
import OAI.ThreeFlat.RAM.HistoryStageBankArena

namespace OAI
/-! # Chronological S12/S13 region bounds of the actual selected word stage -/
namespace ThreeFlat.RAM.HistoryWordStepRanges
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.HistoryContraction Diagonal.PhysicalStage Diagonal.TickWorkspace
open HistoryStageRoot HistoryStageBody HistoryStageSetup HistoryStageSnapshots
open HistoryPartyBatchExec HistoryStageBody.Physical HistoryStageBankArena HistoryBoundedBody
open NavigationNodeRows
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pins E : Type} [Field F] {d l D lanes W : ℕ} {S : State d l} {R : Move F S D lanes}
  {branch : Fin R.rules.count} (L : S.Words Pins) (step : R.WordStep Pins L branch)
  {old : S.ArchiveSites} {charge : (R.next branch).Site→ℕ} (record : R.ArchiveStep branch old charge)
  (v : (R.next branch).Site) (u seedCount : ℕ) (bank : Archive) (family : Family) (m : Memory W)
  (trees : Forest F L.ports.form) (orig : ∀ x,Fin (L.ext x)→E) (pointer : E→ℕ) (tag : ((Fin 3→Bool)→F)→ℕ)
local notation "A" => Physical.layout u bank family
local notation "C" => family.childBound
local notation "V" => volume u
local notation "T" => numInput A C (numeric m)
local notation "X" => HistoryStageSetup.run A C m
local notation "B" => (X).compiled
local notation "z" => Move.WordStep.targetSite (R:=R) (i:=branch) v
local notation "D₀" => step.stage
local notation "N" => fun k=>((D₀).tapeFactor trees z k).compile
local notation "ar" => (D₀).tapeArity trees z
local notation "wire" => (D₀).tapePin trees z
local notation "q" => Typed.copy T (numeric m) N wire
local notation "ops" => Tape.tape («W»:=W) N wire tag q
local notation "produced" => adjust A C T .result ((B).output ops)
local notation "Y" => childCount T (numeric m)
local notation "idx" => record.sites.id v
local notation "target" => NodeValue.ofSite (Run.nodeOfSite step.words (step.nextForest trees)
  (Run.pushedOrigin step orig) v) pointer (T).stream (T).ext

/-- The peak resource estimate for the actual new forest bounds the true
tape's pin allocation, factor stream, individual encoded bit references,
and assembled number of hidden bits. -/
theorem tape_fits (charged : 4*(step.nextForest trees v).resources≤V) (word : 2+V<2^W) :
    (∑ k,ar k)≤V ∧ 4*(∑ k,(N k).cells)≤V ∧
    (∀ k,2+ar k+(N k).internal<2^W) ∧ ((D₀).assemble trees z).compile.internal<2^W := by
  rw [←HistoryWordStepResult.resource_eq step trees v] at charged
  let assembled:=(D₀).assemble trees z
  have maps : (∑ k,ar k)≤assembled.footprint.pins:=by
    change _≤(∑ k,((D₀).tapeFactor trees z k).footprint.pins)+(∑ k,ar k)
    exact Nat.le_add_left _ _
  have rows : (∑ k,(N k).cells)=assembled.rows:=by
    change _=∑ k,((D₀).tapeFactor trees z k).rows
    simp only [Tree.compiled_rows]
  have bits : (∑ k,(N k).internal)≤assembled.bits:=by
    simp only [Tree.compiled_bits]
    change _≤(D₀).hidden z+∑ k,((D₀).tapeFactor trees z k).bits
    exact Nat.le_add_left _ _
  change 4*assembled.resources≤V at charged
  unfold Tree.resources Stage.treeWork at charged
  refine ⟨by omega,by rw [rows];omega,?_,?_⟩
  · intro k
    have a : ar k≤∑ j,ar j := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
    have b : (N k).internal≤∑ j,(N j).internal :=
      Finset.single_le_sum (f := fun j => (N j).internal) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
    omega
  · change assembled.compile.internal<2^W
    rw [Tree.compiled_bits]
    omega

/-- Each old site's external endpoint count also fits in this stage's
slab, including when no old-site price has been extracted separately. -/
theorem child_external (charged : 4*(step.nextForest trees v).resources≤V) (word : 2+V<2^W)
    (k : Fin ((D₀).count z)) : L.ext ((D₀).child z k).val≤V := by
  have h : ar k.succ≤∑ t,ar t :=
    Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ k.succ)
  have all := (tape_fits (L:=L) (step:=step) (v:=v) (u:=u) (trees:=trees) charged word).1
  change L.ext ((D₀).child z k).val+L.ports.halfBits ((D₀).child z k).val≤_ at h
  omega

/-- Public S12/S13 allocation fits at the actual word size of the diagonal
evaluator for every selected chronological index below the S44 volume. -/
theorem scale {u «idx» cap : ℕ} (age : 40≤u) (nSmall : «idx»<(volume u)^2) (capSmall : cap≤volume u) :
    162≤volume u ∧ volume u+400+32*(cap+1)≤Diagonal.TickWorkspace.stride u ∧
    base u 12+(«idx»+1)*(volume u)^2≤base u 13 ∧ base u 13+8*«idx»+8≤base u 14 ∧
    base u 19<2^(16*u^10) := by
  let vol:=volume u
  have big : 2^8≤vol:=Nat.pow_le_pow_right (by decide) ((by omega : 8≤u).trans
    (Nat.le_self_pow (by decide : 10≠0) _))
  have enough : 162≤vol:=by norm_num at big;omega
  have sq : 64*vol≤vol^2:=by rw [pow_two];exact Nat.mul_le_mul_right _ (by omega)
  have fourth : 8*vol^2≤Diagonal.TickWorkspace.stride u:=by
    change 8*vol^2≤vol^4
    calc
      _≤vol^2*vol^2:=Nat.mul_le_mul_right _ (by omega)
      _=_:=by ring
  have slab : («idx»+1)*vol^2≤Diagonal.TickWorkspace.stride u:=by
    change («idx»+1)*vol^2≤vol^4
    calc
      _≤vol^2*vol^2:=Nat.mul_le_mul_right _ nSmall
      _=_:=by ring
  have headroom : 19 < Diagonal.TickWorkspace.stride u := by omega
  have room := Diagonal.TickWorkspace.word_space (u:=u) (i:=19) (by omega) headroom
  refine ⟨enough,?_,?_,?_,by omega⟩
  · change vol+400+32*(cap+1)≤Diagonal.TickWorkspace.stride u;change cap≤vol at capSmall;omega
  · change 13*Diagonal.TickWorkspace.stride u+(«idx»+1)*vol^2≤14*Diagonal.TickWorkspace.stride u;omega
  · change 14*Diagonal.TickWorkspace.stride u+8*«idx»+8≤15*Diagonal.TickWorkspace.stride u;change «idx»<vol^2 at nSmall;omega

/-- The original external headers and the actual earlier selected cache rows determine
the two disjoint read intervals. Only the kernel operation on this node has a new
source: its published stream is in bank zero of the selected motif. -/
theorem of_children (order : step.ChildOrder record) (index : (T).id=idx)
    (b : Banks) (directory : DirectoryRow b record.sites.layer (record.sites.ord v) m)
    (source : record.data.Reads (numeric m)) (nodes : b.nodes=base u 44)
    (countRoom : record.sites.layer.childCount<2^W)
    (listRoom : record.sites.layer.children+(record.sites.ord v).val*record.sites.layer.childCount<2^W)
    (child : ∀ k : Fin record.sites.layer.childCount,let id:=record.data.child (record.sites.ord v) k
      (NodeValue.ofSite (Run.nodeOfSite L trees orig (record.row.children v k).val) pointer
        (streamAt u seedCount id) (endsAt u seedCount id)).Cached tag u id m)
    (rootStream : (atResult (numeric m) (T).kernel).stream=kernelBase u idx family 0)
    (rootPins : (atResult (numeric m) (T).kernel).pins=(D₀).rootWidth z)
    (cap : Y≤C) (large : 162≤V)
    (scratch : V+400+32*(C+1) ≤ Diagonal.TickWorkspace.stride u) (arena : base u 12+(idx+1)*V^2≤base u 13)
    (cache : base u 13+8*idx+8≤base u 14) (words : base u 19<2^W)
    (capacity : (family.motifs+2)*(family.parties+2)*8*32≤V)
    (refresh : ∀ x y n,family.mode=.refresh x y n→0<family.motifs)
    (exts : step.words.ext v≤V) (pins : (∑ k,ar k)≤V) (rows : 4*(∑ k,(N k).cells)≤V) :
    Ranges u idx bank family m N q := by
  let raw:=numeric m
  let id:=record.data.child (record.sites.ord v)
  obtain ⟨degree,actual⟩:=recorded_child_addresses T m b record.data (record.sites.ord v)
    directory source index nodes.symm countRoom listRoom
  have size:=step.count_eq record v
  have smaller (k : Fin record.sites.layer.childCount) : id k < idx:=by
    have iLt:=(old.ord (record.row.children v k).val).isLt
    have seq:=record.row.contiguous
    have atOld:=record.row.childId v k;change id k=old.layer.first+_ at atOld
    change id k<record.sites.layer.first+_;omega
  have parent (k : Fin ((D₀).count z)) :
      let site:=((D₀).child z k).val
      let ptr:=childPtr T raw k.val
      (atResult raw ptr).pins=L.ports.form.width site ∧ (atResult raw ptr).extCount=L.ext site ∧
      (atResult raw ptr).stream=streamAt u seedCount (id (k.cast size.symm)) := by
    let j:=k.cast size.symm
    have addr:=actual j
    have h:=(child j).header
    change atResult raw (base u 13+8*id j)=
      ⟨streamAt u seedCount (id j),L.ports.form.width (record.row.children v j).val,
        (trees (record.row.children v j).val).compile.cells,(trees (record.row.children v j).val).compile.internal,
        endsAt u seedCount (id j),L.ext (record.row.children v j).val⟩ at h
    have c : (record.row.children v j).val=((D₀).child z k).val:=order v j
    rw [c] at h
    dsimp only
    rw [show childPtr T raw k.val=base u 13+8*id j from addr,h]
    exact ⟨rfl,rfl,rfl⟩
  have total : HistoryStageRoot.prefix T raw Y Result.extCount≤V:=by
    rw [degree,size]
    rw [prefix_value («T»:=T) (m:=raw) Result.extCount (fun k=>L.ext ((D₀).child z k).val) (fun k=>(parent k).2.1)
      ((D₀).count z) le_rfl]
    have e:=(step.originOrder v).choose
    change step.words.ext v=∑ k,L.ext ((D₀).child z k).val at e
    simpa only [e, Fin.castLE_refl] using exts
  have pinAt (k : Fin ((D₀).count z+1)) : (q k).pins=(T).maps+Tree.before ar k:=by
    refine Fin.cases ?_ (fun j=>?_) k
    · simp [Typed.copy,mapPtr,Tree.before]
    · change (T).maps+(atResult raw (T).kernel).pins+HistoryStageRoot.prefix T raw j.val Result.pins=
        (T).maps+∑ t : Fin (j.val+1),ar (Fin.castLE j.succ.isLt.le t)
      rw [Fin.sum_univ_succ,rootPins,Nat.add_assoc]
      congr 2
      exact prefix_value («T»:=T) (m:=raw) Result.pins (fun i=>L.ports.form.width ((D₀).child z i).val)
        (fun i=>(parent i).1) _ j.isLt.le
  have jo:=JoinRanges.of_layout u idx bank family m N q index cap large scratch arena cache words
    total pins rows pinAt (fun _=>rfl)
  apply Ranges.of_sectors u idx bank family m N q jo large capacity refresh ?_ total rows (fun _=>rfl) ?_ ?_
  · intro k hk;let j : Fin record.sites.layer.childCount:=⟨k,by rw [←degree];exact hk⟩
    have address:=actual j
    change (T).resultBase+8*raw (raw (HistoryStageRoot.node T+3)+k)=(T).resultBase+8*id j at address
    have decoded : raw (raw (HistoryStageRoot.node T+3)+k)=id j :=
      Nat.mul_left_cancel (by decide : 0<8) (Nat.add_left_cancel address)
    exact decoded.le.trans_lt (smaller j)
  · intro k hz
    have readPtr : HistoryStageRoot.ptr T raw k.val=(T).kernel := ite_eq_left hz
    exact (congrArg (fun a=>(atResult raw a).stream) readPtr).trans rootStream
  · intro k
    refine Fin.cases (by simp) (fun j _=>?_) k
    have readPtr : HistoryStageRoot.ptr T raw (j.val+1)=childPtr T raw j.val := by
      simp only [HistoryStageRoot.ptr,Nat.add_one_ne_zero,ite_false,Nat.add_one_sub_one]
    have src := (congrArg (fun a=>(atResult raw a).stream) readPtr).trans (parent j).2.2
    have bounded : 4*(trees ((D₀).child z j).val).compile.cells≤V:=
      (Nat.mul_le_mul_left 4 (Finset.single_le_sum (f:=fun k=>(N k).cells) (fun _ _=>Nat.zero_le _)
        (Finset.mem_univ j.succ))).trans rows
    have limits:=address_limits (u:=u) (seedCount:=seedCount) (i:=id (j.cast size.symm))
      (rows:=(trees ((D₀).child z j).val).compile.cells) (ext:=0) large bounded (Nat.zero_le _)
    have before := previous_stream_before u idx (smaller (j.cast size.symm))
      (limits.2.1.trans (by simpa only [Nat.add_zero] using limits.2.2))
    exact (Nat.add_le_add_right src.le _).trans before





end
end ThreeFlat.RAM.HistoryWordStepRanges

end OAI
