import OAI.Hierarchy.ProtocolRAMRankGather
import OAI.Hierarchy.TaggedShorterCommonScan

namespace OAI
/-! # Native weighted common-port ranks in the new supergroup numbering -/

namespace Hierarchy.ProtocolRAMPackedCommon

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM ProtocolRAMRankGather TaggedShorterCommonScan
open scoped BigOperators Fin.CommRing

variable {W N bins : ℕ}

def inputBanks (weights keys : Bank) : Columns := ⟨.row,weights,keys⟩

def program (W N bins scratch src groupKeys counters dst : ℕ) (banks : Columns) :=
  ((ProtocolRAMRankGather.program W N scratch src groupKeys banks fields).seq
    (ProtocolRAM.scan W counters bins (.lit 0))).seq
    (TaggedShorterCommonScan.procedure W src groupKeys counters dst N)

def clock (N bins src groupKeys : ℕ) (banks : Columns) :=
  (ProtocolRAMRankGather.work N src groupKeys banks fields+(4+6*bins))+(6+23*N)

theorem run_counts (scratch src groupKeys counters dst : ℕ) (weights keys : Bank) (key : Fin N→Fin bins)
    (width : Fin N→ℕ) (m : Memory W)
    (fit : Fits (inputBanks weights keys) W N scratch src groupKeys)
    (groupsLow : groupKeys+4*N ≤ counters) (countsLow : counters+bins ≤ dst) (endFits : dst+4*N<2^W)
    (weightRead : ∀i : Fin N,m (weights.base+i.val)=(width i:Word W))
    (keyRead : ∀i : Fin N,m (keys.base+i.val)=((key i).val:Word W)) :
    ∃ out,(program W N bins scratch src groupKeys counters dst (inputBanks weights keys)).Exec m out
      (clock N bins src groupKeys (inputBanks weights keys)) ∧
      (∀i : Fin N,out (dst+4*i.val+3)=(earlier key width i.val (key i):Word W)) ∧
      (∀ a < scratch,out a=m a) ∧
      ∀e : Fin bins,out (counters+e.val)=((∑i : Fin N, if key i=e then width i else 0 : ℕ):Word W) := by
  let banks := inputBanks weights keys
  let g := ProtocolRAMRankGather.image scratch src groupKeys banks id key width m fields
  let blank := fillSegment counters bins (fun _=>(0:Word W)) g
  let out := TaggedShorterCommonScan.image src groupKeys counters dst N blank
  have loaded : Loaded banks id key width m := ⟨fun _=>rfl,weightRead,keyRead⟩
  have gate : (ProtocolRAMRankGather.program W N scratch src groupKeys banks fields).Exec m g
      (ProtocolRAMRankGather.work N src groupKeys banks fields) := ProtocolRAMRankGather.run fit id key width m loaded fields
  have clear : (scan W counters bins (.lit 0)).Exec g blank (4+6*bins) := by
    have timing : 4+6*bins=4+bins*(2*(Expr.lit 0).work+4) := by change 4+6*bins=4+bins*6;omega
    rw [timing]
    intro P R K machine pc reg pub exit installed values cfg raw start same
    exact scan_exec counters bins (.lit 0) g trivial (by omega) machine pc reg pub exit installed values cfg raw start same
  have lo1 := fit.start
  have lo2 := fit.sep
  have data (f : ProtocolRAMRankGather.Field) (i : Fin N) : blank (address src groupKeys f i.val)=value id key width f i := by
    have small : address src groupKeys f i.val < counters := by
      have := i.isLt
      cases f <;> simp only [address] <;> omega
    rw [show blank (address src groupKeys f i.val)=g (address src groupKeys f i.val) from
      (by simp [blank,fillSegment,not_le.mpr small])]
    exact ProtocolRAMRankGather.read fit id key width m fields (by cases f <;> simp [fields]) i
  have ready : TaggedShorterCommonScan.Input src groupKeys counters id key width blank := by
    refine ⟨fun i=>⟨data .rowID i,data .zero i,data .weight i⟩,data .key,fun x=>?_⟩
    have := x.isLt
    simp [blank,fillSegment,show counters+x.val < counters+bins by omega]
  have second : (TaggedShorterCommonScan.procedure W src groupKeys counters dst N).Exec blank out (6+23*N) :=
    TaggedShorterCommonScan.run src groupKeys counters dst N blank (by omega)
  obtain ⟨ranks,frame⟩ := TaggedShorterCommonScan.read_frame src groupKeys counters dst id key width blank
    (by omega) groupsLow countsLow endFits ready
  refine ⟨out,?_,ranks,?_,?_⟩
  · have first : ((ProtocolRAMRankGather.program W N scratch src groupKeys banks fields).seq
        (scan W counters bins (.lit 0))).Exec m blank
        (ProtocolRAMRankGather.work N src groupKeys banks fields+(4+6*bins)) := Procedure.Exec.then gate clear
    intro P R K mach pc reg pub exit installed vals cfg raw entry eq
    exact Procedure.Exec.then first second mach pc reg pub exit installed vals cfg raw entry eq
  · intro a ha
    have low : a < counters := by omega
    change TaggedShorterCommonScan.image _ _ _ _ _ _ _=_
    rw [frame a (.inl low) (.inl (by omega))]
    change fillSegment counters bins _ g a=_
    rw [fillSegment,ite_eq_right (by omega)]
    exact ProtocolRAMRankGather.below fit id key width m fields a ha
  · exact TaggedShorterCommonScan.totals src groupKeys counters dst id key width blank
      (by omega) groupsLow countsLow endFits ready

theorem run (scratch src groupKeys counters dst : ℕ) (weights keys : Bank) (key : Fin N→Fin bins)
    (width : Fin N→ℕ) (m : Memory W)
    (fit : Fits (inputBanks weights keys) W N scratch src groupKeys)
    (groupsLow : groupKeys+4*N ≤ counters) (countsLow : counters+bins ≤ dst) (endFits : dst+4*N<2^W)
    (weightRead : ∀i : Fin N,m (weights.base+i.val)=(width i:Word W))
    (keyRead : ∀i : Fin N,m (keys.base+i.val)=((key i).val:Word W)) :
    ∃ out,(program W N bins scratch src groupKeys counters dst (inputBanks weights keys)).Exec m out
      (clock N bins src groupKeys (inputBanks weights keys)) ∧
      (∀i : Fin N,out (dst+4*i.val+3)=(earlier key width i.val (key i):Word W)) ∧
      ∀ a < scratch,out a=m a := by
  obtain ⟨out,exec,offset,frame,_⟩ := run_counts scratch src groupKeys counters dst weights keys key width m
    fit groupsLow countsLow endFits weightRead keyRead
  exact ⟨out,exec,offset,frame⟩

end Hierarchy.ProtocolRAMPackedCommon

end OAI
