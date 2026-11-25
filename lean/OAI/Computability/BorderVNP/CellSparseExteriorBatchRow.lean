import OAI.Computability.BorderVNP.CellSparseExteriorBatch

/-! # Physical operands and publication for one genuine owned RLE task row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open VPVNP.BurstRAM CellPacketEncode

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- The three frame operands and seven indirect controls read by the native entry. -/
structure Layout.Loaded (l : Layout) (m : ℕ → ℕ) : Prop where
  count : m (l.frame+90)=l.count
  tasks : m (l.frame+89)=l.tasks
  control : m (l.frame+92)=l.control
  six : m (l.control+17)=l.six
  pairs : m (l.control+31)=l.pairs
  triples : m (l.control+32)=l.triples
  compact : m (l.control+34)=l.compact
  stride : m (l.control+35)=l.stride
  counts : m (l.control+36)=l.counts

open private controlWord from OAI.Computability.BorderVNP.CellSparseExteriorBatch

set_option maxRecDepth 6000 in
/-- Load the installed public controls, including the actual returned owned count. -/
theorem setup_run (s : Bank w) (m : Memory w) (l : Layout) (fp : (pub 0).val=l.frame)
    (loaded : l.Loaded (readings m)) (frame : l.frame+92 < 2^w) (header : l.control+36 < 2^w) :
    ∃ es t, Runs pub mac setup s m es t m ∧ traceCost es ≤ setup.slots ∧ l.Ready 0 (readings t) := by
  obtain ⟨count,table,ctl,six,pairs,triples,compressed,stride,counts⟩ := loaded
  change readings pub 0=l.frame at fp
  have positive : w≠0 := by rintro rfl; simp at frame
  have safe : setup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [setup,controlWord,readFrame,Code.block,Code.safeReadOnly,Code.evalNat,
      addressOpFits,addressOp,fp,ctl,positive]
    omega
  obtain ⟨es,t,run,hc,regs⟩ := setup.runReadOnly pub mac m s safe
  refine ⟨_,_,run,hc,?_⟩
  simp (config := {decide := true}) [Layout.Ready,regs,setup,controlWord,readFrame,Code.block,Code.evalNat,
    addressOp,fp,ctl,count,table,six,pairs,triples,compressed,stride,counts]

set_option maxRecDepth 6000 in
/-- Read the global cell ID, true pair-directory endpoints, dense supplied extent
and report tail from the two physical source tables. -/
theorem readOwned_run (s : Bank w) (m : Memory w) (l : Layout) (o : Owned) (i : ℕ)
    (ready : l.Ready i (readings s)) (input : o.Stored l i (readings m)) (room : o.Fits l i w) :
    ∃ es t, Runs pub mac readOwned s m es t m ∧ traceCost es ≤ readOwned.slots ∧ o.Ready l i (readings t) := by
  obtain ⟨count,tasks,six,pairs,triples,compact,stride,counts,cursor,one⟩ := ready
  obtain ⟨number,width,base,size,start,spans⟩ := input
  obtain ⟨constants,header,task,pair,ends,tail,output,counter,advance⟩ := room
  unfold Owned.dest at output
  have endEq : l.triples+o.first*3+o.field.spans.length*3=l.triples+3*(o.first+o.field.spans.length) := by ring
  have safe : readOwned.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [readOwned,Code.block,Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,
      tasks,six,pairs,triples,compact,stride,counts,cursor,one,Nat.mul_comm i 6,Nat.mul_comm i 7,
      number,width,base,size,start,spans,Nat.mul_comm o.global 2,Nat.mul_comm o.first 3,
      Nat.mul_comm o.field.spans.length 3]
    omega
  obtain ⟨es,t,run,hc,regs⟩ := readOwned.runReadOnly pub mac m s safe
  refine ⟨_,_,run,hc,?_⟩
  simp (config := {decide := true}) [Owned.Ready,Layout.Ready,Owned.dest,regs,readOwned,Code.block,Code.evalNat,addressOp,
    count,tasks,six,pairs,triples,compact,stride,counts,cursor,one,Nat.mul_comm i 6,Nat.mul_comm i 7,
    number,width,base,size,start,spans,Nat.mul_comm o.global 2,Nat.mul_comm o.first 3,
    Nat.mul_comm o.field.spans.length 3,Nat.mul_add]
  omega

set_option maxRecDepth 6000 in
/-- Both compact task fields and the true encoded count are published. -/
theorem publish_run (s : Bank w) (m : Memory w) (l : Layout) (o : Owned) (i : ℕ)
    (ready : l.Ready i (readings s)) (task : readings s 49=l.tasks+7*i+2)
    (dest : readings s 51=o.dest l) (counter : readings s 52=l.counts+o.global)
    (cursor : readings s 20=o.dest l+o.field.bytes.length) (room : o.Fits l i w) :
    BoundedRun pub mac publish s m publish.slots (fun z =>
      l.Ready (i+1) z.reg ∧ z.mem=Function.update (Function.update (Function.update (readings m)
        (l.tasks+7*i+2) (o.dest l)) (l.tasks+7*i+3) o.field.bytes.length) (l.counts+o.global) o.field.bytes.length) := by
  obtain ⟨count,tasks,six,pairs,triples,compact,stride,counts,index,one⟩ := ready
  have taskFit := room.task
  have inc := room.advance
  have safe : publish.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [publish,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,
      NatState.ofWords,addressOp,addressOpFits,task,cursor,dest,index,one]
    omega
  apply (publish.runFixed pub mac s m safe).mono le_rfl
  rintro z rfl
  simp (config := {decide := true}) [Layout.Ready,publish,Code.block,Code.fixedEval,Code.evalNat,
    NatState.ofWords,addressOp,count,tasks,six,pairs,triples,compact,stride,counts,index,one,task,cursor,dest,counter]

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
