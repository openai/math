import OAI.Computability.BorderVNP.RoutingISAFiniteScalarCall
import OAI.Computability.BorderVNP.RoutingISATypedBatchRow

/-! # Recovering the true finite-field subtotal suffix from a prepared task

The seven-word task identifies its cell by the stored call-row address. The team
loads this cell's actual report width and packs the last bits of the external bank
into its reusable scratch region.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FiniteScalarBatch

open VPVNP.BurstRAM Packing.Directory.ISA CellDispatch

/-- Address computation after loading the existing seven-word task. Registers 50,
51, and 52 contain the call-directory base, the actual-tail table base, and three. -/
def suffix : Code := .block [.binary .sub 15 46 50,.binary .div 15 15 52,.binary .add 15 51 15,
  .load 12 15,.binary .sub 13 5 12,.binary .add 3 4 13,.copy 4 12,.copy 5 6,.copy 2 40]

/-- The row preparation is a deterministic native read of the compact directory and
the actual tail-length column. -/
def locate : Code := .seq TypedBatch.fetch suffix

/-- Counted cursor advance after returning from fixed field macro one. -/
def advance : Code := .binary .add 43 43 47

/-- Complete instructions of one scalar row of the team. -/
def body : Code := .seq locate (.seq FiniteScalarCall.code advance)

/-- Retained task-table and tail-table registers at each row. -/
def Ready {w : ℕ} (table count calls tails i : ℕ) (s : Bank w) : Prop :=
  TypedBatch.Ready table count i s ∧ (s 50).val=calls ∧ (s 51).val=tails ∧ (s 52).val=3

/-- The source task has this global cell number and these bit-major claim values.
The preceding bits in the exterior bank are the canonical supplied ports. -/
structure Row where
  /-- Decoded seven-word task specifying the cell buffers and its call-directory address. -/
  task : TypedBatch.Task
  /-- Global cell index recovered from the call-row address to look up the report length. -/
  cell : ℕ
  /-- Supplied port bits that precede the report in the external bank. -/
  supplied : List Bool
  /-- Bit-major subtotal claims packed into scratch words for the scalar routine. -/
  claims : List Bool

/-- The actual report-bit source address. -/
def Row.src (r : Row) := r.task.cell.externalBase+r.supplied.length

/-- The packed report words delivered to the scalar routine. -/
def Row.words (r : Row) (w : ℕ) := CompactFrame.pack w r.claims

/-- The new memory consists of the original bank with the packed claims stored
in the task's existing reusable scratch interval. -/
def Row.image {w : ℕ} (r : Row) (m : Memory w) := putWords m r.task.cell.scratchBase (r.words w)

/-- Exact addressing and contents in the shared bank on entry to this scalar row. -/
structure Stored {w : ℕ} (r : Row) (m : Memory w) (table calls tails i : ℕ) : Prop where
  task : r.task.Stored m table i
  call : r.task.callRow=calls+3*r.cell
  tail : (m (tails+r.cell)).val=r.claims.length
  bank : r.task.cell.external=r.supplied++r.claims
  bits : CompactWrite.Source m r.src r.claims

/-- Word-range and disjointness conditions for the public tail read and packed scratch output. -/
structure Fits (r : Row) (w tails : ℕ) : Prop where
  index : tails+r.cell < 2^w
  start : r.src < 2^w
  source : r.src+r.claims.length ≤ 2^w
  dest : r.task.cell.scratchBase+(r.words w).length ≤ 2^w
  count : (r.words w).length < 2^w
  apart : CompactWrite.Disjoint r.src r.claims.length r.task.cell.scratchBase (r.words w).length

variable {w table count calls tails i : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

private theorem locate_run (r : Row) (s : Bank w) (m : Memory w) (ready : Ready table count calls tails i s)
    (stored : Stored r m table calls tails i) (fit : Fits r w tails) (hi : i < count) (space : table+7*count ≤ 2^w) :
    ∃ es t, Runs pub mac locate s m es t m ∧ traceCost es ≤ locate.slots ∧
      readings t 2=w ∧ readings t 3=r.src ∧ readings t 4=r.claims.length ∧ readings t 5=r.task.cell.scratchBase := by
  obtain ⟨fs,u,fetch,hf,kept,reg,cr⟩ := TypedBatch.fetch_run (pub:=pub) (macros:=mac) r.task s m ready.1 stored.task hi space
  have c0 : readings u 50 = calls := (congrArg Fin.val (fetch.keepsReg (by decide : TypedBatch.fetch.keeps 50=true))).trans ready.2.1
  have t0 : readings u 51 = tails := (congrArg Fin.val (fetch.keepsReg (by decide : TypedBatch.fetch.keeps 51=true))).trans ready.2.2.1
  have three : readings u 52 = 3 := (congrArg Fin.val (fetch.keepsReg (by decide : TypedBatch.fetch.keeps 52=true))).trans ready.2.2.2
  have addr : readings u 46 = calls+3*r.cell := cr.trans stored.call
  have width : readings u 40=w := kept.1
  have ext : readings u 5 = r.supplied.length+r.claims.length := reg.externalLength.trans (by rw [stored.bank,List.length_append])
  have tail : readings m (tails+r.cell) = r.claims.length := stored.tail
  have safe : suffix.safeReadOnly w (readings pub) (readings m) (readings u) := by
    simp (config := {decide := true}) [suffix,Code.block,Code.safeReadOnly,Code.evalNat,addressOp,addressOpFits,
      c0,t0,three,addr,ext,reg.externalBase,tail]
    exact ⟨fit.index,fit.start⟩
  obtain ⟨gs,t,run,hg,hreg⟩ := suffix.runReadOnly pub mac m u safe
  refine ⟨_,t,fetch.seq run,?_,?_⟩
  · rw [show traceCost (fs++gs) = traceCost fs + traceCost gs from VPVNP.RAMBuckets.cost_append ..]
    exact Nat.add_le_add hf hg
  · rw [hreg]
    simp (config := {decide := true}) [suffix,Code.block,Code.evalNat,addressOp,
      c0,t0,three,addr,ext,reg.externalBase,reg.scratch,tail,width,Row.src]

/-- Native tick allowance for this one local task, including its scalar burst read.
The outer loop guard is charged separately. -/
def Row.cost (r : Row) (w : ℕ) := locate.slots + CompactWrite.setup.slots + (CompactWrite.step.slots+1)*r.claims.length +
  2+FiniteScalarCall.count.slots+1+(r.words w).length+1

/-- Every returning path of this row has the same positive outer trace and scalar
burst. The exposed deterministic prefix and exact event support field reweighting. -/
theorem body_run (r : Row) (s : Bank w) (m : Memory w) (hw : 0 < w) (ready : Ready table count calls tails i s)
    (stored : Stored r m table calls tails i) (fit : Fits r w tails) (hi : i < count) (space : table+7*count ≤ 2^w)
    (scalar : ∀ bs, mac 1 (r.words w) bs = if bs.isEmpty then some .plus else none) :
    ∃ pre u t, Runs pub mac (.seq locate FiniteScalarCall.prepare) s m pre u (r.image m) ∧
      let es := pre ++ [FiniteScalarCall.event r.task.cell.scratchBase (r.words w),tick w]
      Runs pub mac body s m es t (r.image m) ∧ traceCost es ≤ r.cost w ∧ Ready table count calls tails (i+1) t ∧
      ∀ gs v mv, Runs pub mac body s m gs v mv → gs=es ∧ v=t ∧ mv=r.image m := by
  obtain ⟨fs,a,loc,hf,width,src,num,dest⟩ := locate_run (pub:=pub) (mac:=mac) r s m ready stored fit hi space
  obtain ⟨gs,u,prep,call,cost,unique⟩ := FiniteScalarCall.run (pub:=pub) (macros:=mac) a m r.claims hw
    width src num dest stored.bits fit.apart fit.source fit.dest fit.count scalar
  have prior := loc.seq call
  have live : Ready table count calls tails i u := by
    simp only [Ready,TypedBatch.Ready,prior.keepsReg (by decide : (locate.seq FiniteScalarCall.code).keeps 40=true),
      prior.keepsReg (by decide : (locate.seq FiniteScalarCall.code).keeps 41=true),
      prior.keepsReg (by decide : (locate.seq FiniteScalarCall.code).keeps 42=true),
      prior.keepsReg (by decide : (locate.seq FiniteScalarCall.code).keeps 43=true),
      prior.keepsReg (by decide : (locate.seq FiniteScalarCall.code).keeps 44=true),
      prior.keepsReg (by decide : (locate.seq FiniteScalarCall.code).keeps 47=true),
      prior.keepsReg (by decide : (locate.seq FiniteScalarCall.code).keeps 50=true),
      prior.keepsReg (by decide : (locate.seq FiniteScalarCall.code).keeps 51=true),
      prior.keepsReg (by decide : (locate.seq FiniteScalarCall.code).keeps 52=true)]
    exact ready
  let v := Function.update u (43 : Reg) (VPVNP.BurstRAM.PrivateRAM.BinaryOp.add.eval (u 43) (u 47))
  have incr : Runs pub mac advance u (r.image m) [tick w] v (r.image m) := .localStep _ rfl rfl
  have eq : (fs++gs)++[FiniteScalarCall.event r.task.cell.scratchBase (r.words w),tick w] =
      fs++((gs++[FiniteScalarCall.event r.task.cell.scratchBase (r.words w)])++[tick w]) := by simp
  refine ⟨_,u,v,loc.seq prep,?_,?_,?_,?_⟩
  · rw [eq]; exact loc.seq (call.seq incr)
  · rw [eq]
    rw [show traceCost (fs++((gs++[_])++[_])) = traceCost fs+(traceCost (gs++[FiniteScalarCall.event r.task.cell.scratchBase (r.words w)])+1) by
      rw [traceCost,VPVNP.RAMBuckets.cost_append,VPVNP.RAMBuckets.cost_append]; rfl]
    dsimp only [Row.cost,Row.words]
    omega
  · obtain ⟨⟨hw0,hb,hn,hix,hs,h1⟩,hc,ht,h3⟩ := live
    have hlim := hn ▸ (u 42).isLt
    simp (config := {decide := true}) [Ready,TypedBatch.Ready,v,VPVNP.BurstRAM.PrivateRAM.BinaryOp.eval,
      Fin.val_add,hw0,hb,hn,hix,hs,h1,hc,ht,h3,Nat.mod_eq_of_lt (by omega : i+1 < 2^w)]
  · intro es z mz hr
    obtain ⟨a',m',ts,ys,rfl,first,rest⟩ := Runs.seq_iff.mp hr
    obtain ⟨rfl,rfl,rfl⟩ := loc.unique_of_deterministic (by decide) first
    obtain ⟨b',mb,hs,ks,rfl,second,last⟩ := Runs.seq_iff.mp rest
    obtain ⟨rfl,rfl,rfl⟩ := unique _ _ _ second
    obtain ⟨rfl,rfl,rfl⟩ := incr.unique_of_deterministic (by decide) last
    exact ⟨eq.symm,rfl,rfl⟩

end RoutingISA.FiniteScalarBatch

end BorderVNP
end Computability
end OAI
