import OAI.Computability.BorderVNP.CellPacketSupplementalBatchMemory
import OAI.Computability.BorderVNP.RoutingISARegisterFrame
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # The native supplemental record prepass over the team's owned task rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket.Supplement.Batch

open VPVNP.BurstRAM

/-- Read the exclusive descriptor endpoint from the seven-word task table and the
four control scalars from the local owned-cell table. -/
def readRow : Code := .block [
  .constant 44 7,.binary .mul 45 44 43,.binary .add 45 41 45,.constant 44 1,.binary .add 45 45 44,
  .load 46 45,.constant 47 12,.binary .sub 2 46 47,
  .constant 47 4,.binary .mul 45 47 43,.binary .add 45 42 45,
  .load 3 45,.binary .add 45 45 44,.load 4 45,.binary .add 45 45 44,.load 5 45,
  .binary .add 45 45 44,.load 6 45]

/-- Read, patch, then advance to the next owned row. -/
def body : Code := .seq readRow (.seq Supplement.code (.binary .add 43 43 44))

/-- The loop executes precisely once per owned cell, including teams with zero cells. -/
def scan : Code := .seq (.constant 43 0) (.whileLt 43 40 body)

/-- Initialize the count and two pointers from the genuine current geometry frame.
Control word 11 is read indirectly through the directory pointer in slot 92. -/
def loadDirectory : Code := .block [readFrame 40 62 63 90,readFrame 41 62 63 89,
  readFrame 42 62 63 92,.constant 63 11,.binary .add 62 42 63,.load 42 62]

/-- Public evaluator entry for the sparse supplemental prepass. -/
def entry : Code := .seq loadDirectory scan

/-- Register invariant shared by all loop iterations. -/
def Ready (tasks controls count i : ℕ) (s : Reg → ℕ) : Prop :=
  s 40 = count ∧ s 41 = tasks ∧ s 42 = controls ∧ s 43 = i

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {tasks controls count i : ℕ}

set_option maxRecDepth 3000 in
private theorem readRow_run (s : Bank w) (m : Memory w) (c : Cell) (hi : i < count)
    (h : Ready tasks controls count i (readings s)) (stored : Stored c tasks controls i m)
    (room : Room c w) (taskFit : tasks+7*count ≤ 2^w) (controlFit : controls+4*count ≤ 2^w) :
    ∃ es t, Runs pub mac readRow s m es t m ∧ traceCost es ≤ 18 ∧ Input c.layout c.data t m ∧
      Ready tasks controls count i (readings t) ∧ readings t 44 = 1 := by
  obtain ⟨hc,ht,hp,hi'⟩ := h
  have tail := room.tail
  have positive : w ≠ 0 := by rintro rfl; simp at tail
  have safe : readRow.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [readRow,Code.block,Code.safeReadOnly,Code.evalNat,
      addressOpFits,addressOp,ht,hp,hi']
    have endWord := stored.tailEnd
    omega
  obtain ⟨es,t,run,cost,eq⟩ := readRow.runReadOnly pub mac m s safe
  refine ⟨_,_,run,cost,⟨?_,?_,?_,?_,?_,stored.base,stored.tailLen,stored.geomCount,
    stored.suppCount,stored.suppWords⟩,?_,?_⟩
  all_goals
    simp (config := {decide := true}) [Ready,eq,readRow,Code.block,Code.evalNat,addressOp,
      hc,ht,hp,hi',stored.source]
  · rw [stored.tailEnd]; omega
  · exact stored.counters
  · simpa [Nat.add_assoc] using stored.merged
  · simpa [Nat.add_assoc] using stored.report

private theorem body_run (s : Bank w) (m : Memory w) (c : Cell) (hi : i < count)
    (h : Ready tasks controls count i (readings s)) (stored : Stored c tasks controls i m)
    (room : Room c w) (taskFit : tasks+7*count ≤ 2^w) (controlFit : controls+4*count ≤ 2^w) :
    ∃ es t, Runs pub mac body s m es t (Supplement.image c.layout c.data m) ∧
      traceCost es ≤ 61 ∧ Ready tasks controls count (i+1) (readings t) := by
  obtain ⟨xs,t,r₁,b₁,input,stable,one⟩ := readRow_run (pub := pub) (mac := mac) s m c hi h stored room taskFit controlFit
  obtain ⟨ys,v,mv,r₂,b₂,out⟩ := Supplement.run (pub := pub) (mac := mac) c.layout c.data t m
    input room.tail room.counters room.base room.count
  have same : mv = Supplement.image c.layout c.data m := funext fun j => Fin.ext (congrFun out j)
  subst mv
  have kept (j : Reg) (ok : Supplement.code.keeps j = true) : readings v j = readings t j :=
    congrArg Fin.val (r₂.keepsReg ok)
  have before : Ready tasks controls count i (readings v) :=
    ⟨(kept 40 (by decide)).trans stable.1,(kept 41 (by decide)).trans stable.2.1,
      (kept 42 (by decide)).trans stable.2.2.1,(kept 43 (by decide)).trans stable.2.2.2⟩
  have unit := (kept 44 (by decide)).trans one
  let inc : Code := .binary .add 43 43 44
  have safe : inc.safeReadOnly w (readings pub) (readings (Supplement.image c.layout c.data m)) (readings v) := by
    change readings v 43 + readings v 44 < 2^w
    rw [before.2.2.2,unit]
    have fits : count < 2^w := h.1.symm.trans_lt (s 40).isLt
    omega
  obtain ⟨zs,z,r₃,b₃,final⟩ := inc.runReadOnly pub mac _ v safe
  refine ⟨_,z,r₁.seq (r₂.seq r₃),?_,?_⟩
  · have last : traceCost zs ≤ 1 := b₃
    rw [show traceCost (xs++(ys++zs)) = traceCost xs+traceCost (ys++zs) from VPVNP.RAMBuckets.cost_append ..,
      show traceCost (ys++zs) = traceCost ys+traceCost zs from VPVNP.RAMBuckets.cost_append ..]
    omega
  · obtain ⟨hc,ht,hp,idx⟩ := before
    simp (config := {decide := true}) [Ready,final,inc,Code.evalNat,addressOp,hc,ht,hp,idx,unit]

/-- The native scan computes the chronological memory fold from the initially supplied
rows and numeric address separation. It uses at most 62 ticks per owned cell and two
additional ticks for initialization and the final guard. -/
theorem scan_run (s : Bank w) (m : Memory w) (cells : ℕ → Cell)
    (len : readings s 40 = count) (base : readings s 41 = tasks) (ctrl : readings s 42 = controls)
    (taskFit : tasks+7*count ≤ 2^w) (controlFit : controls+4*count ≤ 2^w)
    (init : ∀ i < count, Stored (cells i) tasks controls i m ∧ Room (cells i) w)
    (apart : ∀ j < count, ∀ k < j, ∀ addr ∈ (cells j).sources tasks controls j, (cells k).Outside addr) :
    ∃ es t, Runs pub mac scan s m es t (written m cells count) ∧ traceCost es ≤ 2+62*count ∧
      (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧ Ready tasks controls count count (readings t) := by
  let P (i : ℕ) (z : NatState) := Ready tasks controls count i z.reg ∧ z.mem = readings (written m cells i)
  have step (i : ℕ) (hi : i < count) (u : Bank w) (mu : Memory w) (p : P i (.ofWords u mu)) :
      BoundedRun pub mac body u mu 61 (P (i+1)) := by
    have live : mu = written m cells i := funext fun j => Fin.ext (congrFun p.2 j)
    subst mu
    obtain ⟨source,room⟩ := init i hi
    obtain ⟨xs,t,run,cost,ready⟩ := body_run (pub := pub) (mac := mac) u _ (cells i) hi p.1
      (stored_prefix m cells source (apart i hi)) room taskFit controlFit
    exact ⟨_,t,_,run,cost,ready,rfl⟩
  obtain ⟨xs,u,setup,b₁,regs⟩ := (Code.constant 43 0).runReadOnly pub mac m s (Nat.two_pow_pos _)
  have zero : P 0 (.ofWords u m) := by
    refine ⟨?_,rfl⟩
    change Ready tasks controls count 0 (readings u)
    simp (config := {decide := true}) [Ready,regs,Code.evalNat,len,base,ctrl]
  obtain ⟨ys,t,mt,loop,b₂,done⟩ := run_counted_loop pub mac 43 40 body count 61 P
    (fun _ _ h => ⟨h.1.2.2.2,h.1.1⟩) step 0 (Nat.zero_le _) u m zero
  have exactMem : mt = written m cells count := funext fun j => Fin.ext (congrFun done.2 j)
  subst mt
  have full := setup.seq loop
  refine ⟨_,t,full,?_,full.unsigned_events (by decide),done.1⟩
  rw [show traceCost (xs++ys) = traceCost xs+traceCost ys from VPVNP.RAMBuckets.cost_append ..]
  change traceCost xs ≤ 1 at b₁
  omega

/-- The outer frame and its indirect four-word table pointer are fetched by unsigned
native instructions before the owned-cell scan begins. -/
theorem entry_run (s : Bank w) (m : Memory w) (cells : ℕ → Cell)
    (frame : (pub 0).val+92 < 2^w) (pointer : readings m ((pub 0).val+92)+11 < 2^w)
    (len : readings m ((pub 0).val+90) = count) (base : readings m ((pub 0).val+89) = tasks)
    (ctrl : readings m (readings m ((pub 0).val+92)+11) = controls)
    (taskFit : tasks+7*count ≤ 2^w) (controlFit : controls+4*count ≤ 2^w)
    (init : ∀ i < count, Stored (cells i) tasks controls i m ∧ Room (cells i) w)
    (apart : ∀ j < count, ∀ k < j, ∀ addr ∈ (cells j).sources tasks controls j, (cells k).Outside addr) :
    ∃ es t, Runs pub mac entry s m es t (written m cells count) ∧ traceCost es ≤ 17+62*count ∧
      (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧ Ready tasks controls count count (readings t) := by
  have safe : loadDirectory.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [loadDirectory,readFrame,Code.block,Code.safeReadOnly,Code.evalNat,
      addressOpFits,addressOp,readings]
    change (m ((pub 0).val+92)).val+11 < 2^w at pointer
    omega
  obtain ⟨xs,u,first,b₁,eq⟩ := loadDirectory.runReadOnly pub mac m s safe
  have loaded : readings u 40 = count ∧ readings u 41 = tasks ∧ readings u 42 = controls := by
    simp (config := {decide := true}) [eq,loadDirectory,readFrame,Code.block,Code.evalNat,addressOp,
      show readings pub 0 = (pub 0).val from rfl,len,base,ctrl]
  obtain ⟨ys,t,rest,b₂,_,done⟩ := scan_run (pub := pub) (mac := mac) u m cells
    loaded.1 loaded.2.1 loaded.2.2 taskFit controlFit init apart
  have full := first.seq rest
  refine ⟨_,t,full,?_,full.unsigned_events (by decide),done⟩
  rw [show traceCost (xs++ys) = traceCost xs+traceCost ys from VPVNP.RAMBuckets.cost_append ..]
  change traceCost xs ≤ 15 at b₁
  omega

end RoutingISA.CellPacket.Supplement.Batch

end BorderVNP
end Computability
end OAI
