import OAI.Computability.BorderVNP.RoutingISAOffsetLoops
import OAI.Computability.BorderVNP.RoutingISAScheduledLength

/-! # Certified native construction of the complete partner-offset table

The body computes the row-major address, stores the current prefix, executes
the scheduled-length quotient, checks the next prefix, and advances the cursor.
The three counted loops then construct the two output tables in cubic time.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ} {l : TableLayout} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)

private theorem triple_calc (s : Bank w) (m : Memory w) (h : l.ready (.ofWords s m))
    (al : l.Allocated w) {u v j : ℕ} (hu : u < l.teams) (hv : v < l.teams) (hj : j < l.teams)
    (h21 : readings s 21 = u) (h22 : readings s 22 = v) (h23 : readings s 23 = j) :
    BoundedRun pub macros (tripleAddress 24 21 22 23 3 9) s m (tripleAddress 24 21 22 23 3 9).slots
      (fun z => z.reg 24 = tripleIndex l.offsets l.teams u v j ∧
        (∀ i : Reg, i.val < 24 → z.reg i = readings s i) ∧ z.mem = readings m) := by
  let c := tripleAddress 24 21 22 23 3 9
  have h3 : readings s 3 = l.teams := h 3 (by decide)
  have h9 : readings s 9 = l.offsets := h 9 (by decide)
  have hbound := al.address (offset_contains hu hv hj)
  change (u*l.teams+v)*l.teams+j+l.offsets < 2^w at hbound
  have hsquare : u*l.teams+v < 2^w := (pairKey_bound hu hv).trans al.square
  have safe : c.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [c, tripleAddress, Code.block, Code.evalNat, Code.safeReadOnly,
      addressOpFits, addressOp, h3,h9,h21,h22,h23]
    omega
  obtain ⟨es,t,r,ht,he⟩ := c.runReadOnly pub macros m s safe
  refine ⟨es,t,m,r,ht,?_,fun i hi => (congrFun he i).trans (c.evalNat_protected _ _ _
    (lo := 24) (by decide) i hi),rfl⟩
  change readings t 24 = _
  rw [he]
  simp (config := {decide := true}) [c,tripleAddress,tripleIndex,Code.block,Code.evalNat,addressOp,
    h3,h9,h21,h22,h23]

private def partnerTail : Code := .block [
  .binary .add 29 20 28, .ifLt 29 20 .reject .nop, .copy 20 29, .binary .add 23 23 1]

private theorem partnerTail_run (s : Bank w) (m : Memory w) (h : l.ready (.ofWords s m))
    {u v j pre len : ℕ} (hj : j < l.teams) (al : l.Allocated w)
    (h20 : readings s 20 = pre) (h21 : readings s 21 = u) (h22 : readings s 22 = v)
    (h23 : readings s 23 = j) (h28 : readings s 28 = len) (hfits : pre+len < 2^w) :
    BoundedRun pub macros partnerTail s m partnerTail.slots (fun z =>
      l.ready z ∧ z.reg 21 = u ∧ z.reg 22 = v ∧ z.reg 23 = j+1 ∧ z.reg 20 = pre+len ∧
        z.mem = readings m) := by
  have h1 : readings s 1 = 1 := h 1 (by decide)
  have hfitj := lt_of_le_of_lt (show j+1 ≤ l.teams from hj) al.teamsFit
  have safe : partnerTail.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [partnerTail,Code.block,Code.safeReadOnly,Code.evalNat,
      addressOpFits,addressOp,h20,h23,h28,h1,hfits,hfitj]
  obtain ⟨es,t,r,ht,he⟩ := partnerTail.runReadOnly pub macros m s safe
  refine ⟨es,t,m,r,ht,?_,?_,?_,?_,?_,rfl⟩
  · intro i hi
    exact (congrFun he i).trans ((partnerTail.evalNat_protected _ _ _
      (lo := 13) (by decide) i (by omega)).trans (h i hi))
  all_goals change readings t _ = _
  all_goals rw [he]
  all_goals simp (config := {decide := true}) [partnerTail,Code.block,Code.evalNat,addressOp,
    h20,h21,h22,h23,h28,h1]

/-- The exact native triple-address store and prefix update for one partner. -/
theorem tabulatePartner_kernel (row : ℕ → TableRow) (al : l.Allocated w) (fit : l.RowsFit w row) :
    PartnerKernel l row pub macros := by
  intro u v j hu hv hj s m h hw h21 h22 h23 h20
  let off := tripleIndex l.offsets l.teams u v j
  let pre := l.legPrefix row u v j
  let len := l.partnerLength row u v j
  have hn : l.legPrefix row u v (j+1) = pre+len := Finset.sum_range_succ ..
  have hfit : pre+len < 2^w := by
    rw [← hn]
    exact ((l.legPrefix_mono row u v hj).trans (l.legPrefix_le_sum row hu v)).trans_lt fit.widths
  apply (triple_calc pub macros s m h al hu hv hj h21 h22 h23).seq
  rintro t mt ⟨haddr,hkeep,hm⟩
  change readings t 24 = off at haddr
  change readings mt = readings m at hm
  have hr : l.ready (.ofWords t mt) := fun i hi => (hkeep i (by omega)).trans (h i hi)
  have t21 := (hkeep 21 (by decide)).trans h21
  have t22 := (hkeep 22 (by decide)).trans h22
  have t23 := (hkeep 23 (by decide)).trans h23
  have t20 := (hkeep 20 (by decide)).trans h20
  change readings t 20 = pre at t20
  apply ((Code.store 24 20).runFixed pub macros t mt trivial).seq
  intro t' mt' he
  have bank : readings t' = readings t := congrArg NatState.reg he
  have mem : readings mt' = Function.update (readings m) off pre := by
    have hmem := congrArg NatState.mem he
    change readings mt' = Function.update (readings mt) (readings t 24) (readings t 20) at hmem
    exact hmem.trans (by rw [hm,haddr,t20])
  have hw' (i : ℕ) (hi : i < l.teams^2) : readings mt' (l.widths+i) = l.pairWidth row l.count i := by
    have hne : l.widths+i ≠ off := fun eq => al.separate .offsets .widths off (by decide)
      (offset_contains hu hv hj) (eq ▸ l.contains_offset (a := .widths) hi)
    rw [mem, Function.update_of_ne hne, hw i hi]
  have hr' : l.ready (.ofWords t' mt') := fun i hi => (congrFun bank i).trans (hr i hi)
  obtain ⟨es,t'',r,cost,hr'',hlen,keep⟩ := scheduledLengthWord_run l row pub macros t' mt'
    al fit hr' hu hv hj ((congrFun bank 21).trans t21) ((congrFun bank 22).trans t22)
    ((congrFun bank 23).trans t23) hw'
  obtain ⟨fs,z,mz,tail,tc,hrz,rz21,rz22,rz23,rz20,mz'⟩ :=
    partnerTail_run pub macros t'' mt' hr'' hj al
      ((keep 20 (by decide)).trans ((congrFun bank 20).trans t20))
      ((keep 21 (by decide)).trans ((congrFun bank 21).trans t21))
      ((keep 22 (by decide)).trans ((congrFun bank 22).trans t22))
      ((keep 23 (by decide)).trans ((congrFun bank 23).trans t23)) hlen hfit
  refine ⟨_,z,mz,r.seq tail,?_,hrz,rz21,rz22,rz23,rz20.trans hn.symm,mz'.trans mem⟩
  exact (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add cost tc)

/-- The native offset pass computes all partner prefixes and oriented totals in
at most `128*(teams+1)^3` ticks, preserving every address outside the two arrays. -/
theorem offsetPass_image (l : TableLayout) (row : ℕ → TableRow) (s : Bank w) (m : Memory w)
    (al : l.Allocated w) (fit : l.RowsFit w row) (hr : l.ready (.ofWords s m))
    (hw : ∀ i < l.teams^2, readings m (l.widths+i) = l.pairWidth row l.count i) :
    BoundedRun pub macros offsetPass s m (128*(l.teams+1)^3) (fun z =>
      l.ready z ∧ (∀ u < l.teams, ∀ v < l.teams, ∀ j < l.teams,
        z.mem (tripleIndex l.offsets l.teams u v j) = l.legPrefix row u v j) ∧
      (∀ u < l.teams, ∀ v < l.teams,
        z.mem (pairIndex l.used l.teams u v) = l.legPrefix row u v l.teams) ∧
      ∀ i, ¬l.contains .offsets i → ¬l.contains .used i → z.mem i = readings m i) :=
  offsetPass_of_partnerKernel s m al hr hw (tabulatePartner_kernel pub macros row al fit)

end RoutingISA

end BorderVNP
end Computability
end OAI
