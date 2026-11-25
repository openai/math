import OAI.Computability.BorderVNP.CubePairDirectoryModel

/-! # Native digit scan for an ordered label pair

Each iteration reads the next two symbols by division and remainder, sorts
them, and updates the cube rank, vertex number, kind and orientation. The
loop advances both positional powers by one multiplication.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.PairDirectory

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Running register interpretation after `i` low coordinates have been scanned. -/
structure Prefix (l : Layout) (q i : ℕ) (orig : ℕ → ℕ) (z : NatState) : Prop where
  ready : l.Ready z
  key : z.reg 9 = q
  axis : z.reg 20 = i
  place : z.reg 21 = l.d^i
  pairPlace : z.reg 22 = (l.d*l.d)^i
  vertexPlace : z.reg 23 = 2^(i-1)
  flag : z.reg 24 = kind l.d (q/l.Z) (q%l.Z) i
  rank : z.reg 25 = cubeRank l.d (q/l.Z) (q%l.Z) i
  orient : z.reg 26 = orientation l.d (q/l.Z) (q%l.Z) i
  vertex : z.reg 27 = vertexNo l.d (q/l.Z) (q%l.Z) i
  left : z.reg 28 = q/l.Z
  right : z.reg 29 = q%l.Z
  memory : z.mem = orig

/-- Initialize the local counters and decode source and destination from the row-major key. -/
def start : Code := .block [.copy 20 0,.copy 21 1,.copy 22 1,.copy 23 1,.copy 24 1,
  .copy 25 0,.copy 26 0,.copy 27 0,.binary .div 28 9 5,.binary .mod 29 9 5]

private def sortDigits : Code := .ifLt 31 30 (.block [.copy 32 31,.copy 33 30,.copy 34 1])
  (.block [.copy 32 30,.copy 33 31,.copy 34 0])

private def updateFlag : Code := .ifEq 30 31 (.copy 24 0) .nop

private def updateVertex : Code := .ifEq 20 0 (.copy 26 34)
  (.block [.binary .mul 35 34 23,.binary .add 27 27 35,.binary .add 23 23 23])

private def prepare : Code := .block [.binary .div 30 28 21,.binary .mod 30 30 3,
  .binary .div 31 29 21,.binary .mod 31 31 3,sortDigits,
  .binary .mul 32 32 3,.binary .add 32 32 33]

private def accumulate : Code := .block [updateFlag,.binary .mul 35 32 22,.binary .add 25 25 35,
  updateVertex,.binary .mul 22 22 10,.binary .mul 21 21 3,.binary .add 20 20 1]

/-- One complete native digit iteration. Registers 30 through 35 are temporary. -/
def body : Code := .seq prepare accumulate

/-- The complete digit scan, before writing the result to the output directory. -/
def kernel : Code := .seq start (.whileLt 20 4 body)

private theorem sort_eval (p : Arg → ℕ) (m : ℕ → ℕ) (r : Reg → ℕ) :
    sortDigits.evalNat p m r = Function.update (Function.update (Function.update r 32 (min (r 30) (r 31)))
      33 (max (r 30) (r 31))) 34 (if r 31 < r 30 then r 1 else r 0) := by
  by_cases h : r 31 < r 30
  · simp (disch := decide) [sortDigits,Code.block,Code.evalNat,h,min_eq_right h.le,max_eq_left h.le]
  · simp (disch := decide) [sortDigits,Code.block,Code.evalNat,h,min_eq_left (le_of_not_gt h),max_eq_right (le_of_not_gt h)]

private theorem flag_eval (p : Arg → ℕ) (m : ℕ → ℕ) (r : Reg → ℕ) :
    updateFlag.evalNat p m r = Function.update r 24 (if r 30 = r 31 then r 0 else r 24) := by
  by_cases h : r 30 = r 31 <;> simp [updateFlag,Code.evalNat,h]

private theorem vertex_eval (p : Arg → ℕ) (m : ℕ → ℕ) (r : Reg → ℕ) :
    updateVertex.evalNat p m r =
      Function.update (Function.update (Function.update (Function.update r
        26 (if r 20 = r 0 then r 34 else r 26))
        35 (if r 20 = r 0 then r 35 else r 34*r 23))
        27 (if r 20 = r 0 then r 27 else r 27+r 34*r 23))
        23 (if r 20 = r 0 then r 23 else r 23+r 23) := by
  funext j
  by_cases h : r 20 = r 0 <;> by_cases h26 : j=26 <;> by_cases h35 : j=35 <;>
    by_cases h27 : j=27 <;> by_cases h23 : j=23 <;>
    simp_all (config := {decide := true}) [updateVertex,Code.block,Code.evalNat,addressOp,Function.update]

private theorem accumulate_fields (p : Arg → ℕ) (m : ℕ → ℕ) (s : Reg → ℕ) :
    let out := accumulate.evalNat p m s
    out 20 = s 20+s 1 ∧ out 21 = s 21*s 3 ∧ out 22 = s 22*s 10 ∧
    out 23 = (if s 20=s 0 then s 23 else s 23+s 23) ∧
    out 24 = (if s 30=s 31 then s 0 else s 24) ∧ out 25 = s 25+s 32*s 22 ∧
    out 26 = (if s 20=s 0 then s 34 else s 26) ∧
    out 27 = (if s 20=s 0 then s 27 else s 27+s 34*s 23) ∧ out 28 = s 28 ∧ out 29 = s 29 := by
  dsimp only
  simp only [accumulate,Code.block,Code.evalNat,flag_eval,vertex_eval,addressOp]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem sort_safe (p : Arg → ℕ) (m : ℕ → ℕ) (r : Reg → ℕ) (w : ℕ) :
    sortDigits.safeReadOnly w p m r := by
  simp [sortDigits,Code.block,Code.safeReadOnly]

private theorem flag_safe (p : Arg → ℕ) (m : ℕ → ℕ) (r : Reg → ℕ) (w : ℕ) :
    updateFlag.safeReadOnly w p m r := by simp [updateFlag,Code.safeReadOnly]

private theorem vertex_safe (p : Arg → ℕ) (m : ℕ → ℕ) (r : Reg → ℕ) (w : ℕ) :
    updateVertex.safeReadOnly w p m r ↔ r 20 ≠ r 0 →
      r 34*r 23 < 2^w ∧ r 27+r 34*r 23 < 2^w ∧ r 23+r 23 < 2^w := by
  by_cases h : r 20 = r 0 <;> simp (config := {decide := true}) [updateVertex,Code.block,
    Code.evalNat,addressOp,addressOpFits,Code.safeReadOnly,h,Function.update]

private theorem sumVertex_succ (d u v i : ℕ) (hi : i ≠ 0) :
    vertexNo d u v (i+1) = vertexNo d u v i + flip d u v i * 2^(i-1) := by
  simp [vertexNo,Finset.sum_range_succ,hi]

private theorem sumRank_succ (d u v i : ℕ) :
    cubeRank d u v (i+1) = cubeRank d u v i + pairDigit d u v i * (d*d)^i := by
  simp [cubeRank,Finset.sum_range_succ]

private theorem flip_eq (d u v i : ℕ) : flip d u v i = if digit d v i < digit d u i then 1 else 0 := by
  by_cases h : digit d v i < digit d u i <;> simp [flip,h]

private theorem vertexPlace_succ {i : ℕ} (h : i ≠ 0) : 2^(i-1)+2^(i-1) = 2^i := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  rw [pow_succ]
  simp; omega

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
private theorem body_spec (p : Arg → ℕ) (l : Layout) (q i : ℕ) (orig : ℕ → ℕ) (z : NatState)
    (st : Prefix l q i orig z) {w : ℕ} (fit : l.Fits w) (hi : i < l.axes) :
    body.safeReadOnly w p z.mem z.reg ∧ Prefix l q (i+1) orig ⟨body.evalNat p z.mem z.reg,z.mem⟩ := by
  let u := q/l.Z
  let v := q%l.Z
  have r0 : z.reg 0 = 0 := st.ready 0 (by decide) (by decide)
  have r1 : z.reg 1 = 1 := st.ready 1 (by decide) (by decide)
  have r3 : z.reg 3 = l.d := st.ready 3 (by decide) (by decide)
  have r10 : z.reg 10 = l.d*l.d := st.ready 10 (by decide) (by decide)
  have hp : 0 < l.d^i := pow_pos fit.positive _
  have hsq : (l.d*l.d)^(i+1) < 2^w := by
    apply (Nat.pow_le_pow_right (Nat.mul_pos fit.positive fit.positive) hi).trans_lt
    rw [l.radixPower]
    have := fit.directory
    omega
  have hplace : l.d^(i+1) < 2^w := by
    apply (Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ fit.positive) (i+1)).trans_lt hsq
  have hrank := (cubeRank_lt l.d u v (i+1) fit.positive).trans hsq
  have hv' := (vertexNo_lt l.d u v (i+1)).trans ((Nat.pow_le_pow_right (by decide : 0 < 2) hi).trans_lt fit.vertices)
  have hpair := (pairDigit_lt l.d u v i fit.positive).trans fit.radix
  have hsucc := fit.axes
  have hsum : cubeRank l.d u v i + pairDigit l.d u v i * (l.d*l.d)^i < 2^w := sumRank_succ .. ▸ hrank
  have hterm : pairDigit l.d u v i * (l.d*l.d)^i < 2^w := (Nat.le_add_left ..).trans_lt hsum
  have hmin : min (digit l.d u i) (digit l.d v i)*l.d < 2^w := (Nat.le_add_right ..).trans_lt hpair
  have hplace' : l.d^i*l.d < 2^w := by simpa only [pow_succ] using hplace
  have hsq' : (l.d*l.d)^i*(l.d*l.d) < 2^w := by simpa only [pow_succ] using hsq
  have hincr : i+1 < 2^w := (Nat.succ_le_of_lt hi).trans_lt fit.axes
  have bits (h : i ≠ 0) : flip l.d u v i * 2^(i-1) < 2^w ∧
      vertexNo l.d u v i + flip l.d u v i * 2^(i-1) < 2^w ∧ 2^(i-1)+2^(i-1) < 2^w := by
    rw [sumVertex_succ _ _ _ _ h] at hv'
    exact ⟨(Nat.le_add_left ..).trans_lt hv', hv', (vertexPlace_succ h) ▸
      (Nat.pow_le_pow_right (by decide : 0 < 2) hi.le).trans_lt fit.vertices⟩
  have deq (x : ℕ) : x / l.d^i % l.d = digit l.d x i := rfl
  have peq : min (digit l.d u i) (digit l.d v i) * l.d + max (digit l.d u i) (digit l.d v i) = pairDigit l.d u v i := rfl
  have keep := body.evalNat_protected p z.mem z.reg (lo := 20) (by decide)
  have or0 : orientation l.d u v (i+1) = if i=0 then flip l.d u v i else orientation l.d u v i := by
    by_cases h : i=0 <;> simp [orientation,h]
  have vnext : vertexNo l.d u v (i+1) = if i=0 then vertexNo l.d u v i else
      vertexNo l.d u v i + flip l.d u v i * 2^(i-1) := by
    by_cases h : i=0 <;> simp [vertexNo,Finset.sum_range_succ,h]
  let r := prepare.evalNat p z.mem z.reg
  have kept (j : Reg) (hj : j.val < 30) : r j = z.reg j := prepare.evalNat_protected _ _ _ (by decide) j hj
  have hl : z.reg 28 = u := st.left
  have hr : z.reg 29 = v := st.right
  have prepOK : prepare.safeReadOnly w p z.mem z.reg := by
    simp (disch := decide) only [prepare,Code.block,Code.safeReadOnly,Code.evalNat,sort_safe,sort_eval,
      Function.update_self,Function.update_of_ne,addressOpFits,addressOp,st.place,hl,hr,r3,deq,
      hp,fit.positive,hmin,peq,hpair,and_true]
  have r30 : r 30 = digit l.d u i := by
    simp (disch := decide) only [r,prepare,Code.block,Code.evalNat,sort_eval,Function.update_self,
      Function.update_of_ne,addressOp,st.place,hl,r3,deq]
  have r31 : r 31 = digit l.d v i := by
    simp (disch := decide) only [r,prepare,Code.block,Code.evalNat,sort_eval,Function.update_self,
      Function.update_of_ne,addressOp,st.place,hr,r3,deq]
  have r32 : r 32 = pairDigit l.d u v i := by
    simp (disch := decide) only [r,prepare,Code.block,Code.evalNat,sort_eval,Function.update_self,
      Function.update_of_ne,addressOp,st.place,hl,hr,r3,deq,peq]
  have r34 : r 34 = flip l.d u v i := by
    simp (disch := decide) only [r,prepare,Code.block,Code.evalNat,sort_eval,Function.update_self,
      Function.update_of_ne,addressOp,st.place,hl,hr,r0,r1,r3,deq,flip_eq]
  change (prepare.safeReadOnly w p z.mem z.reg ∧ accumulate.safeReadOnly w p z.mem r) ∧
    Prefix l q (i+1) orig ⟨accumulate.evalNat p z.mem r,z.mem⟩
  have rf : r 24 = kind l.d u v i := (kept _ (by decide)).trans st.flag
  have rr : r 25 = cubeRank l.d u v i := (kept _ (by decide)).trans st.rank
  have ro : r 26 = orientation l.d u v i := (kept _ (by decide)).trans st.orient
  have rv : r 27 = vertexNo l.d u v i := (kept _ (by decide)).trans st.vertex
  have r20 := (kept 20 (by decide)).trans st.axis
  have r21 := (kept 21 (by decide)).trans st.place
  have r22 := (kept 22 (by decide)).trans st.pairPlace
  have r23 := (kept 23 (by decide)).trans st.vertexPlace
  have rr0 := (kept 0 (by decide)).trans r0
  have rr1 := (kept 1 (by decide)).trans r1
  have rr3 := (kept 3 (by decide)).trans r3
  have rr10 := (kept 10 (by decide)).trans r10
  constructor
  · refine ⟨prepOK,?_⟩
    simp (disch := decide) only [accumulate,Code.block,Code.evalNat,Code.safeReadOnly,flag_eval,vertex_eval,
      flag_safe,vertex_safe,addressOp,addressOpFits,Function.update_self,Function.update_of_ne,
      r20,r21,r22,r23,r32,r34,rr,rv,rr0,rr1,rr3,rr10,hterm,hsum,hsq',hplace',hincr,true_and,and_true]
    exact bits
  · obtain ⟨f20,f21,f22,f23,f24,f25,f26,f27,f28,f29⟩ := accumulate_fields p z.mem r
    refine ⟨fun j hj hj' => (keep j (by omega)).trans (st.ready j hj hj'),(keep 9 (by decide)).trans st.key,
      ?_,?_,?_,?_,?_,?_,?_,?_,f28.trans ((kept _ (by decide)).trans st.left),
      f29.trans ((kept _ (by decide)).trans st.right),st.memory⟩
    · simpa only [r20,rr1] using f20
    · simpa only [r21,rr3,pow_succ] using f21
    · simpa only [r22,rr10,pow_succ] using f22
    · rw [r20,rr0,r23] at f23
      by_cases e : i=0
      · simpa [e] using f23
      · simpa only [ite_eq_right e,vertexPlace_succ e,Nat.add_sub_cancel] using f23
    · simpa only [r30,r31,rr0,rf,kind] using f24
    · simpa only [rr,r32,r22,sumRank_succ] using f25
    · rw [r20,rr0,r34,ro] at f26
      exact f26.trans or0.symm
    · rw [r20,rr0,rv,r34,r23] at f27
      exact f27.trans vnext.symm

private theorem start_spec (p : Arg → ℕ) (l : Layout) (q : ℕ) (z : NatState)
    (ready : l.Ready z) (key : z.reg 9 = q) {w : ℕ} (fit : l.Fits w) :
    start.safeReadOnly w p z.mem z.reg ∧ Prefix l q 0 z.mem ⟨start.evalNat p z.mem z.reg,z.mem⟩ := by
  have r0 : z.reg 0 = 0 := ready 0 (by decide) (by decide)
  have r1 : z.reg 1 = 1 := ready 1 (by decide) (by decide)
  have r5 : z.reg 5 = l.Z := ready 5 (by decide) (by decide)
  have hp : 0 < l.Z := pow_pos fit.positive _
  have keep := start.evalNat_protected p z.mem z.reg (lo := 20) (by decide)
  constructor
  · simp (disch := decide) [start,Code.block,Code.safeReadOnly,Code.evalNat,addressOpFits,r5,hp]
  · refine ⟨fun j hj hj' => (keep j (by omega)).trans (ready j hj hj'), (keep 9 (by decide)).trans key, ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl⟩
    all_goals simp (disch := decide) [start,Code.block,Code.evalNat,addressOp,cubeRank,vertexNo,kind,orientation,r0,r1,r5,key]

/-- The completed native scan returns the kind, cube rank, orientation and
vertex number, leaving every shared-memory word intact. -/
theorem run_kernel {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (l : Layout)
    (s : Bank w) (m : Memory w) (q : ℕ) (fit : l.Fits w) (ready : l.Ready (.ofWords s m))
    (key : readings s 9 = q) :
    BoundedRun pub mac kernel s m (start.slots+l.axes*(body.slots+1)+1)
      (Prefix l q l.axes (readings m)) := by
  obtain ⟨safe,out⟩ := start_spec (readings pub) l q (.ofWords s m) ready key fit
  obtain ⟨es,t,hr,hc,hread⟩ := start.runReadOnly pub mac m s safe
  have init : BoundedRun pub mac start s m start.slots (Prefix l q 0 (readings m)) :=
    ⟨es,t,m,hr,hc,by change Prefix l q 0 _ ⟨readings t,readings m⟩; rw [hread]; exact out⟩
  have step (i : ℕ) (hi : i < l.axes) (u : Bank w) (mu : Memory w) (st : Prefix l q i (readings m) (.ofWords u mu)) :
      BoundedRun pub mac body u mu body.slots (Prefix l q (i+1) (readings m)) := by
    obtain ⟨fits,hout⟩ := body_spec (readings pub) l q i (readings m) (.ofWords u mu) st fit hi
    obtain ⟨fs,y,run,hcap,hy⟩ := body.runReadOnly pub mac mu u fits
    exact ⟨fs,y,mu,run,hcap,by change Prefix l q (i+1) _ ⟨readings y,readings mu⟩; rw [hy]; exact hout⟩
  have loop (u : Bank w) (mu : Memory w) (st : Prefix l q 0 (readings m) (.ofWords u mu)) :=
    run_counted_loop pub mac 20 4 body l.axes body.slots (fun i => Prefix l q i (readings m))
      (fun _ _ h => ⟨h.axis,h.ready 4 (by decide) (by decide)⟩) step 0 (Nat.zero_le _) u mu st
  simpa only [kernel, Nat.sub_zero, Nat.add_assoc] using init.seq loop

end Cube.PairDirectory

end BorderVNP
end Computability
end OAI
