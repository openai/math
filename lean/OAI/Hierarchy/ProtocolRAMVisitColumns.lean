import OAI.Hierarchy.ProtocolRAMTurnWalk
import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Cooking the predecessor and endpoint-sum columns of the terminal site walk -/

namespace Hierarchy.ProtocolRAMVisitColumns

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM ProbeStage.Native ProtocolRAMTurnWalk
open scoped Fin.CommRing

structure Inputs where
  item : Expr
  origin : Expr
  rawPosition : Expr
  forwardSite : Bank
  occurrenceEdge : Bank
  tailSite : Bank
  headSite : Bank

def ptr (initial dst : ℕ) (b : Inputs) : Expr :=
  .branch .eq b.rawPosition (.lit 0) (.lit initial) (.op .add (.lit dst) (.op .sub .row (.lit 1)))

def edge (b : Inputs) : Expr :=
  .lookup b.occurrenceEdge (.op .add b.origin (.op .sub b.rawPosition (.lit 1)))

def total (b : Inputs) : Expr :=
  .branch .eq b.rawPosition (.lit 0) (.lookup b.forwardSite b.item)
    (.op .add (.lookup b.tailSite (edge b)) (.lookup b.headSite (edge b)))

def terms (initial dst : ℕ) (b : Inputs) := [ptr initial dst b,total b]

def program (W N initial : ℕ) (b : Inputs) :=
  let ptrBase := initial+1
  let dst := ptrBase+2*N
  ((scan W initial 1 (.lit 0)).seq (ProtocolRAM.program W (columns N ptrBase (terms initial dst b)))).seq
    (ProtocolRAMTurnWalk.program W ptrBase (ptrBase+N) dst N)

def ticks (N initial : ℕ) (b : Inputs) :=
  (10+ProtocolRAM.clock (columns N (initial+1) (terms initial (initial+1+2*N) b)))+(3+14*N)

theorem ticks_eq (N initial : ℕ) (b : Inputs) :
    ticks N initial b = 25+N*(22+2*(ptr initial (initial+1+2*N) b).work+2*(total b).work) := by
  simp only [ticks,terms,columns,ProtocolRAM.clock,Pass.clock]
  ring

variable {W N : ℕ}

def previous? (pos : Fin N → ℕ) (earlier : ∀ i,0 < pos i → 0 < i.val) (i : Fin N) : Before i :=
  if live : 0 < pos i then some ⟨i.val-1,by have := earlier i live;omega⟩ else none

structure Geography (b : Inputs) (m : Memory W) (pos origin item site : Fin N → ℕ)
    (paid entry tail head : ℕ → ℕ) : Prop where
  position : ∀ i,b.rawPosition.eval m (i.val:Word W)=(pos i:Word W)
  origins : ∀ i,b.origin.eval m (i.val:Word W)=(origin i:Word W)
  items : ∀ i,b.item.eval m (i.val:Word W)=(item i:Word W)
  positionFits : ∀ i,pos i < 2^W
  previousRow : ∀ i,0 < pos i → 0 < i.val
  initial : ∀ i,pos i=0 → b.forwardSite.read m (item i:Word W)=(entry (item i):Word W)
  source : ∀ i,pos i=0 → entry (item i)=site i
  edgeAt : ∀ i,0 < pos i → b.occurrenceEdge.read m ((origin i+(pos i-1):ℕ):Word W)=(paid (origin i+(pos i-1)):Word W)
  tailAt : ∀ i,0 < pos i → b.tailSite.read m (paid (origin i+(pos i-1)):Word W)=(tail (paid (origin i+(pos i-1))):Word W)
  headAt : ∀ i,0 < pos i → b.headSite.read m (paid (origin i+(pos i-1)):Word W)=(head (paid (origin i+(pos i-1))):Word W)
  /-- The actual previous record and the current one are the two ends of this
  reported occurrence. This equality follows in either direction of traversal. -/
  adjacent : ∀ (i : Fin N) (_h : 0 < pos i),
    let e := paid (origin i+(pos i-1))
    tail e+head e=site i+site ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩

theorem ptr_read {b : Inputs} {m : Memory W} {pos origin item site : Fin N → ℕ}
    {paid entry tail head : ℕ → ℕ}
    (g : Geography b m pos origin item site paid entry tail head) (initial dst : ℕ) (i : Fin N) :
    (ptr initial dst b).eval m (i.val:Word W)=
      (pointer dst initial i (previous? pos g.previousRow i):Word W) := by
  by_cases h : pos i=0
  · simp [ptr,Expr.eval,Comparison.test,g.position,h,previous?,pointer]
  · have nz : (pos i:Word W)≠0 := by
      intro eq
      apply h
      simpa only [Fin.val_cast_of_lt (g.positionFits i),Fin.val_zero] using congrArg Fin.val eq
    have prev := g.previousRow i (Nat.pos_of_ne_zero h)
    simp [ptr,Expr.eval,Comparison.test,g.position,nz,RowOp.opcode,BinaryOp.eval,previous?,Nat.pos_of_ne_zero h,
      pointer,Nat.cast_add,Nat.cast_sub (by omega : 1 ≤ i.val)]

theorem total_read {b : Inputs} {m : Memory W} {pos origin item site : Fin N → ℕ}
    {paid entry tail head : ℕ → ℕ}
    (g : Geography b m pos origin item site paid entry tail head) (i : Fin N) :
    (total b).eval m (i.val:Word W)=(site i:Word W)+carried (fun j=>(site j:Word W)) i (previous? pos g.previousRow i) := by
  by_cases h : pos i=0
  · simp [total,Expr.eval,Comparison.test,g.position,g.items,h,g.initial i h,g.source i h,previous?,carried]
  · have positive := Nat.pos_of_ne_zero h
    have nz : (pos i:Word W)≠0 := by
      intro eq
      apply h
      simpa only [Fin.val_cast_of_lt (g.positionFits i),Fin.val_zero] using congrArg Fin.val eq
    have ed : (edge b).eval m (i.val:Word W)=(paid (origin i+(pos i-1)):Word W) := by
      change b.occurrenceEdge.read m (b.origin.eval m (i.val:Word W)+(b.rawPosition.eval m (i.val:Word W)-1))=_
      rw [g.origins,g.position]
      simpa only [Nat.cast_add,Nat.cast_sub (by omega : 1 ≤ pos i),Nat.cast_one] using g.edgeAt i positive
    simp only [total,Expr.eval,Comparison.test,g.position,beq_iff_eq,Nat.cast_zero,ite_eq_right nz,RowOp.opcode,
      BinaryOp.eval,ed,g.tailAt i positive,g.headAt i positive,previous?,dite_eq_left positive,carried,previous]
    simpa only [Nat.cast_add] using congrArg (fun x : ℕ=>(x:Word W)) (g.adjacent i positive)

theorem run (initial : ℕ) (b : Inputs) (m : Memory W) (pos origin item site : Fin N → ℕ)
    (paid entry tail head : ℕ → ℕ)
    (g : Geography b m pos origin item site paid entry tail head)
    (inputs : ∀ e ∈ terms initial (initial+1+2*N) b,e.Fits W initial)
    (space : initial+1+3*N < 2^W) :
    ∃ out,(program W N initial b).Exec m out (ticks N initial b) ∧
      (∀ i : Fin N,out (initial+1+2*N+i.val)=(site i:Word W)) ∧
      ∀ a,a < initial ∨ initial+1+3*N ≤ a → out a=m a := by
  let dst := initial+1+2*N
  let es := terms initial dst b
  let blank := ProtocolRAM.image initial 1 (.lit 0) m
  let ms := ProtocolRAM.result (columns N (initial+1) es) blank
  let prev := previous? pos g.previousRow
  let answer (i : Fin N) : Word W := site i
  have init : (scan W initial 1 (.lit 0)).Exec m blank 10 := scan_exec initial 1 (.lit 0) m trivial (by omega)
  have prep : (ProtocolRAM.program W (columns N (initial+1) es)).Exec blank ms (ProtocolRAM.clock (columns N (initial+1) es)) :=
    columns_exec es blank (columns_safe es (Nat.le_succ initial) inputs (by dsimp [es,terms];omega))
  have atF (j : Fin 2) (i : Fin N) :
      ms (initial+1+j.val*N+i.val)=(es[j.val]'(by exact j.isLt)).eval m (i.val:Word W) := by
    have eread := columns_read es blank (Nat.le_succ initial) inputs j.val (show j.val<es.length from j.isLt) i
    exact eread.trans (ProtocolRAM.eval_below _ _ m blank
      (inputs _ (List.getElem_mem ..)) (fun a ha=>ProtocolRAMGeneratedWrite.frame_image initial 1 _ m a (.inl ha)))
  have zeroAt : ms initial=0 := by
    rw [show ms initial=blank initial from columns_frame es blank (.inl (by omega))]
    have read := ProtocolRAMGeneratedWrite.read_image initial 1 (.lit 0) m (0 : Fin 1)
    change blank (initial+0)=(0:Word W) at read
    simpa only [Nat.add_zero] using read
  have ptrAt (i : Fin N) : ms (initial+1+i.val)=(pointer dst initial i (prev i):Word W) := by
    have h := atF 0 i
    change ms (initial+1+0*N+i.val)=(ptr initial dst b).eval m (i.val:Word W) at h
    simpa only [Nat.zero_mul,Nat.add_zero] using h.trans (ptr_read g initial dst i)
  have sumAt (i : Fin N) : ms (initial+1+N+i.val)=answer i+carried answer i (prev i) := by
    have h := atF 1 i
    change ms (initial+1+1*N+i.val)=(total b).eval m (i.val:Word W) at h
    simpa only [Nat.one_mul] using h.trans (total_read g i)
  have loop : (ProtocolRAMTurnWalk.program W (initial+1) (initial+1+N) dst N).Exec ms
      (ProtocolRAMTurnWalk.image dst answer ms N) (3+14*N) :=
    ProtocolRAMTurnWalk.run _ _ dst initial answer prev ms (by dsimp [dst];omega) (by dsimp [dst];omega)
      (by dsimp [dst];omega) (by dsimp [dst];omega) zeroAt ptrAt sumAt
  refine ⟨_,?_,fun i=>site_read dst answer ms N le_rfl i i.isLt,?_⟩
  · have first : ((scan W initial 1 (.lit 0)).seq (ProtocolRAM.program W (columns N (initial+1) es))).Exec m ms
        (10+ProtocolRAM.clock (columns N (initial+1) es)) := Procedure.Exec.then init prep
    intro P R K mach pc reg pub out installed data cfg raw enter same
    exact Procedure.Exec.then first loop mach pc reg pub out installed data cfg raw enter same
  · intro a ha
    exact (ProtocolRAMTurnWalk.frame dst answer ms N a (by dsimp [dst];omega)).trans
      ((columns_frame es blank (by dsimp [es,terms];omega)).trans
        (ProtocolRAMGeneratedWrite.frame_image initial 1 _ m a (by omega)))

end Hierarchy.ProtocolRAMVisitColumns

end OAI
