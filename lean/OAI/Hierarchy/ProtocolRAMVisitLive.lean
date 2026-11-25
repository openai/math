import OAI.Hierarchy.ProtocolRAMVisitColumns

namespace OAI
/-! # Recovering endpoint sites on live predecessor chains -/

namespace Hierarchy.ProtocolRAMVisitLive

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM ProbeStage.Native ProtocolRAMTurnWalk
open ProtocolRAMVisitColumns (Inputs ptr terms ticks previous?)
open scoped Fin.CommRing
variable {W N : ℕ}

/-- The word produced by the native subtraction at every ordinal, including
inactive rows whose endpoint entries are arbitrary. -/
def fill (sums : Fin N → Word W) (prev : (i : Fin N) → Before i) (i : Fin N) : Word W :=
  sums i - (match prev i with
    | none => 0
    | some j => fill sums prev (previous i j))
termination_by i.val
decreasing_by exact j.isLt

theorem fill_eq (sums : Fin N → Word W) (prev : (i : Fin N) → Before i) (i : Fin N) :
    fill sums prev i = sums i - carried (fill sums prev) i (prev i) := by
  rw [fill]
  cases prev i <;> rfl

private theorem fill_live (sums : Fin N → Word W) (pos : Fin N → ℕ)
    (earlier : ∀ i : Fin N, 0 < pos i → 0 < i.val) (active : Fin N → Prop) (site : Fin N → ℕ)
    (closed : ∀ i : Fin N, 0 < pos i → active i → active ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩)
    (endpoint : ∀ i, active i → sums i =
      (site i : Word W) + carried (fun j => (site j : Word W)) i (previous? pos earlier i))
    (i : Fin N) (live : active i) : fill sums (previous? pos earlier) i = (site i : Word W) := by
  have atStep (n : ℕ) : ∀ j : Fin N, j.val=n → active j →
      fill sums (previous? pos earlier) j=(site j:Word W) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j equal current
      rw [fill_eq,endpoint j current]
      by_cases more : 0 < pos j
      · let p : Fin N := ⟨j.val-1,(Nat.sub_le ..).trans_lt j.isLt⟩
        have smaller : p.val < n := by
          have positive := earlier j more
          change j.val-1 < n
          omega
        have prior := ih p.val smaller p rfl (closed j more current)
        dsimp only [p] at prior
        simp only [previous?,dite_eq_left more,carried,previous,prior,add_sub_cancel_right]
      · simp only [previous?,dite_eq_right more,carried,add_zero,sub_zero]
  exact atStep i.val i rfl live

private theorem ptr_read (baseAddr dst : ℕ) (b : Inputs) (m : Memory W) (pos : Fin N → ℕ)
    (earlier : ∀ i : Fin N, 0 < pos i → 0 < i.val)
    (position : ∀ i, b.rawPosition.eval m (i.val:Word W)=(pos i:Word W))
    (positionFits : ∀ i, pos i<2^W) (i : Fin N) :
    (ptr baseAddr dst b).eval m (i.val:Word W)=(pointer dst baseAddr i (previous? pos earlier i):Word W) := by
  by_cases h : pos i=0
  · simp [ptr,Expr.eval,Comparison.test,position,h,previous?,pointer]
  · have nz : (pos i:Word W)≠0 := by
      intro eq
      apply h
      simpa only [Fin.val_cast_of_lt (positionFits i),Fin.val_zero] using congrArg Fin.val eq
    have prev := earlier i (Nat.pos_of_ne_zero h)
    simp [ptr,Expr.eval,Comparison.test,position,nz,RowOp.opcode,BinaryOp.eval,previous?,Nat.pos_of_ne_zero h,
      pointer,Nat.cast_add,Nat.cast_sub (by omega : 1 ≤ i.val)]

private theorem run_words (baseAddr : ℕ) (b : Inputs) (m : Memory W) (prev : (i : Fin N) → Before i)
    (answer : Fin N → Word W)
    (pointers : ∀ i, (ptr baseAddr (baseAddr+1+2*N) b).eval m (i.val:Word W) =
      (pointer (baseAddr+1+2*N) baseAddr i (prev i):Word W))
    (sums : ∀ i, (ProtocolRAMVisitColumns.total b).eval m (i.val:Word W) = answer i + carried answer i (prev i))
    (inputs : ∀ e ∈ terms baseAddr (baseAddr+1+2*N) b, e.Fits W baseAddr) (space : baseAddr+1+3*N < 2^W) :
    ∃ out,(ProtocolRAMVisitColumns.program W N baseAddr b).Exec m out (ticks N baseAddr b) ∧
      (∀ i : Fin N, out (baseAddr+1+2*N+i.val)=answer i) ∧
      ∀ a,a<baseAddr ∨ baseAddr+1+3*N≤a → out a=m a := by
  let dst := baseAddr+1+2*N
  let es := terms baseAddr dst b
  let blank := ProtocolRAM.image baseAddr 1 (.lit 0) m
  let ms := ProtocolRAM.result (columns N (baseAddr+1) es) blank
  have init : (scan W baseAddr 1 (.lit 0)).Exec m blank 10 := scan_exec baseAddr 1 (.lit 0) m trivial (by omega)
  have prep : (ProtocolRAM.program W (columns N (baseAddr+1) es)).Exec blank ms (ProtocolRAM.clock (columns N (baseAddr+1) es)) :=
    columns_exec es blank (columns_safe es (Nat.le_succ baseAddr) inputs (by dsimp [es,terms];omega))
  have atF (j : Fin 2) (i : Fin N) :
      ms (baseAddr+1+j.val*N+i.val)=(es[j.val]'(by exact j.isLt)).eval m (i.val:Word W) := by
    have eread := columns_read es blank (Nat.le_succ baseAddr) inputs j.val (show j.val<es.length from j.isLt) i
    exact eread.trans (ProtocolRAM.eval_below _ _ m blank
      (inputs _ (List.getElem_mem ..)) (fun a ha=>ProtocolRAMGeneratedWrite.frame_image baseAddr 1 _ m a (.inl ha)))
  have zeroAt : ms baseAddr=0 := by
    rw [show ms baseAddr=blank baseAddr from columns_frame es blank (.inl (by omega))]
    have read := ProtocolRAMGeneratedWrite.read_image baseAddr 1 (.lit 0) m (0 : Fin 1)
    change blank (baseAddr+0)=(0:Word W) at read
    simpa only [Nat.add_zero] using read
  have ptrAt (i : Fin N) : ms (baseAddr+1+i.val)=(pointer dst baseAddr i (prev i):Word W) := by
    have h := atF 0 i
    change ms (baseAddr+1+0*N+i.val)=(ptr baseAddr dst b).eval m (i.val:Word W) at h
    simpa only [Nat.zero_mul,Nat.add_zero] using h.trans (pointers i)
  have sumAt (i : Fin N) : ms (baseAddr+1+N+i.val)=answer i+carried answer i (prev i) := by
    have h := atF 1 i
    change ms (baseAddr+1+1*N+i.val)=(ProtocolRAMVisitColumns.total b).eval m (i.val:Word W) at h
    simpa only [Nat.one_mul] using h.trans (sums i)
  have loop : (ProtocolRAMTurnWalk.program W (baseAddr+1) (baseAddr+1+N) dst N).Exec ms
      (ProtocolRAMTurnWalk.image dst answer ms N) (3+14*N) :=
    ProtocolRAMTurnWalk.run _ _ dst baseAddr answer prev ms (by dsimp [dst];omega) (by dsimp [dst];omega)
      (by dsimp [dst];omega) (by dsimp [dst];omega) zeroAt ptrAt sumAt
  refine ⟨_,?_,fun i=>site_read dst answer ms N le_rfl i i.isLt,?_⟩
  · have first : ((scan W baseAddr 1 (.lit 0)).seq (ProtocolRAM.program W (columns N (baseAddr+1) es))).Exec m ms
        (10+ProtocolRAM.clock (columns N (baseAddr+1) es)) := Procedure.Exec.then init prep
    intro P R K mach pc reg pub out installed data cfg raw enter same
    exact Procedure.Exec.then first loop mach pc reg pub out installed data cfg raw enter same
  · intro a ha
    exact (ProtocolRAMTurnWalk.frame dst answer ms N a (by dsimp [dst];omega)).trans
      ((columns_frame es blank (by dsimp [es,terms];omega)).trans
        (ProtocolRAMGeneratedWrite.frame_image baseAddr 1 _ m a (by omega)))

/-- Only active endpoints need geometric receipts. Every row still executes
the identical physical program and contributes its usual number of ticks. -/
theorem run (baseAddr : ℕ) (b : Inputs) (m : Memory W) (pos : Fin N → ℕ)
    (earlier : ∀ i : Fin N, 0 < pos i → 0 < i.val) (active : Fin N → Prop) (site : Fin N → ℕ)
    (position : ∀ i, b.rawPosition.eval m (i.val:Word W)=(pos i:Word W))
    (positionFits : ∀ i, pos i<2^W)
    (closed : ∀ i : Fin N, 0 < pos i → active i → active ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩)
    (endpoint : ∀ i, active i → (ProtocolRAMVisitColumns.total b).eval m (i.val:Word W) =
      (site i : Word W) + carried (fun j => (site j : Word W)) i (previous? pos earlier i))
    (inputs : ∀ e ∈ terms baseAddr (baseAddr+1+2*N) b, e.Fits W baseAddr) (space : baseAddr+1+3*N < 2^W) :
    ∃ out,(ProtocolRAMVisitColumns.program W N baseAddr b).Exec m out (ticks N baseAddr b) ∧
      (∀ i : Fin N, active i → out (baseAddr+1+2*N+i.val)=(site i:Word W)) ∧
      ∀ a,a<baseAddr ∨ baseAddr+1+3*N≤a → out a=m a := by
  let sums (i : Fin N) := (ProtocolRAMVisitColumns.total b).eval m (i.val:Word W)
  let prev := previous? pos earlier
  obtain ⟨out,exec,words,frame⟩ := run_words baseAddr b m prev (fill sums prev)
    (ptr_read baseAddr _ b m pos earlier position positionFits)
    (fun i => (sub_add_cancel (sums i) (carried (fill sums prev) i (prev i))).symm.trans
      (congrArg (· + carried (fill sums prev) i (prev i)) (fill_eq sums prev i).symm)) inputs space
  exact ⟨out,exec,fun i hi => (words i).trans (fill_live sums pos earlier active site closed endpoint i hi),frame⟩

end Hierarchy.ProtocolRAMVisitLive

end OAI
