import OAI.Hierarchy.TraceReceiverMaskBanks
import OAI.Hierarchy.TraceReceiverMaskExpr
import OAI.Hierarchy.TraceReceiverMaskOrdinal
import OAI.ThreeFlat.RAM.EffectStencils
import OAI.ThreeFlat.RAM.EffectSeedProcedure

namespace OAI
/-! # Constant-text publication of the public first-leaf mask dictionary -/

namespace Hierarchy.TraceReceiverMaskLoop
open ThreeFlat Diagonal LaneCursor LaneCursor.RowLayout
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.EffectStream RAM.PhysicalProcedure RAM.DescriptorExpr
open TraceReceiverMaskBanks TraceReceiverMaskExpr
open scoped Fin.CommRing

variable {W : ℕ}
private abbrev E (W : ℕ) := Term W 1 1

def destination (W d base : ℕ) (inverse : Bool) : E W :=
  .binary .add (.literal base) (if inverse then maskTerm W d else .result 0)

def payload (W d : ℕ) (inverse : Bool) : E W :=
  if inverse then .select .eq (.result 0) (.literal ((d+1:ℕ):Word W)) (.literal 1) (.result 0)
  else maskTerm W d

def stencil (W d base : ℕ) (inverse : Bool) : E W :=
  ExpressionEffects.pairTerm 0 (destination W d base inverse) (payload W d inverse)

def updates (lane low base : ℕ) (inverse : Bool) : List (Record W) :=
  if inverse then sparse lane low base else dense lane low base

@[simp] theorem len_updates (lane low base : ℕ) (inverse : Bool) :
    (updates (W:=W) lane low base inverse).length=count lane low := by
  cases inverse <;> simp [updates,sparse,dense]

private def expected (lane low base : ℕ) (inverse : Bool) (i : Fin (count lane low)) : Record W :=
  if inverse then ((base+(rowOffset lane low i).val : ℕ),(firstIndex (rowOffset lane low) i).val)
  else ((base+i.val : ℕ),(rowOffset lane low i).val)

attribute [local irreducible] maskTerm

set_option maxHeartbeats 1000000 in
private theorem row (lane low base : ℕ) (inverse : Bool) (i : Fin (count lane low))
    (depth : lane+low<W) (rows : count lane low<2^W) (pub : Fin 1→Word W) (m : Memory W) :
    ((destination W (lane+low) base inverse).eval pub m (fun _=>(i.val:Word W)),
      (payload W (lane+low) inverse).eval pub m (fun _=>(i.val:Word W))) =
        expected lane low base inverse i := by
  let d:=lane+low
  have offset : (rowOffset lane low i).val=TracePhysical.maskNat d i.val := TracePhysical.offset_nat _ i
  have mask : (maskTerm W d).eval pub m (fun _=>(i.val:Word W)) =
      (TracePhysical.maskNat d i.val:Word W) := eval_mask depth rows i.isLt pub m
  have idx := TraceReceiverMaskOrdinal.firstIndex_val lane low i
  change (firstIndex (rowOffset lane low) i).val = if i.val=d+1 then 1 else i.val at idx
  have cmp : Comparison.eq.test (i.val:Word W) ((d+1:ℕ):Word W) = decide (i.val=d+1) :=
    PhysicalPinsExpr.test_cast .eq i.val (d+1) (i.isLt.trans rows)
      (by dsimp [count] at rows;dsimp [d];omega)
  cases inverse with
  | false =>
    apply Prod.ext
    · change (destination W d base false).eval pub m (fun _=>(i.val:Word W))=((base+i.val:ℕ):Word W)
      simp only [destination,Bool.false_eq_true,ite_false,Term.eval_binary,Term.eval_literal,Term.eval,
        BinaryOp.eval,Nat.cast_add]
    · exact mask.trans (congrArg (fun z : ℕ=>(z:Word W)) offset.symm)
  | true =>
    apply Prod.ext
    · change (destination W d base true).eval pub m (fun _=>(i.val:Word W))=
        ((base+(rowOffset lane low i).val:ℕ):Word W)
      simp only [destination,ite_true,Term.eval_binary,Term.eval_literal,mask,offset,BinaryOp.eval,Nat.cast_add]
    · change (payload W d true).eval pub m (fun _=>(i.val:Word W)) =
        ((firstIndex (rowOffset lane low) i).val:Word W)
      simp only [payload,ite_true,Term.eval_select,Term.eval_literal,Term.eval,cmp,idx,decide_eq_true_eq]
      by_cases h : i.val=d+1 <;> simp [h]

private theorem generated (lane low base : ℕ) (inverse : Bool)
    (depth : lane+low<W) (rows : count lane low<2^W) (pub : Fin 1→Word W) (m : Memory W) :
    ExpressionEffects.records (count lane low) (destination W (lane+low) base inverse)
      (payload W (lane+low) inverse) pub m=updates lane low base inverse := by
  have eqn : updates (W:=W) lane low base inverse=List.ofFn (expected lane low base inverse) := by
    cases inverse <;> rfl
  rw [eqn]
  unfold ExpressionEffects.records
  apply congrArg List.ofFn
  funext i
  exact row lane low base inverse i depth rows pub m

def tape (lane low base tmp : ℕ) (inverse : Bool) (m : Memory W) : Memory W :=
  fillSegment tmp (2*count lane low) (packedWord tmp (updates lane low base inverse)) m

def step (W lane low base tmp : ℕ) (inverse : Bool) : Procedure W :=
  (PhysicalInputPhases.writing (stencil W (lane+low) base inverse) (fun _=>tmp) tmp
    (2*count lane low)).seq (EffectSeed.scatter W tmp (count lane low))

def applied (lane low base tmp : ℕ) (inverse : Bool) (m : Memory W) : Memory W :=
  after (tape lane low base tmp inverse m) (events (updates lane low base inverse))

def steps (W lane low base : ℕ) (inverse : Bool) :=
  let o:=count lane low
  (4+2*o*(2*(stencil W (lane+low) base inverse).binds+4))+(4+6*o)

attribute [local irreducible] Procedure.Exec

private theorem run_step (lane low base tmp : ℕ) (inverse : Bool) (m : Memory W)
    (depth : lane+low<W) (space : tmp+2*count lane low<2^W)
    (away : Safe tmp (updates (W:=W) lane low base inverse)) :
    (step W lane low base tmp inverse).Exec m (applied lane low base tmp inverse m)
      (steps W lane low base inverse) := by
  let o:=count lane low
  let d:=lane+low
  let arr:=updates (W:=W) lane low base inverse
  let a:=destination W d base inverse
  let v:=payload W d inverse
  let pub:=fun _ : Fin 1=>(tmp:Word W)
  have hr : o<2^W := by dsimp [o]; omega
  have same (i : Fin o) (scratch : Memory W) :
      (a.eval pub scratch (fun _=>(i.val:Word W)),v.eval pub scratch (fun _=>(i.val:Word W))) =
      (a.eval pub m (fun _=>(i.val:Word W)),v.eval pub m (fun _=>(i.val:Word W))) :=
    (row lane low base inverse i depth hr pub scratch).trans (row lane low base inverse i depth hr pub m).symm
  have write : (PhysicalInputPhases.writing (stencil W d base inverse) pub tmp (2*o)).Spec
      (fun x=>x=m) (fun i r=>r=fillSegment tmp (2*o) (packedWord tmp arr) i)
      (4+2*o*(2*(stencil W d base inverse).binds+4)) := PhysicalInputPhases.writing_spec (stencil W d base inverse) pub tmp (2*o) space
    (fun x=>x=m) (packedWord tmp arr) (by
      intro initial sameMem slot scratch lo hi _
      subst initial
      change (stencil W d base inverse).eval pub scratch (fun _=>slot) =
        packedWord tmp (updates lane low base inverse) slot.val
      rw [←generated lane low base inverse depth hr pub m]
      apply ExpressionEffects.pairTerm_packed 0 a v pub o tmp m scratch slot rfl lo hi space
      intro i e he
      rcases List.mem_cons.mp he with rfl|he
      · exact congrArg Prod.fst (same i scratch)
      · have eqn : e=v := List.mem_singleton.mp he
        subst e
        exact congrArg Prod.snd (same i scratch))
  have replay : (EffectSeed.scatter W tmp arr.length).Spec (fun m=>Loaded m tmp arr)
      (fun i r=>r=after i (events arr)) (4+6*arr.length) := EffectSeed.scatter_spec tmp arr (by simpa [arr] using space) away
  have loaded : Loaded (tape lane low base tmp inverse m) tmp arr := by
    simpa only [tape,arr,len_updates] using loaded_fillSegment tmp arr m
  have writing : (PhysicalInputPhases.writing (stencil W d base inverse) pub tmp (2*o)).Exec
      m (tape lane low base tmp inverse m) (4+2*o*(2*(stencil W d base inverse).binds+4)) :=
    Procedure.Spec.exec write m rfl
  have scattering : (EffectSeed.scatter W tmp o).Exec (tape lane low base tmp inverse m)
      (applied lane low base tmp inverse m) (4+6*o) := by
    have executed : (EffectSeed.scatter W tmp arr.length).Exec (tape lane low base tmp inverse m)
        (after (tape lane low base tmp inverse m) (events arr)) (4+6*arr.length) :=
      Procedure.Spec.exec replay _ loaded
    simpa only [arr,len_updates,o,applied] using executed
  exact Procedure.Exec.then (A:=PhysicalInputPhases.writing (stencil W d base inverse) pub tmp (2*o))
    (B:=EffectSeed.scatter W tmp o) writing scattering

def program (W lane low dictBase masks tmp : ℕ) : Procedure W :=
  (step W lane low dictBase tmp true).seq (step W lane low masks tmp false)

def output (lane low dictBase masks tmp : ℕ) (m : Memory W) : Memory W :=
  applied lane low masks tmp false (applied lane low dictBase tmp true m)

def work (W lane low dictBase masks : ℕ) :=
  steps W lane low dictBase true+steps W lane low masks false

theorem run (lane low dictBase masks tmp : ℕ) (m : Memory W)
    (depth : lane+low<W) (sparseRoom : dictBase+2^lane*2^low≤tmp)
    (denseRoom : masks+count lane low≤tmp) (space : tmp+2*count lane low<2^W) :
    (program W lane low dictBase masks tmp).Exec m (output lane low dictBase masks tmp m)
      (work W lane low dictBase masks) := by
  unfold program work output
  refine Procedure.Exec.then (A:=step W lane low dictBase tmp true) (B:=step W lane low masks tmp false)
    (run_step lane low dictBase tmp true m depth space ?_)
    (run_step lane low masks tmp false _ depth space ?_)
  · intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    apply Or.inl
    change ((dictBase+(rowOffset lane low i).val : ℕ) : Word W).val<tmp
    have hi := (rowOffset lane low i).isLt
    rw [Fin.val_cast_of_lt (by omega)]
    omega
  · intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    apply Or.inl
    change ((masks+i.val : ℕ) : Word W).val<tmp
    have hi := i.isLt
    rw [Fin.val_cast_of_lt (by omega)]
    omega

theorem outside (lane low dictBase masks tmp : ℕ) (m : Memory W) (x : ℕ)
    (away : x<tmp ∨ tmp+2*count lane low≤x) :
    output lane low dictBase masks tmp m x=TraceReceiverMaskBanks.image lane low dictBase masks m x := by
  let o:=count lane low
  let d:=sparse (W:=W) lane low dictBase
  let v:=dense (W:=W) lane low masks
  change after (fillSegment tmp (2*o) (packedWord tmp v) _) (events v) x=_
  rw [after_fillSegment_outside _ _ _ _ _ _ away]
  apply after_eq_at
  exact after_fillSegment_outside tmp (2*o) (packedWord tmp d) m (events d) x away

theorem frame (lane low dictBase masks tmp : ℕ) (m : Memory W) (x : ℕ)
    (sparseRoom : dictBase+2^lane*2^low≤tmp) (denseRoom : masks+count lane low≤tmp)
    (space : tmp+2*count lane low<2^W) (awayT : x<tmp ∨ tmp+2*count lane low≤x)
    (awayD : x<dictBase ∨ dictBase+2^lane*2^low≤x) (awayM : x < masks ∨ masks+count lane low≤x) :
    output lane low dictBase masks tmp m x=m x :=
  (outside lane low dictBase masks tmp m x awayT).trans
    (TraceReceiverMaskBanks.frame lane low dictBase masks m x (by omega) (by omega) awayD awayM)

private theorem binds (W depth base : ℕ) (inverse : Bool) :
    (stencil W depth base inverse).binds = if inverse then 29 else 26 := by
  cases inverse <;> simp [stencil,ExpressionEffects.pairTerm_binds,destination,payload,
    binds_mask,Term.binary,Term.select,Term.literal,Term.binds]

/-- The linked program has the same label, register and parameter counts at every width. -/
theorem fixed_size (W lane low dictBase masks tmp : ℕ) :
    (program W lane low dictBase masks tmp).labels=197 ∧
    (program W lane low dictBase masks tmp).registers=73 ∧
    (program W lane low dictBase masks tmp).slots=6 := by
  simp [program,step,Procedure.seq,PhysicalInputPhases.writing,EffectSeed.scatter,Term.labels_eq,binds]

theorem linear_work (W lane low dictBase masks : ℕ) :
    work W lane low dictBase masks = 16+248*count lane low := by
  simp [work,steps,binds]
  ring

/-- Both mask arrays and their shared two-word temporary tape fit in one high sector. -/
theorem sector_room {w lane low high : ℕ} (large : 7≤w) (depth : lane+low≤2*w+1)
    (atMost : high≤30*2^(32*w)) :
    high+2^lane*2^low+3*count lane low ≤ high+2^(32*w) ∧
    high+2^lane*2^low+3*count lane low < 2^(64*w) := by
  let e:=32*w-1
  have hspan : 2^lane*2^low ≤ 2^e := by
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega)
  have ht : 3*count lane low ≤ 2^e := by
    have h : 3*count lane low ≤ e := by dsimp [count,e]; omega
    exact h.trans Nat.lt_two_pow_self.le
  have size : 2^e+2^e=2^(32*w) := by
    rw [show 32*w=e+1 by dsimp [e]; omega,pow_succ]
    omega
  have top : 32*2^(32*w)<2^(64*w) := by
    change 2^5*2^(32*w)<2^(64*w)
    rw [←pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  omega

section Trace
variable {F : Type*} [Fintype F] [CommRing F] {w p S f lane low : ℕ}
    (hF : Fintype.card F≤2^w) (hw : 3≤w+1) (hp : p≤2^(w+1)) (base : ℕ)
    (st : Word w) (hs : S≤2^w) (hf : f≤2^(w+1)) (r k : ℕ)
    (fit : S+f≤2^(1+(lane+low)))
local notation "P" => TraceBitHeader.layout hF hw hp base st hs hf r k fit
local notation "N" => TraceBitHeader.network hF hw hp base st hs hf r k (lane+low)

theorem readouts (dictBase masks tmp : ℕ) (m : Memory W)
    (sparseRoom : dictBase+2^lane*2^low≤tmp) (denseRoom : masks+count lane low≤tmp)
    (space : tmp+2*count lane low<2^W)
    (apart : dictBase+2^lane*2^low ≤ masks ∨ masks+count lane low≤dictBase) :
    let o:=output lane low dictBase masks tmp m
    (∀ a : Occurrence N, (o (dictBase+((P).offset ((P).code a)).val)).val=((P).code a).val) ∧
    ∀ i,(o (masks+i.val)).val=((P).offset i).val := by
  have banks:=TraceReceiverMaskBanks.readouts hF hw hp base st hs hf r k fit dictBase masks m
    (by omega) (by omega) apart
  constructor
  · intro a
    have hi := ((P).offset ((P).code a)).isLt
    rw [outside lane low dictBase masks tmp m (dictBase+((P).offset ((P).code a)).val) (.inl (by omega))]
    exact banks.1 a
  · intro i
    have hi : i.val<count lane low := i.isLt
    rw [outside lane low dictBase masks tmp m (masks+i.val) (.inl (by omega))]
    exact banks.2 i

end Trace

end Hierarchy.TraceReceiverMaskLoop

end OAI
