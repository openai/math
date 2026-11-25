import OAI.Computability.NearSquareRoot.PhysicalWalshCompileParameters
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileChildRun
import OAI.Computability.NearSquareRoot.KernelEffectiveMixBankOpcode
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelectRoute
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeRouteIO

/-! # Effective dispatch of physical Walsh instructions

The bounded tape program follows the total prefix decoder, including its
zero-row convention for malformed axes and the identity on a diagonal XOR.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.Dispatch

open IntegerMultiplication Code Space KernelPass KernelPass.ComputableSyntax
open PhysicalWalsh PhysicalWalshNode PhysicalWalshContext PhysicalWalshCompileChild
open CommonRegisters GeneratorSyntax Filter

/-- A literal one-by-one matrix whose unique entry defaults to the zero dyadic. -/
def zeroOpcode : Op := (0,[1,1],[])

@[simp] theorem leaf_zeroOpcode (A : ℕ) : Packed.leaf A zeroOpcode = Packed.zeroRow A := by
  simp [zeroOpcode,Packed.leaf,Packed.zeroRow,arg,List.getD,KernelComputableDyadic.zero,
    KernelComputableDyadic.coefficient]
  rfl

/-- All control decisions use natural operands of the finite instruction. -/
def dispatch (mix : Op → Cmd) (scale : EffectiveScale.Params → Cmd)
    (xorCode child : Raw → Op → Cmd) (raw : Raw) (op : Op) : Cmd :=
  if op.1 = 0 then mix op
  else if op.1 = 1 then
    if arg op 0 < raw.1 ∧ arg op 1 < raw.1 then
      if arg op 0 = arg op 1 then .pass else xorCode raw op
    else mix zeroOpcode
  else if op.1 = 2 then scale (raw.1-1,op)
  else if op.1 = 3 then
    if arg op 0 < raw.1 then child raw op else mix zeroOpcode
  else .pass

private theorem effectiveIf {X : Type} [Primcodable X] {f g : X → Cmd} {p : X → Prop}
    [DecidablePred p] (hp : PrimrecPred p) (hf : Effective ltr f) (hg : Effective ltr g) :
    Effective ltr (fun x => if p x then f x else g x) :=
  (Computable.cond hp.decide.to_comp hf hg).of_eq (fun x => by by_cases h : p x <;> simp [h])

private theorem effective_dispatchFor {X : Type} [Primcodable X] (raw : X → Raw) (hr : Primrec raw)
    {mix scale} {xorCode : X → Op → Cmd} {child : Raw → Op → Cmd}
    (hm : Effective ltr mix) (hs : Effective ltr scale)
    (hx : Effective ltr (Function.uncurry xorCode)) (hc : Effective ltr (Function.uncurry child)) :
    Effective ltr (fun e : X × Op => dispatch mix scale (fun _ => xorCode e.1) child (raw e.1) e.2) := by
  have A : Primrec (fun e : X × Op => (raw e.1).1) := Primrec.fst.comp (hr.comp Primrec.fst)
  have tag : Primrec (fun e : X × Op => e.2.1) := Primrec.fst.comp Primrec.snd
  have arg' (k : ℕ) : Primrec (fun e : X × Op => arg e.2 k) := primrec_arg.comp Primrec.snd (.const k)
  have sc := hs.comp ((Primrec.nat_sub.comp A (.const 1)).pair Primrec.snd).to_comp
  exact effectiveIf (Primrec.eq.comp tag (.const 0)) (hm.comp Computable.snd)
    (effectiveIf (Primrec.eq.comp tag (.const 1))
      (effectiveIf ((Primrec.nat_lt.comp (arg' 0) A).and (Primrec.nat_lt.comp (arg' 1) A))
        (effectiveIf (Primrec.eq.comp (arg' 0) (arg' 1)) (effective_const ltr .pass) hx)
        (effective_const ltr (mix zeroOpcode)))
      (effectiveIf (Primrec.eq.comp tag (.const 2)) sc
        (effectiveIf (Primrec.eq.comp tag (.const 3))
          (effectiveIf (Primrec.nat_lt.comp (arg' 0) A) (hc.comp ((hr.to_comp.comp Computable.fst).pair Computable.snd)) (effective_const ltr (mix zeroOpcode)))
          (effective_const ltr .pass))))

theorem effective_dispatch {mix scale xorCode child}
    (hm : Effective ltr mix) (hs : Effective ltr scale)
    (hx : Effective ltr (Function.uncurry xorCode)) (hc : Effective ltr (Function.uncurry child)) :
    Effective ltr (Function.uncurry (dispatch mix scale xorCode child)) :=
  effective_dispatchFor id Primrec.id hm hs hx hc

theorem within_dispatch {R : ℕ} {mix scale xorCode child}
    (hm : ∀ op, Within R (mix op)) (hs : ∀ p, Within R (scale p))
    (hx : ∀ raw op, Within R (xorCode raw op)) (hc : ∀ raw op, Within R (child raw op))
    (raw : Raw) (op : Op) : Within R (dispatch mix scale xorCode child raw op) := by
  unfold dispatch
  split_ifs <;> first | apply hm | apply hs | apply hx | apply hc | trivial

private theorem diagonal {a W : ℕ} (hw : 0<W) (p : Plan (a+1) W W)
    (scan arena : PhysicalWalshNode.Shape → ℕ) (cost : ∀ s, arena s ≤ scan s)
    (fit : ∀ s, routeArena (coords a W) PhysicalWalshNode.Shape.w (Header.wire (a+1)) s ≤ arena s)
    (op : Op) (tag : op.1 = 1) (valid : arg op 0 < a+1) (eqn : arg op 0 = arg op 1) :
    PhysicalWalshCompileChild.LeafRuns hw p scan arena cost op .pass := by
  let vm := spec hw p scan arena cost
  let u (t : vm.Step) := t.val.shape
  let i : Fin (a+1) := ⟨arg op 0,valid⟩
  let L := work a W
  have same : Packed.leaf (a+1) op = ⟨1,1,Plan.xor (i,i)⟩ := by
    simp [Packed.leaf,tag,←eqn,valid,i]
  dsimp only [PhysicalWalshCompileChild.LeafRuns]
  rw [same]
  intro x _
  have row (t : vm.Step) : (fun _ : Fin 1 => PhysicalWalshNode.xor a (i,i) (u t) (x t 0)) = x t := by
    funext j n
    rw [show j=0 from Subsingleton.elim _ _]
    change x t 0 (xorIndex a (i,i) (u t) n) = x t 0 n
    rw [xorIndex_diag]
  change Runs .pass vm.meter 0 u (fun t => send (packet L (u t) (x t)))
    (fun t => send (packet L (u t) (fun _ : Fin 1 => PhysicalWalshNode.xor a (i,i) (u t) (x t 0))))
  simp only [row]
  refine ⟨4, fun t env clock space _ park base hp => ?_⟩
  have small := (fitsLayout (m:=vm.meter) (coords a W) PhysicalWalshNode.Shape.w (Header.wire (a+1)) fit).packet (u t) (x t)
  change (send (packet L (u t) (x t))).count ≤ 4*(arena (u t)+1) at small
  apply (BoundedFits.pass (env := env) ((hp.pile 0 (send (packet L (u t) (x t)))).mono
    (by omega : base + _ ≤ base+(4*(arena (u t)+1)+space)))).mono _ le_rfl le_rfl
  change 1 ≤ 4*(scan (u t)+1)+0*clock
  omega

/-- All valid and malformed instructions are covered. The only external
routine is the non-diagonal physical XOR permutation. -/
theorem compileWith {Z : Type} [Primcodable Z] (xorCode : Z × Raw → Op → Cmd) (N : ℕ)
    (effective : Effective ltr (Function.uncurry xorCode)) (within : ∀ r op, Within N (xorCode r op)) :
    ∃ (emit : Z × Raw → Op → Cmd) (R d : ℕ), Effective ltr (Function.uncurry emit) ∧
      1 ≤ d ∧ (∀ raw op, Within R (emit raw op)) ∧
      ∀ (z : Z) (a W : ℕ) (ops : List Op), (Packed.decode (a+1) ops).i = W →
        ∀ (hw : 0<W) (p : Plan (a+1) W W) (scan arena : PhysicalWalshNode.Shape → ℕ)
          (cost : ∀ s, arena s ≤ scan s), (∀ s, allowance (a+1) d s ≤ arena s) →
          (∀ s, routeArena (coords a W) PhysicalWalshNode.Shape.w (Header.wire (a+1)) s ≤ arena s) →
          (∀ op, op.1 = 1 → arg op 0 < a+1 → arg op 1 < a+1 → arg op 0 ≠ arg op 1 →
            PhysicalWalshCompileChild.LeafRuns hw p scan arena cost op (xorCode (z,a+1,ops) op)) →
          ∀ op, PhysicalWalshCompileChild.LeafRuns hw p scan arena cost op (emit (z,a+1,ops) op) := by
  obtain ⟨child,Rc,d,ec,hd,hc,childOK⟩ := compileRaw
  obtain ⟨R,mixPack,scalePack,rx,rc⟩ := ((KernelEffectiveMixBank.compileRoute Header.Wire).and
    (EffectiveScale.compile.and ((eventually_ge_atTop N).and (eventually_ge_atTop Rc)))).exists
  obtain ⟨mix,em,hm⟩ := mixPack
  obtain ⟨scale,es,hs⟩ := scalePack
  refine ⟨fun k => dispatch mix scale (fun _ => xorCode k) child k.2,R,d,
    effective_dispatchFor Prod.snd Primrec.snd em es effective ec,hd,
    fun k => within_dispatch (fun op => (hm op).1) (fun k => (hs k).1)
      (fun _ op => RegisterSelect.within_mono rx _ (within k op))
      (fun raw op => RegisterSelect.within_mono rc _ (hc raw op)) k.2,?_⟩
  intro z a W ops width hw p scan arena cost cap fit xrun
  let vm := spec hw p scan arena cost
  let u (t : vm.Step) := t.val.shape
  let L := coords a W
  let w := PhysicalWalshNode.Shape.w
  let desc := Header.wire (a+1)
  let xc := PhysicalWalshNode.xor a
  let cc := fun axis s => run hw p (descend (a+1) W axis s)
  let xr := fun (_ : Fin (a+1) × Fin (a+1)) (s : PhysicalWalshNode.Shape) (_ : Data s) => True
  let cr := fun axis s => Good hw p (descend (a+1) W axis s)
  have mixOK (op : Op) (ht : op.1 = 0) : PhysicalWalshCompileChild.LeafRuns hw p scan arena cost op (mix op) :=
    (hm op).2 L w desc vm.meter fit xc cc xr cr u ht
  have zeroOK := mixOK zeroOpcode rfl
  dsimp only [PhysicalWalshCompileChild.LeafRuns] at zeroOK
  rw [leaf_zeroOpcode] at zeroOK
  intro op
  by_cases t0 : op.1=0
  · simpa [dispatch,t0] using mixOK op t0
  by_cases t1 : op.1=1
  · by_cases v0 : arg op 0<a+1
    · by_cases v1 : arg op 1<a+1
      · by_cases eqn : arg op 0=arg op 1
        · simpa [dispatch,t0,t1,v0,v1,eqn] using diagonal hw p scan arena cost fit op t1 v0 eqn
        · simpa [dispatch,t0,t1,v0,v1,eqn] using xrun op t1 v0 v1 eqn
      · simpa [PhysicalWalshCompileChild.LeafRuns,Packed.leaf,dispatch,t0,t1,v0,v1] using zeroOK
    · simpa [PhysicalWalshCompileChild.LeafRuns,Packed.leaf,dispatch,t0,t1,v0] using zeroOK
  by_cases t2 : op.1=2
  · simp only [dispatch,ite_eq_right t0,ite_eq_right t1,ite_eq_left t2,Nat.add_sub_cancel]
    exact (hs (a,op)).2 L w desc vm.meter fit xc cc xr cr u t2
  by_cases t3 : op.1=3
  · by_cases v0 : arg op 0<a+1
    · simpa [dispatch,t0,t1,t2,t3,v0] using childOK a W ops width hw p scan arena cost cap op t3 v0
    · simpa [PhysicalWalshCompileChild.LeafRuns,Packed.leaf,dispatch,t0,t1,t2,t3,v0] using zeroOK
  · simp only [PhysicalWalshCompileChild.LeafRuns,Packed.leaf,dispatch,ite_eq_right t0,ite_eq_right t1,ite_eq_right t2,ite_eq_right t3]
    exact (empty_sound (routeOps L w desc xc cc) (routeGuards L w desc xr cr) u
        (fitsLayout (m:=vm.meter) L w desc fit))

/-- Dispatch without an external routing parameter. -/
theorem compile (xorCode : Raw → Op → Cmd) (N : ℕ)
    (effective : Effective ltr (Function.uncurry xorCode)) (within : ∀ r op, Within N (xorCode r op)) :
    ∃ (emit : Raw → Op → Cmd) (R d : ℕ), Effective ltr (Function.uncurry emit) ∧
      1 ≤ d ∧ (∀ raw op, Within R (emit raw op)) ∧
      ∀ (a W : ℕ) (ops : List Op), (Packed.decode (a+1) ops).i = W →
        ∀ (hw : 0<W) (p : Plan (a+1) W W) (scan arena : PhysicalWalshNode.Shape → ℕ)
          (cost : ∀ s, arena s ≤ scan s), (∀ s, allowance (a+1) d s ≤ arena s) →
          (∀ s, routeArena (coords a W) PhysicalWalshNode.Shape.w (Header.wire (a+1)) s ≤ arena s) →
          (∀ op, op.1 = 1 → arg op 0 < a+1 → arg op 1 < a+1 → arg op 0 ≠ arg op 1 →
            PhysicalWalshCompileChild.LeafRuns hw p scan arena cost op (xorCode (a+1,ops) op)) →
          ∀ op, PhysicalWalshCompileChild.LeafRuns hw p scan arena cost op (emit (a+1,ops) op) := by
  obtain ⟨emit,R,d,he,hd,hr,run⟩ := compileWith (Z:=Unit) (fun k => xorCode k.2) N
    (PhysicalWalshCompile.ignoreParameter effective) (fun k => within k.2)
  exact ⟨fun r => emit ((),r),R,d,PhysicalWalshCompile.fixParameter he (),
    hd,fun r => hr ((),r),run ()⟩

end PhysicalWalshCompile.Dispatch

end NearSquareRoot
end Computability
end OAI
