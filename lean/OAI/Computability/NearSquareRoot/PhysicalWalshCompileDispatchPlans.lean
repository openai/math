import OAI.Computability.NearSquareRoot.PhysicalWalshCompileDispatch
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileXorPacket
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileFamily

/-! # Emitting the normalized Walsh successor kernel on its reached lanes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.Dispatch

open IntegerMultiplication Code Space KernelPass KernelPass.ComputableSyntax
open PhysicalWalsh PhysicalWalshNode PhysicalWalshContext GeneratorSyntax CommonRegisters

/-- Only distinct, in-range XOR axes require the external flat permutation.
The physical header contains the shape of the currently reached invocation. -/
def XorRuns (flat : Raw → Op → Cmd) (a W : ℕ) (ops : List Op)
    (scan arena : PhysicalWalshNode.Shape → ℕ) : Prop :=
  ∀ op : Op, op.1 = 1 → ∀ (ha : arg op 0 < a+1) (hb : arg op 1 < a+1), arg op 0 ≠ arg op 1 →
    PhysicalWalshCompileXorPacket.FlatRuns (a:=a) (W:=W) scan arena (⟨_,ha⟩,⟨_,hb⟩)
      (flat (a+1,ops) op)

/-- The named plan body leaves both headers in place, acts on the real parent
lanes, and charges one unit of recursive time for each syntactic child call. -/
def Body {a W : ℕ} (hw : 0<W) (p : Plan (a+1) W W) (scan arena : PhysicalWalshNode.Shape → ℕ)
    (cost : ∀ s, arena s ≤ scan s) (cmd : Cmd) : Prop :=
  let vm := spec hw p scan arena cost
  let u := fun t : vm.Step => t.val.shape
  let src := fun t : vm.Step => lane (a+1) W (u t) t.val.row
  let dst := fun t : vm.Step => (nodeOps hw p).applyPlan p (u t) (src t)
  Runs cmd vm.meter p.calls u (fun t => send (packet (work a W) (u t) (src t)))
    (fun t => send (packet (work a W) (u t) (dst t)))

/-- A total file generator compiles the entire raw prefix plan on a fixed
register bank. Its only realization premise is the named off-diagonal XOR
on the ordered flat stream returned by the address permutation. -/
theorem plansWith {Z : Type} [Primcodable Z] (flat : Z × Raw → Op → Cmd) (effective : Effective ltr (Function.uncurry flat))
    (N : ℕ) (within : ∀ r op, Within N (flat r op)) :
    ∃ (emit : Z × Raw → Cmd) (R d : ℕ), Effective ltr emit ∧ 0 < R ∧ 1 ≤ d ∧
      (∀ raw, Within R (emit raw)) ∧
      ∀ (z : Z) (a W : ℕ) (ops : List Op) (hw : 0<W) (p : Plan (a+1) W W),
        Packed.decode (a+1) ops = ⟨W,W,p⟩ →
        ∀ (scan arena : PhysicalWalshNode.Shape → ℕ) (cost : ∀ s, arena s ≤ scan s),
          (∀ s, allowance (a+1) d s ≤ arena s) →
          (∀ s, routeArena (coords a W) PhysicalWalshNode.Shape.w (Header.wire (a+1)) s ≤ arena s) →
          XorRuns (fun r => flat (z,r)) a W ops scan arena → Body hw p scan arena cost (emit (z,a+1,ops)) := by
  obtain ⟨wrap,Rw,ew,rw,runWrap⟩ := PhysicalWalshCompileXorPacket.compileWith flat effective N within
  obtain ⟨leaf,Rl,d,el,hd,rl,runLeaf⟩ := compileWith wrap Rw ew rw
  obtain ⟨emit,R,ee,hR,reg,verified⟩ :=
    compile_family (PhysicalWalshGrid.Header × Header.Wire) (List Dusk.Pair)
      (Prod.snd : Z × Raw → Raw) Computable.snd leaf el Rl rl
  refine ⟨emit,R,d,ee,hR,hd,reg,?_⟩
  intro z a W ops hw p decode scan arena cost cap fit routes
  let vm := spec hw p scan arena cost
  let u (t : vm.Step) := t.val.shape
  let L := coords a W
  let w := PhysicalWalshNode.Shape.w
  let desc := Header.wire (a+1)
  let xc := PhysicalWalshNode.xor a
  let cc := fun axis s => run hw p (descend (a+1) W axis s)
  let xr := fun (_ : Fin (a+1) × Fin (a+1)) (s : PhysicalWalshNode.Shape) (_ : Data s) => True
  let cr := fun axis s => Good hw p (descend (a+1) W axis s)
  let f := routeOps L w desc xc cc
  let G : Guards (a+1) (work a W) := routeGuards L w desc xr cr
  let src (t : vm.Step) := lane (a+1) W (u t) t.val.row
  have leaves := runLeaf z a W ops (congrArg Packed.i decode) hw p scan arena cost cap fit
    (fun op tag ha hb ne => runWrap z a W hw p scan arena cost fit ops op tag ha hb
      (routes op tag ha hb ne))
  have body : Implements f G vm.meter u (Packed.decode (a+1) ops) (emit (z,a+1,ops)) :=
    verified (z,a+1,ops) vm.Step PhysicalWalshNode.Shape (work a W) vm.meter u f G
      (fitsLayout L w desc fit) leaves
  rw [decode] at body
  have eligible (t : vm.Step) : Ready f G p (u t) (src t) :=
    (routeReady_iff L w desc xc cc xr cr p (u t) (src t)).mpr
      (good_step hw p t.property t.val.representable)
  have result (t : vm.Step) : f.applyPlan p (u t) (src t) = (nodeOps hw p).applyPlan p (u t) (src t) :=
    routeApply_eq L w desc xc cc p (u t) (src t)
  have h := body src eligible
  change Runs (emit (z,a+1,ops)) vm.meter p.calls u
    (fun t => send (packet (work a W) (u t) (src t)))
    (fun t => send (packet (work a W) (u t) (f.applyPlan p (u t) (src t)))) at h
  change Runs (emit (z,a+1,ops)) vm.meter p.calls u
    (fun t => send (packet (work a W) (u t) (src t)))
    (fun t => send (packet (work a W) (u t) ((nodeOps hw p).applyPlan p (u t) (src t))))
  simpa only [result] using h

/-- Compile a plan whose flat router needs only the raw search record. -/
theorem plans (flat : Raw → Op → Cmd) (effective : Effective ltr (Function.uncurry flat))
    (N : ℕ) (within : ∀ r op, Within N (flat r op)) :
    ∃ (emit : Raw → Cmd) (R d : ℕ), Effective ltr emit ∧ 0 < R ∧ 1 ≤ d ∧
      (∀ raw, Within R (emit raw)) ∧
      ∀ (a W : ℕ) (ops : List Op) (hw : 0<W) (p : Plan (a+1) W W),
        Packed.decode (a+1) ops = ⟨W,W,p⟩ →
        ∀ (scan arena : PhysicalWalshNode.Shape → ℕ) (cost : ∀ s, arena s ≤ scan s),
          (∀ s, allowance (a+1) d s ≤ arena s) →
          (∀ s, routeArena (coords a W) PhysicalWalshNode.Shape.w (Header.wire (a+1)) s ≤ arena s) →
          XorRuns flat a W ops scan arena → Body hw p scan arena cost (emit (a+1,ops)) := by
  obtain ⟨emit,R,d,he,hR,hd,hr,run⟩ := plansWith (Z:=Unit) (fun k => flat k.2)
    (PhysicalWalshCompile.ignoreParameter effective) N (fun k => within k.2)
  exact ⟨fun r => emit ((),r),R,d,PhysicalWalshCompile.fixCommandParameter he (),
    hR,hd,fun r => hr ((),r),run ()⟩

end PhysicalWalshCompile.Dispatch

end NearSquareRoot
end Computability
end OAI
