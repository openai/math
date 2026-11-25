import OAI.Computability.NearSquareRoot.PhysicalWalshCompileParameters
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileChildRun
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileBank
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeRouteIO
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyProduct

/-! # Calling a named flat XOR command on one row of a routed node packet -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileXorPacket

open IntegerMultiplication Code Space KernelPass KernelPass.ComputableSyntax
open PhysicalWalsh PhysicalWalshNode PhysicalWalshCompile
open CommonRegisters GeneratorSyntax Filter

/-- The flat router acts on an increasing-address record list. Its clock and
workspace are separately bounded on each well-framed recursive shape. -/
def FlatRuns {a W : ℕ} (scan arena : PhysicalWalshNode.Shape → ℕ)
    (g : Fin (a+1) × Fin (a+1)) (c : Cmd) : Prop :=
  ClosedRuns c (fun t : XorInput W => scan t.shape) (fun t => arena t.shape)
    (fun t => .fork (send (Header.wire (a+1) t.shape)) (send (laneFlat (a+1) W t.shape t.row)))
    (fun t => send (laneFlat (a+1) W t.shape (xor a g t.shape t.row)))

open private prep done_ prep_easy done_easy from OAI.Computability.NearSquareRoot.PhysicalWalshNodeRouteIO
open private Scans.atInput from OAI.Computability.NearSquareRoot.PhysicalWalshCompileSound

private theorem assemble {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)
    (scan arena : PhysicalWalshNode.Shape → ℕ) (cost : ∀ s, arena s ≤ scan s)
    (fit : ∀ s, PhysicalWalshContext.routeArena (coords a W) PhysicalWalshNode.Shape.w
      (Header.wire (a+1)) s ≤ arena s)
    (op : Op) (tag : op.1 = 1) (ha : arg op 0 < a+1) (hb : arg op 1 < a+1)
    {before body after : Cmd} (front : Scans before prep) (back : Scans after done_)
    (flatRun : FlatRuns (W := W) scan arena (⟨arg op 0,ha⟩,⟨arg op 1,hb⟩) body) :
    PhysicalWalshCompileChild.LeafRuns hw p scan arena cost op ((before.join (left body)).join after) := by
  let g : Fin (a+1) × Fin (a+1) := (⟨arg op 0,ha⟩,⟨arg op 1,hb⟩)
  dsimp only [PhysicalWalshCompileChild.LeafRuns]
  rw [show Packed.leaf (a+1) op = ⟨1,1,Plan.xor g⟩ by simp [Packed.leaf,tag,ha,hb,g]]
  intro x _
  let vm := spec hw p scan arena cost
  let u (t : vm.Step) := t.val.shape
  let L := work a W
  have room : FitsLayout vm.meter L := PhysicalWalshContext.fitsLayout _ _ _ fit
  let z (t : vm.Step) : XorInput W := ⟨u t,t.property,t.val.batches,x t 0⟩
  let y (t : vm.Step) := xor a g (u t) (x t 0)
  let hdr (t : vm.Step) := L.header (u t)
  let stream (t : vm.Step) (v : Data (u t)) := laneFlat (a+1) W (u t) v
  have storage (t : vm.Step) (v : Data (u t)) : L.store (u t) v = stream t v := by
    change ((coords a W).rows (u t)).map _ = _
    rw [coords_range a W (u t) t.property]; rfl
  have singleton (t : vm.Step) (r : Rows L (u t) 1) :
      packet L (u t) r = (hdr t,[stream t (r 0)]) := by
    rw [← storage t (r 0)]
    rfl
  have headSize (t : vm.Step) : size (hdr t) ≤ vm.meter.arena (u t) := room.header _
  have outSize (t : vm.Step) : size (stream t (y t)) ≤ vm.meter.arena (u t) := by
    rw [← storage]; exact room.row _ _
  have stage := Scans.atInput (m := vm.meter) (u := u) front (fun t => packet L (u t) (x t)) 4
    (fun t => room.packet _ _)
  have routed : Runs body vm.meter 0 u
      (fun t => .fork (send (Header.wire (a+1) (u t))) (send (stream t (x t 0))))
      (fun t => send (stream t (y t))) := Runs.closed (flatRun.on z)
  have parked := routed.left (fun t => send (hdr t)) 1 (fun t => by
    change size (hdr t) ≤ _; have := headSize t; omega)
  have unstage := Scans.atInput (m := vm.meter) (u := u) back (fun t => (stream t (y t),hdr t)) 3
    (fun t => by rw [size_prod]; dsimp only; have := outSize t; have := headSize t; omega)
  have s' : Runs before vm.meter 0 u (fun t => send (packet L (u t) (x t)))
      (fun t => .fork (.fork (send (Header.wire (a+1) (u t))) (send (stream t (x t 0)))) (send (hdr t))) := by
    convert stage using 1
    funext t
    rw [singleton]
    rfl
  have e' : Runs after vm.meter 0 u (fun t => .fork (send (stream t (y t))) (send (hdr t)))
      (fun t => send (packet L (u t) (fun _ : Fin 1 => y t))) := by
    convert unstage using 1
    funext t
    exact congrArg send (singleton t (fun _ : Fin 1 => y t))
  exact (s'.seq parked).seq e'

/-- The same two fixed scans wrap an entire uniformly generated family of
routers. They retain the routed grid header while the flat permutation runs. -/
theorem compileWith {Z : Type} [Primcodable Z] (c : Z × Raw → Op → Cmd) (he : Effective ltr (Function.uncurry c))
    (R : ℕ) (hr : ∀ raw op, Within R (c raw op)) :
    ∃ (wrap : Z × Raw → Op → Cmd) (M : ℕ), Effective ltr (Function.uncurry wrap) ∧
      (∀ raw op, Within M (wrap raw op)) ∧
      ∀ (z : Z) (a W : ℕ) (hw : 0 < W) (p : Plan (a+1) W W) (scan arena : PhysicalWalshNode.Shape → ℕ)
        (cost : ∀ s, arena s ≤ scan s),
        (∀ s, PhysicalWalshContext.routeArena (coords a W) PhysicalWalshNode.Shape.w
          (Header.wire (a+1)) s ≤ arena s) → ∀ (ops : List Op) (op : Op), op.1 = 1 →
        ∀ (ha : arg op 0 < a+1) (hb : arg op 1 < a+1),
        FlatRuns (W := W) scan arena (⟨_,ha⟩,⟨_,hb⟩) (c (z,a+1,ops) op) →
        PhysicalWalshCompileChild.LeafRuns hw p scan arena cost op (wrap (z,a+1,ops) op) := by
  obtain ⟨pre,front⟩ := exists_scanner prep_easy
  obtain ⟨post,back⟩ := exists_scanner done_easy
  obtain ⟨M,hm,hmR,hb,he'⟩ := ((eventually_gt_atTop 0).and ((eventually_ge_atTop R).and
    ((RegisterSelect.within_eventually pre).and (RegisterSelect.within_eventually post)))).exists
  refine ⟨fun raw op => (pre.join (left (c raw op))).join post,M,
    ((effective_const ltr pre).join (KernelEffectiveFamily.effective_left he)).join (effective_const ltr post),
    fun raw op => ⟨⟨hb,KernelEffectiveFamily.within_left hm (RegisterSelect.within_mono hmR _ (hr raw op))⟩,he'⟩,?_⟩
  intro z a W hw p scan arena cost fit ops op tag ha hb flatRun
  exact assemble hw p scan arena cost fit op tag ha hb front back flatRun

/-- The packet wrapper specialized to a single routing parameter. -/
theorem compile (c : Raw → Op → Cmd) (he : Effective ltr (Function.uncurry c))
    (R : ℕ) (hr : ∀ raw op, Within R (c raw op)) :
    ∃ (wrap : Raw → Op → Cmd) (M : ℕ), Effective ltr (Function.uncurry wrap) ∧
      (∀ raw op, Within M (wrap raw op)) ∧
      ∀ (a W : ℕ) (hw : 0 < W) (p : Plan (a+1) W W) (scan arena : PhysicalWalshNode.Shape → ℕ)
        (cost : ∀ s, arena s ≤ scan s),
        (∀ s, PhysicalWalshContext.routeArena (coords a W) PhysicalWalshNode.Shape.w
          (Header.wire (a+1)) s ≤ arena s) → ∀ (ops : List Op) (op : Op), op.1 = 1 →
        ∀ (ha : arg op 0 < a+1) (hb : arg op 1 < a+1),
        FlatRuns (W := W) scan arena (⟨_,ha⟩,⟨_,hb⟩) (c (a+1,ops) op) →
        PhysicalWalshCompileChild.LeafRuns hw p scan arena cost op (wrap (a+1,ops) op) := by
  obtain ⟨wrap,M,ew,rw,run⟩ := compileWith (Z:=Unit) (fun k => c k.2)
    (PhysicalWalshCompile.ignoreParameter he) R (fun k => hr k.2)
  exact ⟨fun r => wrap ((),r),M,PhysicalWalshCompile.fixParameter ew (),
    fun r => rw ((),r),run ()⟩

end PhysicalWalshCompileXorPacket

end NearSquareRoot
end Computability
end OAI
