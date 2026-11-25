import OAI.Computability.NearSquareRoot.ScheduleRegisterSelectCore
import OAI.Computability.NearSquareRoot.PhysicalWalshContext
import OAI.Computability.NearSquareRoot.ScheduleRegisterTagProgram

/-! # Generated scale commands in recursive routed packets -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveScale
open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshContext
open CommonRegisters GeneratorSyntax KernelEffectiveFamily Filter KernelPass KernelPass.ComputableSyntax

/-- The static prefix copies out the scale header while retaining the complete
routed header for return. Its type uses erased trees so its source is fixed. -/
abbrev Routed := ((Tree × Tree) × Tree) × Tree

def prepare (x : Routed) := (x.1,(x.1.1.2,x.2))

private theorem prepare_easy : Code.Easy prepare := by unfold prepare; fun_prop

private theorem TimedAt.runs {X U : Type} {m : Meter U} {u : X → U}
    {p q : X → Tree} {cmd : Cmd} (h : TimedAt cmd (m.arena ∘ u) p q)
    (start : ∀ x, (p x).count ≤ 4*(m.arena (u x)+1)) :
    PhysicalWalsh.Runs cmd m 0 u p q := by
  obtain ⟨C,run⟩ := h
  refine ⟨C+4,fun x env t s _ parked base cap => ?_⟩
  have size := start x
  have time : C*(m.arena (u x)+1) ≤ (C+4)*(m.scan (u x)+1) :=
    Nat.mul_le_mul (by omega) (Nat.succ_le_succ (m.arena_le _))
  apply (BoundedFits.of_fits (run x env parked)
    (cap := base+((C+4)*(m.arena (u x)+1)+s)) (depth := (C+4)*(m.arena (u x)+1)+s)
     ?_ (by dsimp only [Function.comp_apply]; rw [Nat.add_mul]; omega)).mono (by dsimp only [Function.comp_apply]; omega) le_rfl le_rfl
  intro j
  have hj := cap.pile 0 (p x) j
  dsimp only [Function.comp_apply]
  rw [Nat.add_mul]
  omega

/-- Uniform specification over all meters, descriptors and reached rows of
the structural plan compiler. -/
def RouteRuns (p : Params) (cmd : Cmd) : Prop := ∀ {U F X D : Type} [Codec D]
    (L : KernelScaleBank.Layout p.1 U F) (w : U → ℕ) (desc : U → D)
    (m : Meter U) (_fit : ∀ s, routeArena L w desc s ≤ m.arena s)
    (xor : Fin (p.1+1) × Fin (p.1+1) → ∀ s, PhysicalWalshGrid.Row L w s → PhysicalWalshGrid.Row L w s)
    (child : Fin (p.1+1) → ∀ s, PhysicalWalshGrid.Row L w s → PhysicalWalshGrid.Row L w s)
    (xr : Fin (p.1+1) × Fin (p.1+1) → ∀ s, PhysicalWalshGrid.Row L w s → Prop)
    (cr : Fin (p.1+1) → ∀ s, PhysicalWalshGrid.Row L w s → Prop)
    (u : X → U), p.2.1 = 2 →
    PhysicalWalshCompile.Implements (routeOps L w desc xor child) (routeGuards L w desc xr cr)
      m u (Packed.leaf (p.1+1) p.2) cmd

private theorem wrap {p : Params} {cmd before : Cmd}
    (h : CoreRuns p cmd) (pre : KernelEffectiveFamily.Runs before prepare) :
    RouteRuns p (before.join (rightCmd cmd)) := by
  intro U F X D inst L w desc m fit xor child xr cr u htag
  rw [Packed.leaf,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left htag]
  intro x room
  let li := PhysicalWalshGrid.reindex L u
  let wi := w ∘ u
  let inp (t : X) := x t 0
  let pred := test (tagParams p)
  let tbl := @KernelComputableSelector.table (arg p.2 0) p.2.2.2
  let out (t : X) := PhysicalWalshGrid.scale L w pred tbl (u t) (inp t)
  let hdr (t : X) := (PhysicalWalshGrid.header L w (u t),desc (u t))
  let raw (t : X) : Routed := (((send (hdr t).1.1,send (hdr t).1.2), send (hdr t).2),send (KernelScaleBank.bank li inp t))
  have body := h li wi inp out (fun t z hz => KernelScaleRecord.applyCoeff_mark _ _ (room t z hz))
  let query (t : X) := send (packet (routeLayout L w desc) (u t) (x t))
  let reply (t : X) := send (packet (routeLayout L w desc) (u t) (fun _ : Fin 1 => out t))
  have hx (t : X) : (packet (routeLayout L w desc) (u t) (x t)).2 = KernelScaleBank.bank li inp t := by
    simp [packet,KernelScaleBank.bank,li,inp,PhysicalWalshContext.routeLayout,PhysicalWalshGrid.layout,
      PhysicalWalshGrid.reindex,List.ofFn_succ]
  have hy (t : X) : (packet (routeLayout L w desc) (u t) (fun _ : Fin 1 => out t)).2 =
      KernelScaleBank.bank li out t := by
    simp [packet,KernelScaleBank.bank,li,PhysicalWalshContext.routeLayout,PhysicalWalshGrid.layout,
      PhysicalWalshGrid.reindex,List.ofFn_succ]
  have hq (t : X) : send (raw t) = query t := by
    change (send (hdr t)).fork (send (KernelScaleBank.bank li inp t)) =
      (send (hdr t)).fork (send (packet (routeLayout L w desc) (u t) (x t)).2)
    rw [hx]
  have ha (t : X) : (send (hdr t)).fork (send (KernelScaleBank.bank li out t)) = reply t := by
    change _ = (send (hdr t)).fork (send (packet (routeLayout L w desc) (u t) (fun _ : Fin 1 => out t)).2)
    rw [hy]
  have A : TimedAt before (fun t => (query t).count) query (fun t => send (prepare (raw t))) := by
    obtain ⟨C,e⟩ := pre
    refine ⟨C,fun t env => ?_⟩
    simpa only [size,hq] using e (raw t) env
  have B := body.right (fun t => send (hdr t))
  have full : TimedAt (before.join (rightCmd cmd)) (m.arena ∘ u) query reply := by
    have ab := A.join B
    have fitH := fitsLayout L w desc fit
    have ab' : TimedAt (before.join (rightCmd cmd))
        (fun i => (query i).count + ((send (hdr i)).count + KernelScaleBank.volume li wi i)) query reply := by
      obtain ⟨C,e⟩ := ab
      exact ⟨C,fun t env => by simpa only [ha] using e t env⟩
    apply ab'.bound 6
    intro t
    have v := fitH.packet (u t) (x t)
    have hh := fitH.header (u t)
    have hb : KernelScaleBank.volume li wi t ≤ m.arena (u t) := by
      apply le_trans _ (fit _)
      apply le_trans (b := PhysicalWalshGrid.budget L w (u t))
      · exact Nat.mul_le_mul_right _ (Nat.le_succ _)
      · unfold routeArena
        omega
    change (query t).count ≤ 4*(m.arena (u t)+1) at v
    change (send (hdr t)).count ≤ m.arena (u t) at hh
    dsimp only [Function.comp_apply]
    omega
  exact full.runs (fun t => (fitsLayout L w desc fit).packet (u t) (x t))

/-- Uniform source for every decoded scale leaf. -/
theorem route_family (tagsRun : ∀ᶠ R in atTop, ∃ c : Tags → Cmd, Effective ltr c ∧
    ∀ p, Within R (c p) ∧ TagRuns p (c p)) :
    ∀ᶠ R in atTop, ∃ c : Params → Cmd, Effective ltr c ∧ ∀ p, Within R (c p) ∧ RouteRuns p (c p) := by
  filter_upwards [eventually_ge_atTop 3, RegisterSelect.easy_eventually prepare_easy, core_family tagsRun]
    with R hR hp hc
  obtain ⟨cmd,hGen,run⟩ := hc
  obtain ⟨pre,hPre,C,e⟩ := hp
  exact ⟨fun p => pre.join (rightCmd (cmd p)),(effective_const ltr pre).join (effective_right hGen),
    fun p => ⟨⟨hPre,within_right hR (run p).1⟩,wrap (run p).2 ⟨C,e⟩⟩⟩

/-- The complete scale emitter is computable jointly in the arity and opcode,
uses an absolute register cutoff, and implements the reached physical leaf. -/
theorem compile : ∀ᶠ R in atTop, ∃ c : Params → Cmd, Effective ltr c ∧
    ∀ p, Within R (c p) ∧ RouteRuns p (c p) :=
  route_family RegisterTagProgram.generate

end EffectiveScale

end NearSquareRoot
end Computability
end OAI
