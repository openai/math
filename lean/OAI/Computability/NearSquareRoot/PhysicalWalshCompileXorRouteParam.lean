import OAI.Computability.NearSquareRoot.PhysicalWalshCompileXorConjugate

/-! # Directed Walsh routing with an external arithmetic calibration -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileXorRoute
open IntegerMultiplication Code KernelPass.ComputableSyntax PhysicalWalshNode PhysicalWalshContext
open GeneratorSyntax CommonRegisters PhysicalWalshNode.Route
open private effective_if effective_exchange from OAI.Computability.NearSquareRoot.PhysicalWalshCompileXorSelect

variable {Z : Type} [Primcodable Z]

private theorem orderedWith (skip : Cmd) {swap : Z × SwapArgs → Cmd} (hs : Effective ltr swap) :
    Effective ltr (fun t : Z × SwapArgs => ordered skip (fun k => swap (t.1,k)) t.2) := by
  let x (t : Z × SwapArgs) := t.2.2.1
  let y (t : Z × SwapArgs) := t.2.2.2
  have hx : Primrec x := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hy : Primrec y := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have raw : Primrec (fun t : Z × SwapArgs => t.2.1) := Primrec.fst.comp Primrec.snd
  exact effective_if (Primrec.eq.comp hx hy) (effective_const _ _)
    (effective_if (Primrec.nat_lt.comp hy hx) hs (hs.comp (Primrec.fst.pair (raw.pair (hy.pair hx))).to_comp))

private def emitWith (K : Kit) (swap : Z × SwapArgs → Cmd) (front : Z × Raw → Cmd)
    (e : Z × Raw) (op : Op) :=
  emit K.chain K.erase (fun k => swap (e.1,k)) (fun raw => front (e.1,raw))
    (canonicalTarget ∘ Prod.fst) (canonicalSource ∘ Prod.fst) e.2 op

private theorem effectiveEmitWith (K : Kit) {swap : Z × SwapArgs → Cmd} {front : Z × Raw → Cmd}
    (hs : Effective ltr swap) (hf : Effective ltr front) :
    Effective ltr (Function.uncurry (emitWith K swap front)) := by
  let X := (Z × Raw) × Op
  have par : Computable (fun e : X => e.1.1) := Computable.fst.comp Computable.fst
  have raw : Computable (fun e : X => e.1.2) := Computable.snd.comp Computable.fst
  have src : Primrec (fun e : X => arg e.2 1) := primrec_arg.comp Primrec.snd (.const 1)
  have dst : Primrec (fun e : X => arg e.2 0) := primrec_arg.comp Primrec.snd (.const 0)
  have a := Computable.fst.comp raw
  have u := primrec_canonicalSource.to_comp.comp a
  have t := primrec_canonicalTarget.to_comp.comp a
  have s := orderedWith K.erase hs
  have f := s.comp (par.pair (raw.pair (src.to_comp.pair u)))
  have g := s.comp (par.pair (raw.pair ((effective_exchange src.to_comp u dst.to_comp).pair t)))
  exact effective_if (Primrec.eq.comp dst src) (effective_const _ _)
    (K.effective_chain (K.effective_chain (K.effective_chain (K.effective_chain f g) (hf.comp Computable.fst)) g) f)

/-- The external calibration is available when emitting every one of the five
tables. The execution keeps the same node packet, clock and parked-data bound as the
uncalibrated conjugation. -/
theorem compileWith (swap : Z × SwapArgs → Cmd) (front : Z × Raw → Cmd)
    (hs : Effective ltr swap) (hg : Effective ltr front) (N : ℕ)
    (rs : ∀ k, Within N (swap k)) (rg : ∀ k, Within N (front k)) :
    ∃ (route : Z × Raw → Op → Cmd) (M : ℕ), Effective ltr (Function.uncurry route) ∧
      (∀ k op, Within M (route k op)) ∧
      ∀ (z : Z) (a W : ℕ) (ops : List Op) (scan arena : PhysicalWalshNode.Shape → ℕ),
        (∀ s, arena s ≤ scan s) →
        (∀ s, routeArena (coords a W) PhysicalWalshNode.Shape.w (Header.wire (a+1)) s ≤ arena s) →
        (∀ i j : Fin (a+1), j < i → Flat (a:=a) (W:=W) scan arena (axisSwap i j)
          (swap (z,(a+1,ops),i.val,j.val))) →
        (0 < a → Flat (a:=a) (W:=W) scan arena (PhysicalWalshNode.xor a (targetAxis a,sourceAxis a))
          (front (z,a+1,ops))) →
        ∀ (op : Op) (hd : arg op 0 < a+1) (hs : arg op 1 < a+1),
          PhysicalWalshCompileXorPacket.FlatRuns (W:=W) scan arena (⟨_,hd⟩,⟨_,hs⟩) (route (z,a+1,ops) op) := by
  obtain ⟨K,R,hK⟩ := exists_kit
  let M := max R N
  have r : R ≤ M := le_max_left ..
  have n : N ≤ M := le_max_right ..
  let target := canonicalTarget ∘ (Prod.fst : Raw → ℕ)
  let source := canonicalSource ∘ (Prod.fst : Raw → ℕ)
  refine ⟨emitWith K swap front,M,effectiveEmitWith K hs hg,?_,?_⟩
  · intro k op
    exact within_emit (fun _ _ => hK.within_chain r) (hK.within_erase r)
      (fun p => RegisterSelect.within_mono n _ (rs (k.1,p))) (fun raw => RegisterSelect.within_mono n _ (rg (k.1,raw)))
      k.2 op
  · intro z a W ops scan arena cost fit sw gate op hd hsrc
    let dst : Fin (a+1) := ⟨arg op 0,hd⟩
    let src : Fin (a+1) := ⟨arg op 1,hsrc⟩
    have pos (h : dst ≠ src) : 0 < a := by
      by_contra! ha
      have hi := dst.isLt
      have hj := src.isLt
      exact h (Fin.ext (by omega))
    apply runs_emit hK cost fit target source (a+1,ops) op dst src (targetAxis a) (sourceAxis a)
      rfl rfl rfl rfl _ sw (fun h => gate (pos h))
    exact fun h eqn => canonical_apart (pos h) (congrArg Fin.val eqn)

end PhysicalWalshCompileXorRoute

end NearSquareRoot
end Computability
end OAI
