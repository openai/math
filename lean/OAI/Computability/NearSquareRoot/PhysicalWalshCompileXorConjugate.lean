import OAI.Computability.NearSquareRoot.PhysicalWalshCompileXorSelect
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileXorRoute
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeSwapRouter

/-! # Physical correctness of the emitted five-pass Walsh column route -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileXorRoute

open IntegerMultiplication Code KernelPass.ComputableSyntax PhysicalWalshNode PhysicalWalshContext
open GeneratorSyntax CommonRegisters PhysicalWalshNode.Route

variable {K : Kit} {R a W : ℕ} {scan arena : PhysicalWalshNode.Shape → ℕ}

private theorem same_action {F G : (s : PhysicalWalshNode.Shape) → Data s → Data s} {cmd : Cmd}
    (h : Flat (a:=a) (W:=W) scan arena F cmd) (eq : ∀ s x, F s x = G s x) :
    Flat (a:=a) (W:=W) scan arena G cmd := by
  have e : F = G := funext fun s => funext (eq s)
  rwa [← e]

/-- A full interchange on any pair uses one ordered rectangle or the
descriptor-erasing identity on coincident axes. -/
theorem runs_ordered (hk : Legal K R) (cost : ∀ s, arena s ≤ scan s)
    (fit : ∀ s, routeArena (coords a W) PhysicalWalshNode.Shape.w (Header.wire (a+1)) s ≤ arena s)
    (swap : SwapArgs → Cmd) (raw : Raw)
    (swaps : ∀ i j : Fin (a+1), j < i → Flat (a:=a) (W:=W) scan arena
      (axisSwap i j) (swap (raw,i.val,j.val))) (i j : Fin (a+1)) :
    Flat (a:=a) (W:=W) scan arena (axisSwap i j) (ordered K.erase swap (raw,i.val,j.val)) := by
  by_cases eqn : i = j
  · subst j
    simpa only [ordered,ite_true] using
      same_action (hk.runs_id cost fit) (fun s x => (axisSwap_self i s x).symm)
  have diff : i.val ≠ j.val := fun h => eqn (Fin.ext h)
  by_cases ji : j.val < i.val
  · simpa only [ordered,ite_eq_right diff,ite_eq_left ji] using swaps i j ji
  · have ij : i < j := show i.val < j.val by omega
    have h := same_action (swaps j i ij) (G:=axisSwap i j) (fun s x => by
      rw [axisSwap,axisSwap,Equiv.swap_comm j i])
    simpa only [ordered,ite_eq_right diff,ite_eq_right ji] using h

/-- Both mathematical compositions and the named stack command contain the
same four slot transpositions and canonical XOR. -/
theorem runs_emit (hk : Legal K R) (cost : ∀ s, arena s ≤ scan s)
    (fit : ∀ s, routeArena (coords a W) PhysicalWalshNode.Shape.w (Header.wire (a+1)) s ≤ arena s)
    {swap : SwapArgs → Cmd} {front : Raw → Cmd} (to_ from_ : Raw → ℕ)
    (raw : Raw) (op : Op) (dst src target source : Fin (a+1))
    (hd : arg op 0 = dst.val) (hs : arg op 1 = src.val)
    (ht : to_ raw = target.val) (hu : from_ raw = source.val)
    (apart : dst ≠ src → target ≠ source)
    (swaps : ∀ i j : Fin (a+1), j < i → Flat (a:=a) (W:=W) scan arena
      (axisSwap i j) (swap (raw,i.val,j.val)))
    (gate : dst ≠ src → Flat (a:=a) (W:=W) scan arena (PhysicalWalshNode.xor a (target,source)) (front raw)) :
    PhysicalWalshCompileXorPacket.FlatRuns (W:=W) scan arena (dst,src)
      (emit K.chain K.erase swap front to_ from_ raw op) := by
  change Flat (a:=a) (W:=W) scan arena (PhysicalWalshNode.xor a (dst,src)) _
  by_cases eqn : dst = src
  · subst src
    simp only [emit,hd,hs,ite_true]
    apply same_action (hk.runs_id cost fit)
    intro s x
    funext n
    simp [PhysicalWalshNode.xor]
  have diff : dst.val ≠ src.val := fun h => eqn (Fin.ext h)
  let j := Equiv.swap src source dst
  have first := runs_ordered hk cost fit swap raw swaps src source
  have next := runs_ordered hk cost fit swap raw swaps j target
  have h := hk.runs_chain cost fit (hk.runs_chain cost fit (hk.runs_chain cost fit
    (hk.runs_chain cost fit first next) (gate eqn)) next) first
  have full := same_action h (G:=PhysicalWalshNode.xor a (dst,src)) (swap_route dst src target source eqn (apart eqn))
  simpa only [emit,hd,hs,ht,hu,ite_eq_right diff,exchange_fin,j] using full

/-- Canonical finite target and source used by the fast gate. -/
def targetAxis (a : ℕ) : Fin (a+1) := ⟨canonicalTarget (a+1), target_lt a⟩

def sourceAxis (a : ℕ) : Fin (a+1) := ⟨canonicalSource (a+1), source_lt a⟩

/-- A single, absolute-register raw compiler works for all valid source and
destination indices. Only strictly ordered swaps and the canonical gate
on each reached node are required of the two physical primitive families. -/
theorem compile (swap : SwapArgs → Cmd) (front : Raw → Cmd)
    (hs : Effective ltr swap) (hg : Effective ltr front) (N : ℕ)
    (rs : ∀ k, Within N (swap k)) (rg : ∀ raw, Within N (front raw)) :
    ∃ (route : Raw → Op → Cmd) (M : ℕ), Effective ltr (Function.uncurry route) ∧
      (∀ raw op, Within M (route raw op)) ∧
      ∀ (a W : ℕ) (ops : List Op) (scan arena : PhysicalWalshNode.Shape → ℕ)
        (_cost : ∀ s, arena s ≤ scan s),
        (∀ s, routeArena (coords a W) PhysicalWalshNode.Shape.w (Header.wire (a+1)) s ≤ arena s) →
        (∀ i j : Fin (a+1), j < i → Flat (a:=a) (W:=W) scan arena (axisSwap i j)
          (swap ((a+1,ops),i.val,j.val))) →
        (0 < a → Flat (a:=a) (W:=W) scan arena (PhysicalWalshNode.xor a (targetAxis a,sourceAxis a))
          (front (a+1,ops))) →
        ∀ (op : Op) (hd : arg op 0 < a+1) (hs : arg op 1 < a+1),
          PhysicalWalshCompileXorPacket.FlatRuns (W:=W) scan arena (⟨_,hd⟩,⟨_,hs⟩) (route (a+1,ops) op) := by
  obtain ⟨K,R,hK⟩ := exists_kit
  let M := max R N
  have r : R ≤ M := le_max_left ..
  have n : N ≤ M := le_max_right ..
  let target := canonicalTarget ∘ (Prod.fst : Raw → ℕ)
  let source := canonicalSource ∘ (Prod.fst : Raw → ℕ)
  refine ⟨emit K.chain K.erase swap front target source,M,
    effective_emit (fun hf hg => K.effective_chain hf hg) hs hg
      (primrec_canonicalTarget.to_comp.comp Computable.fst) (primrec_canonicalSource.to_comp.comp Computable.fst),
    within_emit (fun _ _ => hK.within_chain r) (hK.within_erase r)
      (fun k => RegisterSelect.within_mono n _ (rs k)) (fun raw => RegisterSelect.within_mono n _ (rg raw)),?_⟩
  intro a W ops scan arena cost fit sw gate op hd hs
  let dst : Fin (a+1) := ⟨arg op 0,hd⟩
  let src : Fin (a+1) := ⟨arg op 1,hs⟩
  have pos (h : dst ≠ src) : 0<a := by
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
