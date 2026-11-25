import OAI.Computability.NearSquareRoot.PhysicalWalshCompileChildRun

/-! # Effective choice of the five physical passes for a directed column XOR -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileXorRoute

open IntegerMultiplication Code KernelPass.ComputableSyntax CommonRegisters GeneratorSyntax

/-- A slot-interchange primitive is indexed by its enclosing template and two
axis numbers. The caller requests only pairs with a larger first index. -/
abbrev SwapArgs := Raw × ℕ × ℕ

private theorem effective_if {X : Type} [Primcodable X] {f g : X → Cmd} {p : X → Prop}
    [DecidablePred p] (hp : PrimrecPred p) (hf : Effective ltr f) (hg : Effective ltr g) :
    Effective ltr (fun x => if p x then f x else g x) :=
  (Computable.cond hp.decide.to_comp hf hg).of_eq (fun x => by by_cases h : p x <;> simp [h])

/-- Order a swap request for the physical primitive, with a separate
descriptor-erasing command for a repeated slot. -/
def ordered (skip : Cmd) (swap : SwapArgs → Cmd) (e : SwapArgs) :=
  if e.2.1 = e.2.2 then skip
  else if e.2.2 < e.2.1 then swap e else swap (e.1,e.2.2,e.2.1)

theorem effective_ordered (skip : Cmd) {swap : SwapArgs → Cmd} (hs : Effective ltr swap) :
    Effective ltr (ordered skip swap) := by
  let x : SwapArgs → ℕ := fun e => e.2.1
  let y : SwapArgs → ℕ := fun e => e.2.2
  have hx : Primrec x := Primrec.fst.comp Primrec.snd
  have hy : Primrec y := Primrec.snd.comp Primrec.snd
  exact effective_if (Primrec.eq.comp hx hy) (effective_const _ _)
    (effective_if (Primrec.nat_lt.comp hy hx) hs (hs.comp (Primrec.fst.pair (hy.pair hx)).to_comp))

theorem within_ordered {R : ℕ} {skip : Cmd} {swap : SwapArgs → Cmd}
    (hz : Within R skip) (hs : ∀ e, Within R (swap e)) (e : SwapArgs) :
    Within R (ordered skip swap e) := by unfold ordered; split_ifs <;> first | assumption | apply hs

/-- The destination's new number after interchanging the source with the
canonical source slot. -/
def exchange (src newSrc dst : ℕ) := if dst=src then newSrc else if dst=newSrc then src else dst

private theorem effective_exchange {X : Type} [Primcodable X] {f g h : X → ℕ}
    (hf : Computable f) (hg : Computable g) (hh : Computable h) :
    Computable (fun x => exchange (f x) (g x) (h x)) := by
  have eq (a b : X → ℕ) (ha : Computable a) (hb : Computable b) :
      Computable (fun x => decide (a x = b x)) := Primrec.eq.decide.to_comp.comp ha hb
  exact (Computable.cond (eq h f hh hf) hg (Computable.cond (eq h g hh hg) hf hh)).of_eq
    (fun x => by simp only [exchange, Bool.cond_decide])

theorem exchange_fin {A : ℕ} (src newSrc dst : Fin A) :
    exchange src newSrc dst = (Equiv.swap src newSrc dst).val := by
  simp only [Equiv.swap_apply_def,exchange,Fin.val_inj]
  split_ifs <;> rfl

/-- Conjugate a canonical gate by two swaps. Their reverse order restores
each record to the original slot coordinates. -/
def emit (link : Cmd → Cmd → Cmd) (skip : Cmd) (swap : SwapArgs → Cmd) (front : Raw → Cmd)
    (target source : Raw → ℕ) (raw : Raw) (op : Op) : Cmd :=
  let dst := arg op 0
  let src := arg op 1
  if dst = src then skip else
    let first := ordered skip swap (raw,src,source raw)
    let next := ordered skip swap (raw,exchange src (source raw) dst,target raw)
    link (link (link (link first next) (front raw)) next) first

theorem effective_emit {link : Cmd → Cmd → Cmd} {skip : Cmd} {swap : SwapArgs → Cmd}
    {front : Raw → Cmd} {target source : Raw → ℕ}
    (hl : ∀ {f g : Raw × Op → Cmd}, Effective ltr f → Effective ltr g →
      Effective ltr (fun x => link (f x) (g x)))
    (hs : Effective ltr swap) (hf : Effective ltr front) (ht : Computable target)
    (hu : Computable source) : Effective ltr (Function.uncurry (emit link skip swap front target source)) := by
  have src : Primrec (fun e : Raw × Op => arg e.2 1) := primrec_arg.comp Primrec.snd (.const 1)
  have dst : Primrec (fun e : Raw × Op => arg e.2 0) := primrec_arg.comp Primrec.snd (.const 0)
  have u := hu.comp (Computable.fst (α:=Raw) (β:=Op))
  have t := ht.comp (Computable.fst (α:=Raw) (β:=Op))
  have s := effective_ordered skip hs
  have f := s.comp (Computable.fst.pair (src.to_comp.pair u))
  have g := s.comp (Computable.fst.pair ((effective_exchange src.to_comp u dst.to_comp).pair t))
  exact effective_if (Primrec.eq.comp dst src) (effective_const _ _) (hl (hl (hl (hl f g) (hf.comp Computable.fst)) g) f)

theorem within_emit {R : ℕ} {link : Cmd → Cmd → Cmd} {skip : Cmd} {swap : SwapArgs → Cmd}
    {front : Raw → Cmd} {target source : Raw → ℕ}
    (hl : ∀ c d, Within R c → Within R d → Within R (link c d))
    (hz : Within R skip) (hs : ∀ e, Within R (swap e)) (hf : ∀ r, Within R (front r))
    (raw : Raw) (op : Op) : Within R (emit link skip swap front target source raw op) := by
  simp only [emit]
  split
  · exact hz
  · exact hl _ _ (hl _ _ (hl _ _ (hl _ _ (within_ordered hz hs _) (within_ordered hz hs _))
      (hf _)) (within_ordered hz hs _)) (within_ordered hz hs _)

/-- At arity at least three the canonical directed pair is (2,1). At arity
two the same compiler selects (1,0). -/
def canonicalTarget (A : ℕ) := if 2 < A then 2 else A-1

def canonicalSource (A : ℕ) := if 2 < A then 1 else 0

theorem primrec_canonicalTarget : Primrec canonicalTarget :=
  Primrec.ite (Primrec.nat_lt.comp (.const 2) Primrec.id) (.const 2)
    (Primrec.nat_sub.comp Primrec.id (.const 1))

theorem primrec_canonicalSource : Primrec canonicalSource :=
  Primrec.ite (Primrec.nat_lt.comp (.const 2) Primrec.id) (.const 1) (.const 0)

theorem target_lt (a : ℕ) : canonicalTarget (a+1) < a+1 := by unfold canonicalTarget; split <;> omega

theorem source_lt (a : ℕ) : canonicalSource (a+1) < a+1 := by unfold canonicalSource; split <;> omega

theorem canonical_apart {a : ℕ} (ha : 0<a) : canonicalTarget (a+1) ≠ canonicalSource (a+1) := by
  unfold canonicalTarget canonicalSource; split <;> omega

end PhysicalWalshCompileXorRoute

end NearSquareRoot
end Computability
end OAI
