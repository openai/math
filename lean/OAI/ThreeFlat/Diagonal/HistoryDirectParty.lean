import OAI.ThreeFlat.Diagonal.HistoryPartyTrees

namespace OAI
/-! # A rooted party with its two real boundary source maps -/
namespace ThreeFlat.Diagonal.HistoryContraction.Tree

noncomputable section
open HistogramTileNetwork MotifOuterTerms LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector
open scoped Classical BigOperators

variable {F H J E S : Type} [Field F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [Fintype H] [DecidableEq H] [Nonempty H]
    {r k p e n d h : ℕ} (D : PortGraph J E) (G : Supply J S) (j : J) (w base : E → ℕ)
    (B : Header (D.Port j) H (fun q => base q.1.1) k n) (sa : Fin e ≃ (ports G).Port j) (sw : H → S → ℕ)
    (fits : ∀ z q, sw z (sa q).1.1 ≤ d)
    (M : ∀ z j, D.State (fun e => Fin (2^base e)) j → (ports G).State (fun a => Fin (2^sw z a)) j → F)
    (id : H ≃ Fin h) (z : Histogram H r) (C : BitNetwork F ((r*d)+(r*d+r*d))) (Cc : BitNetwork F (r+(r+r)))
    (old : (a : D.Port j) → Fin (w a.1.1) → Fin p)
    (fresh : (a : (ports G).Port j) → Fin (histWidth sw z a.1.1 + r*k) → Fin p)

def directParty : Tree F p := .join 0 1 (fun _ => _) (fun _ => partyPointer D G j base w B sa sw z
    (fun q t => .pin (old q t)) (fun q t => .pin (fresh q t))) (fun _ => party D G j base B sa sw fits M id z C Cc)

omit [Fintype J] [Nonempty J] [Fintype E] in
theorem directParty_eval (pad : ∀ e, w e ≤ base e*r)
    (hC : ∀ M X Y, C.eval (Fin.append M (Fin.append X Y)) = if Y=Routing.StableCompaction.compact M X then 1 else 0)
    (hc : ∀ M X Y, Cc.eval (Fin.append M (Fin.append X Y)) = if Y=Routing.StableCompaction.compact M X then 1 else 0)
    (pin : Fin p → Bool) (x : D.State (fun e => Fin (2^w e)) j)
    (y : (ports G).State (fun a => (Fin r → Fin (2^k)) × Fin (2^histWidth sw z a)) j)
    (hx : ∀ a t, pin (old a t) = (x a).val.testBit t.val)
    (hy : ∀ a t, pin (fresh a t) = (SlotRefinement.selectorWord r k _ (y a)).val.testBit t.val) :
    (directParty D G j w base B sa sw fits M id z C Cc old fresh).compile.eval pin =
      histogramKernel D G w base pad sw B.code M z j x y := by
  rw [directParty,compile,BitNetwork.Ordered.glue_eval,Fintype.sum_unique,Fin.prod_univ_one]
  let N := (party D G j base B sa sw fits M id z C Cc).compile
  calc
    _ = N.eval (partyInputs D G j base B sa sw z w pad x y (d:=d)) := by
      apply congrArg N.eval
      exact partyPointer_read D G j base w B sa sw z (d:=d)
        (fun q t => .pin (old q t)) (fun q t => .pin (fresh q t))
        pad pin _ x y hx hy
    _ = _ := by
      change (party D G j base B sa sw fits M id z C Cc).compile.eval (Fin.append _ _) = _
      rw [party_value]
      exact party_eval D G j base B sa sw fits M id z C Cc w pad hC hc x y

end
end ThreeFlat.Diagonal.HistoryContraction.Tree

end OAI
