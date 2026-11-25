import OAI.ThreeFlat.Diagonal.HistoryPartyTrees

namespace OAI
/-! # Ordered postorder traversal of occupied motifs and active sites -/

namespace ThreeFlat.Diagonal.HistoryContraction.Tree

noncomputable section
open HistogramTileNetwork MotifKernel MotifOuterTerms LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector
open scoped Classical BigOperators

variable {J E S H Z F : Type} [Field F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] [Fintype Z] [DecidableEq Z] {k d r s p c a : ℕ}
  (D : PortGraph J E) (G : Supply J S) (place : J → Z) (v : Z) (w base : E → ℕ) (sw : H → S → ℕ)
  (code : H ↪ Fin (2^k)) (id : H ≃ Fin s) (z : Histogram H r) (edges : Fin a ≃ Absorbed (ports G) place v)
  (parts : Fin c ≃ {j // place j=v}) {e n : Fin c → ℕ} (supply : ∀ i, Fin (e i) ≃ (ports G).Port (parts i).val)
  (demand : ∀ i, Fin (n i) ≃ D.Port (parts i).val) (fits : ∀ i q u, sw q (supply i u).1.1 ≤ d)
  (M : ∀ z j, D.State (fun e => Fin (2^base e)) j → (ports G).State (fun a => Fin (2^sw z a)) j → F)
  (C : BitNetwork F ((r*d)+(r*d+r*d))) (count : BitNetwork F (r+(r+r)))
  (old : ∀ i, (q : D.Port (parts i).val) → Fin (w q.1.1) → BitSource (order G place v sw z edges (k:=k)).bits p)
  (cross : (x : ExternalAt (ports G) place v) → Fin (histWidth sw z x.val.val+r*k) → Fin p)

def occupiedTree : Tree F p :=
  .join (order G place v sw z edges (k:=k)).bits c _ (localWire D G place v w base sw code z edges parts supply demand old cross)
    (fun i => party D G (parts i).val base (hd D base code parts demand i) (supply i) sw (fits i) M id z C count)

omit [Fintype Z] [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] in
theorem occupiedTree_eval (pin : Fin p → Bool) :
    (occupiedTree D G place v w base sw code id z edges parts supply demand fits M C count old cross).compile.eval pin =
      (occupied D G place v w base sw code id z edges parts supply demand fits M C count old cross).eval pin := by
  rw [occupiedTree,compile,occupied,BitNetwork.Ordered.glue_eval,BitNetwork.Ordered.glue_eval]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  let B := hd D base code parts demand i
  let f (t : Fin (r*(e i*k) + (r*B.arity+e i*(r*d)))) :=
    (localWire D G place v w base sw code z edges parts supply demand old cross (d:=d) i t).read g pin
  have split : Fin.append (fun j => f (j.castAdd _)) (fun j => f (Fin.natAdd (r*(e i*k)) j)) = f := by
    funext j
    exact Fin.addCases (fun j => Fin.append_left ..) (fun j => Fin.append_right ..) j
  simpa only [split] using party_value D G (parts i).val base B (supply i) sw (fits i) M id z C count
    (fun j => f (j.castAdd _)) (fun j => f (Fin.natAdd _ j))

section Active
variable {M' J' E' V' : Type} [Fintype M'] [Fintype J'] [Fintype E'] [Fintype V'] [DecidableEq V'] {s' : ℕ}
    (P : M' → PortGraph J' E') (site : M' → J' → V') {I : M' → E' → Type} [∀ m e, Fintype (I m e)]
    (v : V') (order : Fin s' ≃ Active site v) (child : ∀ _m : Active site v, Tree F p)

def activeTree : Tree F p := .join 0 s' (fun _ => p) (fun _ j => .pin j) (fun i => child (order i))

omit [Fintype V'] in
theorem activeTree_eval (K : ∀ m j, (P m).State (I m) j → F)
    (shared : ∀ m, WiresAt (P m).tail (P m).head (site m) (I:=I m) none) (pin : Fin p → Bool)
    (actual : ∀ m : Active site v, (child m).compile.eval pin = groupedFactor (P m) (site m) (K m) v (shared m)) :
    (activeTree site v order child).compile.eval pin = ∏ m, groupedFactor (P m) (site m) (K m) v (shared m) := by
  rw [activeTree,compile,BitNetwork.Ordered.glue_eval,Fintype.sum_unique,product_active]
  simp only [BitSource.read,actual]
  exact order.prod_comp (fun m : Active site v => groupedFactor (P m.val) (site m.val) (K m.val) v (shared m.val))

end Active
end
end ThreeFlat.Diagonal.HistoryContraction.Tree

end OAI
