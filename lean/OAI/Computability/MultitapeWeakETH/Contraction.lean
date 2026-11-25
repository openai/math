import OAI.Computability.MultitapeWeakETH.FieldTables
import OAI.Computability.VPVNP.WireTensor

/-! # Grouping network vertices at tensor parties -/

namespace OAI.Computability.MultitapeWeakETH.Network

open VPVNP.WireTensor

variable {n b : ℕ} (G : Network n b) {K J : Type} [Field K] [Fintype J]

abbrev External (v : Fin G.vertices) :=
  (G.localBits G.input v → Bool) × (G.localBits G.output v → Bool)

noncomputable instance (v : Fin G.vertices) : Fintype (G.External v) := by
  classical unfold External localBits; infer_instance

noncomputable def externalCoeff (table : (v : Fin G.vertices) → G.View v → K)
    (ext : ∀ v, G.External v) : K :=
  ∑ labels : G.Labels, ∏ v, table v (fun e => labels e.1,ext v)

theorem externalCoeff_words (table : (v : Fin G.vertices) → G.View v → K) (x z : Word n) :
    G.externalCoeff table (fun _ => (fun i => x i.1,fun i => z i.1)) = G.contract table x z := rfl

open scoped Classical in
/-- Supply wires and all factors at the same site are grouped before applying
the local maps. A loop has two ports carrying the same global edge label. -/
theorem placed_restriction (place : Fin G.vertices → J)
    (table : (v : Fin G.vertices) → G.View v → K) :
    Restricts (wireNetwork (k := K) (place ∘ G.src) (place ∘ G.dst) (fun e => Word (G.width e)))
      (placedTensor place G.External (G.externalCoeff table)) := by
  classical
  let a := place ∘ G.src
  let c := place ∘ G.dst
  let supply := wireNetwork (k := K) a c (fun e => Word (G.width e))
  let localEntry (v : Fin G.vertices) (ext : G.External v) (wire : supply.Basis (place v)) :=
    table v (fun e => if h : G.src e.1 = v then wire.1 e.1 (congrArg place h.symm)
      else wire.2 e.1 (congrArg place (e.2.resolve_left h).symm),ext)
  let map (j : J) (ext : (v : Fin G.vertices) → j = place v → G.External v) (wire : supply.Basis j) :=
    ∏ v, if h : j = place v then localEntry v (ext v h) (h ▸ wire) else 1
  refine ⟨map,?_⟩
  funext ext
  erw [applyLocal_wireNetwork a c (fun e => Word (G.width e)) (C := fun j =>
    (v : Fin G.vertices) → j = place v → G.External v) map ext]
  dsimp only [placedTensor,externalCoeff]
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro labels _
  dsimp only [map]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro v _
  rw [Finset.prod_eq_single (place v)]
  · simp only
    change table v (_,_) = table v (_,_)
    congr 2
    funext e
    split <;> rfl
  · intro j _ ne
    simp [ne]
  · simp

end OAI.Computability.MultitapeWeakETH.Network
