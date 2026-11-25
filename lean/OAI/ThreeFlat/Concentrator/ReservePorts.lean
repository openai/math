import OAI.ThreeFlat.Concentrator.EdgeMixing

namespace OAI
/-! # Candidate incidences in the reserve graph -/

namespace ThreeFlat.Concentrator

open BinPackingGames.Foundations.PCP.PoweringWalks

/-- Embed the candidate requests into directed port positions in row-major order. -/
def reservePortEmbedding {n m d : ℕ} (size : n ≤ m * d) : Fin n ↪ Fin m × Fin d :=
  (Fin.castLEEmb size).trans finProdFinEquiv.symm.toEmbedding

private theorem source_card_le {V D E : Type*} [Fintype D] [DecidableEq V]
    (port : E ↪ V × D) (S : Finset E) (v : V) :
    (S.filter (fun x => (port x).1 = v)).card ≤ Fintype.card D := by
  classical
  let sources := S.filter fun x => (port x).1 = v
  let index (x : sources) := (port x.val).2
  have hindex : Function.Injective index := by
    intro x y heq
    apply Subtype.ext
    apply port.injective
    exact Prod.ext ((Finset.mem_filter.mp x.property).2.trans
      (Finset.mem_filter.mp y.property).2.symm) heq
  simpa [sources] using Fintype.card_le_of_injective index hindex

/-- A vertex has at most `d` possible outgoing and `d` possible incoming
requests. The incidence finset counts a loop once. -/
theorem incident_card_le_two_mul_degree {V D E : Type*} [Fintype D] [DecidableEq V]
    (G : PortGraph V D) (port : E ↪ V × D) (S : Finset E) (v : V) :
    ((portReserveGraph G port).incident S v).card ≤ 2 * Fintype.card D := by
  classical
  unfold ReserveGraph.incident portReserveGraph
  simp only [Finset.filter_or]
  have outgoing := source_card_le port S v
  have incoming := source_card_le (port.trans G.rot.toEmbedding) S v
  apply (Finset.card_union_le _ _).trans
  simpa only [two_mul, Function.Embedding.trans_apply, Equiv.toEmbedding_apply] using
    add_le_add outgoing incoming

end ThreeFlat.Concentrator

end OAI
