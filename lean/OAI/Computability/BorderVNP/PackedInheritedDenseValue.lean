import OAI.Computability.BorderVNP.PackedInheritedDenseOrder

/-! # The same private program models a densely saved site

The dense input vector and the original vector agree at every physical
ordinal. Consequently the stored site program, including its private
choices and weights, realizes the reindexed table on all input words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening DirectoryCircuit

variable {D M np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (rows : N.Edge ↪ Fin M) (portID : P ↪ Fin np) (v : N.Site)

private noncomputable abbrev dense := Names.denseLayout N rows
private noncomputable abbrev savedID := CutCircuit.denseRows N rows

/-- Each stored wire lane keeps its numerical ordinal in the full local input. -/
theorem dense_wireOrdinal (z : Incident N v) (k : Fin (N.width z.val)) :
    sourceOrder (dense N rows) (savedID N rows) portID v
      (.inl ⟨denseIncident N rows v z, Fin.cast (dense_width N rows z.val).symm k⟩) =
    Fin.cast (dense_incoming N rows v).symm (sourceOrder N rows portID v (.inl ⟨z,k⟩)) := by
  apply Fin.ext
  rw [Fin.val_cast,wireOrdinal,wireOrdinal,dense_wireStart]
  rfl

/-- Every lane of an exterior argument keeps its original full-input ordinal. -/
theorem dense_portOrdinal (u : Attached N v) (k : Fin (bits u.val)) :
    sourceOrder (dense N rows) (savedID N rows) portID v (.inr ⟨u,k⟩) =
      Fin.cast (dense_incoming N rows v).symm (sourceOrder N rows portID v (.inr ⟨u,k⟩)) := by
  apply Fin.ext
  rw [Fin.val_cast,portOrdinal,portOrdinal,dense_portStart]

/-- Reading a vector packed from the saved layout gives the old site's live words at every address. -/
theorem dense_inputWords
    (z : ∀ c : Incident (dense N rows) v, Fin ((dense N rows).width c.val) → Bool)
    (x : ∀ u : Attached N v, Fin (bits u.val) → Bool) (k : Fin (incoming N v)) :
    inputWords (dense N rows) (savedID N rows) portID v z x (Fin.cast (dense_incoming N rows v).symm k) =
      inputWords N rows portID v
        (liveWords N (Names.denseRank N rows).toEmbedding (fun i => N.src ((Names.denseRank N rows).symm i)) v z) x k := by
  obtain ⟨t,rfl⟩ := (sourceOrder N rows portID v).surjective k
  rcases t with ⟨c,k⟩ | ⟨u,k⟩
  · rw [←dense_wireOrdinal,inputWords_wire,inputWords_wire]
    rfl
  · rw [←dense_portOrdinal,inputWords_port,inputWords_port]

/-- Dense save reuses the old site's stored private program without modifying its records. -/
theorem Site.Models.densePack {R : Type*} [AddCommMonoid R] (p : Pack D P bits R)
    (rows : p.layout.Edge ↪ Fin M) (portID : P ↪ Fin np) (v : p.layout.Site)
    (s : Site) (hsize : s.incoming = Inherited.incoming p.layout v) (weight : List (Bool × Option ℕ) → R)
    (models : s.Models p.layout rows portID v hsize weight p.table) :
    let saved := DirectoryCircuit.densePack p rows
    s.Models saved.layout (CutCircuit.denseRows p.layout rows) portID v
      (hsize.trans (dense_incoming p.layout rows v).symm) weight saved.table := by
  dsimp only
  intro z x
  have hbits (k : Fin s.incoming) := dense_inputWords p.layout rows portID v z x (Fin.cast hsize k)
  exact (congrArg (s.value weight) (funext hbits)).trans (models _ _)

end Packing.Inherited

end BorderVNP
end Computability
end OAI
