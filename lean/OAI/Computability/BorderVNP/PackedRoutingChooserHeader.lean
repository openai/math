import OAI.Computability.BorderVNP.PackedRoutingTraffic

/-! # The sparse chooser decodes its actual frame after the two placement passes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open RoutingISA VPVNP.BurstRAM DiagonalResidueRAM Cube.LabelIndex

/-- The private placement writes after the cable triples, so it preserves the
public frame and the entire triple array at their original addresses. -/
theorem private_before_ends {head origin m C J desc gap i : ℕ} {before after : ℕ → ℕ}
    (run : (privateLayout head origin m C J desc gap).Image before i after) (a : ℕ)
    (lt : a < (bases origin m C J).ends) : after a = before a := by
  apply run.outside
  · intro j _
    dsimp [privateLayout,bases] at *
    omega
  · left
    dsimp [privateLayout,bases,PrivatePlacement.Layout.scratch,PrivatePlacement.Layout.supplied] at *
    omega

/-- Frame 6 is the actual geometry result, 7 the full physical cable count, 8 the
demand base, 9 its populated length, and 11 the true cell count after publication. -/
theorem chooser_header {W head origin m C J desc gap base : ℕ} (before : ℕ → ℕ)
    (after : Memory W) (rows : List Directory.Row) (initial : Header head origin m C J before)
    (f8 : before (head+8) = base) (headGeom : head+11 < origin) (headDemand : head+11 < base)
    (run : (privateLayout head origin m C J desc gap).Image before J (readings after))
    (fit : rows.length < 2^W) :
    let mem := readings (Directory.ISA.publish after head base rows)
    let l := Cube.LabelIndex.layout head mem
    l.cables = origin ∧ l.cableCount = m ∧ l.deliveries = base ∧
      l.deliveryCount = rows.length ∧ l.cells = C := by
  intro mem l
  have kept (i : ℕ) (hi : i ≤ 11) (ne : i ≠ 9) : mem (head+i) = before (head+i) := by
    have d := CableTriples.published_outside after head base rows (head+i) (by omega) (Or.inl (by omega))
    have p := private_before_ends run (head+i) (by dsimp [bases]; omega)
    exact (congrArg Fin.val d).trans p
  have cnt := (Directory.ISA.publish_read after head base rows (by omega)).1
  exact ⟨(kept 6 (by decide) (by decide)).trans initial.cables,
    (kept 7 (by decide) (by decide)).trans initial.edges,
    (kept 8 (by decide) (by decide)).trans f8,(congrArg Fin.val cnt).trans (word_val _ _ fit),
    (kept 11 (by decide) (by decide)).trans initial.cells⟩

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
