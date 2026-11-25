import OAI.Hierarchy.DescentResetStemTemplateScene

namespace OAI
/-! # The signed calendar ticket selects the template of the actual reset -/

namespace Hierarchy.DescentSixParty.ClosedReset.Window

open DescentCompiler DescentDenseHostOrder DescentResetLocalRoster DescentResetStemDecoder
open scoped Classical
noncomputable section

private abbrev signedRows (r n : ℕ) := 2*DescentFallbackShapeTable.rows r (2^n)

private def signedTemplate {n h : ℕ} (board : NonlinearExpanders.Graph n h) (r depth : ℕ)
    (j : Fin (2*signedRows r n)) : Option (Fin (DescentDenseHostOrder.roster board r depth).card × Fin (DescentDenseHostOrder.roster board r depth).card) :=
  let u : Fin 2 × Fin (signedRows r n) := finProdFinEquiv.symm j
  localTemplate board r depth (finTwoEquiv u.1) u.2.val

private theorem calendar_congr {n n' h r r' : ℕ}
    (a : NonlinearExpanders.Graph n h) (b : NonlinearExpanders.Graph n' h)
    (dim : n=n') (graph : HEq a b) (roots : r=r') (depth : ℕ) :
    (DescentDenseHostOrder.roster a r depth).card=(DescentDenseHostOrder.roster b r' depth).card ∧
      HEq (signedTemplate a r depth) (signedTemplate b r' depth) := by
  subst n'
  subst r'
  obtain rfl := eq_of_heq graph
  exact ⟨rfl,HEq.rfl⟩

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

private theorem calendar_width : k=B.reset.k-B.terminals.commonDepth := by
  rw [B.keyWidth,B.commonDepth]
  omega

theorem calendar_palette :
    (DescentDenseHostOrder.roster ctl.board k (GroupStage.depthBound D n f g)).card =
      (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth) (GroupStage.depthBound D n f g)).card :=
  (calendar_congr ctl.board B.reset.graph B.dimension.symm B.graph.symm (calendar_width B) _).1

theorem calendar_heads :
    2*DescentFallbackShapeTable.rows k (2^n) =
      2*DescentFallbackShapeTable.rows (B.reset.k-B.terminals.commonDepth) (2^B.reset.n) := by
  rw [← calendar_width B,B.dimension]

theorem calendar_stemTemplates :
    HEq (fun j : Fin (2*(2*DescentFallbackShapeTable.rows k (2^n))) =>
      let u : Fin 2 × Fin (2*DescentFallbackShapeTable.rows k (2^n)) := finProdFinEquiv.symm j
      localTemplate ctl.board k (GroupStage.depthBound D n f g) (finTwoEquiv u.1) u.2.val)
      (stemTemplates B) :=
  (calendar_congr ctl.board B.reset.graph B.dimension.symm B.graph.symm (calendar_width B) _).2

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
