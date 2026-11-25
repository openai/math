import OAI.ThreeFlat.RAM.TickTerminalRootPrice

namespace OAI
/-! # Hardware counts of the original four compiled terms in the selected-root loop -/

noncomputable section
namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure HistoryTerminalTape
open scoped Fin.CommRing BigOperators

open private addressTemplate seed_uniform generator_uniform from OAI.ThreeFlat.RAM.TickTerminalRootPrice

private structure TermSizes where
  seed : ℕ
  commands : ℕ
  arguments : ℕ
  expression : ℕ

private def sizes (W : ℕ) (A : Arena) : TermSizes :=
  ⟨(HeaderScan.closed (w:=W) (boot A)).binds,(generator W A true).binds,
    (generator W A false).binds,(TickTerminalPrimitive.expression W).binds⟩

private theorem sizes_congr {s c a e s' c' a' e' : ℕ} (hs : s=s') (hc : c=c') (ha : a=a') (he : e=e') :
    TermSizes.mk s c a e=TermSizes.mk s' c' a' e' := by subst_vars; rfl

private theorem sizes_at (W : ℕ) (A : Arena) : sizes W A=sizes 1 addressTemplate :=
  sizes_congr (seed_uniform W A) (generator_uniform W A true) (generator_uniform W A false) (expression_uniform W)

private def dimensions {W : ℕ} (body : Procedure W) : ℕ × ℕ × ℕ :=
  (body.labels,body.registers,body.slots)

private def dimensionsFromTerms (sl sr cl cr al ar el er : ℕ) : ℕ × ℕ × ℕ :=
  (7+(((((6+sl)+(13+cl))+(13+al))+(18+(el+6)))+10),
    3+(((((4+sr)+(4+cr))+(4+ar))+(4+er))+5),4)

private def shapeOfSizes (p : TermSizes) : ℕ × ℕ × ℕ :=
  dimensionsFromTerms (3*p.seed+1) p.seed (3*p.commands+1) p.commands
    (3*p.arguments+1) p.arguments (3*p.expression+1) p.expression

private theorem dimension_values (W : ℕ) (A : Arena) :
    let seed := HeaderScan.closed (w:=W) (boot A)
    let cmd := generator W A true
    let arg := generator W A false
    let body := TickTerminalPrimitive.expression W
    dimensions (many W A) = dimensionsFromTerms seed.labels seed.binds cmd.labels cmd.binds
      arg.labels arg.binds body.labels body.binds := rfl

private theorem shape_of_terms {W : ℕ} (s c a : Term W 0 1) (e : Term W 1 1) :
    dimensionsFromTerms s.labels s.binds c.labels c.binds a.labels a.binds e.labels e.binds =
      shapeOfSizes ⟨s.binds,c.binds,a.binds,e.binds⟩ := by
  simp only [shapeOfSizes,Term.labels_eq]

attribute [local irreducible] dimensionsFromTerms shapeOfSizes

private theorem native_dimensions (W : ℕ) (A : Arena) : dimensions (many W A) = shapeOfSizes (sizes W A) :=
  (dimension_values W A).trans (shape_of_terms (HeaderScan.closed (w:=W) (boot A)) (generator W A true)
    (generator W A false) (TickTerminalPrimitive.expression W))


end ThreeFlat.RAM.TickTerminalRoot

end
end OAI
