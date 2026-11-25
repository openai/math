import OAI.Computability.NearSquareRoot.InterchangeROMOuterRulersNative
import OAI.Computability.NearSquareRoot.InterchangeROMFamilyGeometry

/-! # The two generated bank adapters of the selected template -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom
  CommonRegisters GeneratorSyntax Interchange InterchangeAddress InterchangeAddress.Request
  InterchangeROMExpose InterchangeROMRepair InterchangeROMRecursion InterchangeSpectralFibre

private abbrev rows (x : Template.Data) := x.labels*Raw.rowCount x.m
private abbrev slots (x : Template.Data) := positions x.a x.m

noncomputable def templateEnter (x : Template.Data) := entry (rows x) x.b (slots x)
noncomputable def templateLeave (x : Template.Data) := leave (rows x) x.b (slots x)

private theorem sizes : Computable rows ∧ Computable slots := by
  have m := (Template.Data.primrec_header 2).to_comp
  have a := (Template.Data.primrec_header 3).to_comp
  exact ⟨Primrec.nat_mul.to_comp.comp (Template.Data.primrec_header 4).to_comp
    (Raw.primrec_rowCount.to_comp.comp m), Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp a m) a⟩

theorem effective_templateEnter : Effective ltr templateEnter :=
  effective_entry sizes.1 (Template.Data.primrec_header 1).to_comp sizes.2

theorem effective_templateLeave : Effective ltr templateLeave :=
  effective_leave sizes.1 (Template.Data.primrec_header 1).to_comp sizes.2

theorem template_registers : ∃ R, ∀ x, Within R (templateEnter x) ∧ Within R (templateLeave x) := by
  obtain ⟨R,h⟩ := wire_registers
  exact ⟨R,fun x => h _ _ _⟩

/-- Both endpoint commands share an absolute polynomial degree. Their common
coefficient is computed from the template before the request is read. -/
theorem template_wires : ∃ (k : ℕ) (charge : Template.Data → ℕ), Computable charge ∧
    ∀ {j t : ℕ} (x : Template.Data) (h : Template.Data.Valid j t x) (q : Request x.b)
      (ok : Packed (@value (x.modulusIndex+1)) q) (hw : positions x.a x.m < q.width) (parent : Cmd),
    let i := InterchangeROMStars.frame x.a x.m q h.1.2.2.1.two_le (by have := h.1.2.2.2.2.2.1; omega) hw ok.1
    let W := x.labels*Raw.rowCount x.m
    let tag := send (centerHeader i)
    let head := send (groupedHeader i W)
    let op : key i W → key i W := swapMain (OuterReserves.main x.a x.m)
    At parent (templateEnter x) (job x.b) [] [] (.fork tag (centerPayload i)) (.fork tag (.fork head (stream i W id)))
      (charge x*(localMass q k+1)) 0 0 ∧
    At parent (templateLeave x) (job x.b) [] [] (.fork tag (.fork head (stream i W op)))
      (.fork tag (InterchangeROMStars.afterMain x.a x.m q i.radix i.slots hw ok.1)) (charge x*(localMass q k+1)) 0 0 := by
  obtain ⟨k,C,K,run⟩ := native_wires
  let cell (x : Template.Data) := 2*(x.modulusIndex+1)+3
  let data (x : Template.Data) := bufferCost (rows x) (cell x)
  let charge (x : Template.Data) := wireCost K C k (rows x) x.b (slots x) (data x)
  have digit : Computable cell := by
    have p := (Template.Data.primrec_header 0).to_comp
    have modIndex := Primrec.nat_sub.to_comp.comp p (Computable.const 1)
    exact Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (.const 2) (Primrec.succ.to_comp.comp modIndex)) (.const 3)
  have count : Computable data := Primrec.nat_mul.to_comp.comp (Primrec.nat_add.to_comp.comp sizes.1 (.const 2))
    (Primrec.nat_add.to_comp.comp digit (.const 3))
  refine ⟨k,charge,computable_wireCost K C k sizes.1 (Template.Data.primrec_header 1).to_comp sizes.2 count,?_⟩
  intro j t x h q ok hw parent i W tag head op
  exact run q i.radix i.slots hw ok.1 W (cell x) (InterchangeROMFamily.legal_width h).1
    (InterchangeROMFamily.legal_width h).2 (fun k => record_size (ok.2.2 k)) parent

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
