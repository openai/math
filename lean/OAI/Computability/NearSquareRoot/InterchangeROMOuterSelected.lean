import OAI.Computability.NearSquareRoot.InterchangeROMOuterMass
import OAI.Computability.NearSquareRoot.InterchangeROMFamilyGeometry
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalNative

/-! # The packed cubic phase on the actual grouped parent rows -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
  NearSquareRoot.Interchange NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeAddress.Request
  NearSquareRoot.InterchangeROMRecursion NearSquareRoot.InterchangeROMExpose NearSquareRoot.InterchangeSpectralFibre
  NearSquareRoot.InterchangeROMRepair NearSquareRoot.InterchangeROMRepair.Physical NearSquareRoot.InterchangeROMFamily

/-- The selected cubic program supplies the middle component on every legal
template. Its whole emitted recursive ledger lies in the smaller bank. The
header exponent is absolute and its coefficient is computed from the template. -/
theorem selected_main : ∃ e : ℕ, ∃ K : Template.Data → ℕ, Computable K ∧
    ∀ {j t : ℕ} (x : Template.Data) (h : Template.Data.Valid j t x) (q : Request x.b)
      (ok : Packed (@value (x.modulusIndex+1)) q) (hw : positions x.a x.m < q.width),
      let i := InterchangeROMStars.frame x.a x.m q h.1.2.2.1.two_le
        (by have := h.1.2.2.2.2.2.1; omega) hw ok.1
      let W := x.labels*Raw.rowCount x.m
      let op : key i W → key i W := swapMain (OuterReserves.main x.a x.m)
      ∀ v : tensor i x.modulusIndex x.labels (Raw.rowCount x.m),
        ∃ sm : List (Request x.b), sm.length ≤ x.calls ∧
          (∀ y∈sm, Packed (@value (x.modulusIndex+1)) y ∧ y.width=f i ∧ y.recordWidth=q.recordWidth ∧
            y.rows.count=(groupedRows i W).count) ∧
          ∀ parent, At parent (Selected.program x) (job x.b) sm [] (cubic i v) (cubic i (permute v op))
            (K x*(localMass q e+1)) 0 0 := by
  obtain ⟨e,he,K,comp,run⟩ := Selected.program_packed
  let rate (x : Template.Data) := K x*groupedRate x.b (x.a+x.m+x.a) e
  have a : Computable (fun x : Template.Data => x.a) := (Template.Data.primrec_header 3).to_comp
  have m : Computable (fun x : Template.Data => x.m) := (Template.Data.primrec_header 2).to_comp
  refine ⟨e,rate,computable_cubic_rate comp (Template.Data.primrec_header 1).to_comp
    (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp a m) a) (.const e),?_⟩
  intro j t x h q ok hw i W op v
  have hb := h.1.2.2.1.two_le
  let : NeZero x.b := ⟨by omega⟩
  let : Fact (x.modulusIndex+1).Prime := ⟨modulus h ▸ h.1.1⟩
  have wide := legal_width h
  have less : W < x.b := (bank_width x).trans_lt h.1.2.2.2.2.1
  have dims := packed_dimensions hb W (by have := wide.1; dsimp only [W]; omega) less q i.n ok.1
  obtain ⟨sm,len,safe,exec⟩ := run h dims (lanes_pos i.slots i.inside) v
  exact ⟨sm,len,safe,fun parent => (exec parent).mono (cubic_clock_le i W wide.1 wide.2 e he (K x)) le_rfl le_rfl⟩

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
