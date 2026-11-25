import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepPrice
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalMaskPrice

/-! # Computable row support for the mask, pivot and saved headers -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Sweep

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  InterchangeROMAddress InterchangeAddress

private abbrev Descriptor := InterchangeROMMaskCompile.Params × Header

private def singletonSpec (q : Descriptor) : InterchangeROMAddress.Spec := (q.1.1,[q.1.2])

private abbrev maskK := Physical.Mask.command_bounded.choose
private abbrev maskD := Physical.Mask.command_bounded.choose_spec.choose

private def overhead (q : Descriptor) : ℕ :=
  maskK*((size q+1)^maskD+1) + headerTime (singletonSpec q) q.2 pivotK pivotDegree +
    110*(size (InterchangeROMMaskCompile.desc q).2+3) + 2001*size q.2 + 2010

private theorem polynomial : Dom (@size Descriptor _) overhead := by
  let W := @size Descriptor _
  have top : Dom W W := Dom.base _
  have spec : Dom W (fun q => size (singletonSpec q)) :=
    (top.add (Dom.const W 2)).mono fun q => by
      simp only [W,singletonSpec,size_prod,size_cons,size_nil]; omega
  have h : Dom W (fun q => size q.2) :=
    top.mono fun q => by simp only [W,size_prod]; omega
  have z : Dom W (fun q => size (singletonSpec q,q.2)+1) :=
    ((spec.add h).add (Dom.const W 2)).mono fun q => by simp [size_prod]
  have d : Dom W (fun q => size (InterchangeROMMaskCompile.desc q).2) :=
    InterchangeROMMaskCompile.desc_poly.length.mono fun q => by
      simp only [size_prod]; omega
  have t : Dom W (fun q => headerTime (singletonSpec q) q.2 pivotK pivotDegree) :=
    (((Dom.const W 5).mul spec).add ((Dom.const W pivotK).mul (z.pow pivotDegree))).add (Dom.const W 20)
  exact (((((Dom.const W maskK).mul (((top.add (Dom.const W 1)).pow maskD).add
    (Dom.const W 1))).add t).add ((Dom.const W 110).mul (d.add (Dom.const W 3)))).add
    ((Dom.const W 2001).mul h)).add (Dom.const W 2010)

private abbrev deg := polynomial.choose
private abbrev coeff := polynomial.choose_spec.choose
private abbrev factor := (Physical.Mask.shape_power deg).choose

/-- Coefficient of the row count in all header work for one physical spectral field. -/
def headerPrice (b n : ℕ) : ℕ := maskK + Physical.Mask.linearPrice coeff deg factor b n

theorem computable_headerPrice {X : Type} [Primcodable X] {b n : X → ℕ}
    (hb : Computable b) (hn : Computable n) :
    Computable fun x => headerPrice (b x) (n x) :=
  Primrec.nat_add.to_comp.comp (Computable.const maskK)
    (Physical.Mask.computable_linearPrice coeff deg factor hb hn)

theorem shapeCharge_le {I J : Type} [DecidableEq J] {b n : ℕ} (ord : J ≃ Fin n)
    (P G B : I → Tape) (f l : I → ℕ) (j : J)
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) (u : I)
    (hb : 2 ≤ b) (ok : ∀ k ∈ P u ++ G u ++ B u, 2 ≤ k ∧ k ≤ b) :
    let q := child ord P G B f l j v u
    let h := header (f u) (P u) (G u) (B u)
    let N := countRows (b:=b) ord P G B f u
    shapeCharge b n (ord j) h q.header N ≤ headerPrice b n*N := by
  intro q h N
  let z : Descriptor := (Physical.Mask.parameter b n (ord j).val,h)
  have hc : q.header = send (InterchangeROMMaskCompile.desc z).2 := by
    rw [show InterchangeROMMaskCompile.desc z = _ from
      InterchangeROMMaskCompile.desc_numeric ord (P u) (G u) (B u) b (f u) j j]
    rfl
  have hp : (size z+1)^deg ≤ ((4*b+8*n+24)^deg*factor)*N :=
    (Physical.Mask.shape_power deg).choose_spec ord j (P u) (G u) (B u) hb ok (f u)
  have htotal := (polynomial.choose_spec.choose_spec z).trans (Nat.mul_le_mul_left coeff hp)
  have hexp : shapeCharge b n (ord j) h q.header N = maskK*N + overhead z := by
    rw [hc]
    change maskK*(N+((size z+1)^maskD)+1) + headerTime (singletonSpec z) h pivotK pivotDegree +
      110*(size (InterchangeROMMaskCompile.desc z).2+3) + 2001*size h + 2010 =
        maskK*N + overhead z
    simp only [overhead,show z.2 = h from rfl,Nat.mul_add]
    omega
  rw [hexp,headerPrice,Nat.add_mul]
  refine Nat.add_le_add_left (htotal.trans ?_) _
  simp only [Physical.Mask.linearPrice,Nat.mul_assoc,Nat.add_mul]
  exact Nat.mul_le_mul_left _ (by omega)

end InterchangeROMRepair.Sweep

end

end NearSquareRoot
end Computability
end OAI
