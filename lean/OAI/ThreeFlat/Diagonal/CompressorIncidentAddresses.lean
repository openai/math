import OAI.ThreeFlat.Diagonal.CompressorIncidentGeometry
import OAI.ThreeFlat.Diagonal.CompressorDenseMotifs

namespace OAI
/-! # Decoding the chronological site and local six-word record address -/

noncomputable section

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Fin.NatCast
variable {w t l N : ℕ} {B : Type}

def siteNumber (b : B ≃ Fin N) (s : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l)) :=
  2^l*(2^t*(b s.1).val+(tagOrdinal t s.2.1).val)+(tagOrdinal l s.2.2).val

private theorem high {r i : ℕ} (a : ℕ) (h : i<r) : (r*a+i)/r=a := by
  rw [Nat.mul_add_div (by omega : 0<r),Nat.div_eq_of_lt h,Nat.add_zero]

private theorem low {r i : ℕ} (a : ℕ) (h : i<r) : (r*a+i)%r=i := by
  rw [Nat.mul_add_mod,Nat.mod_eq_of_lt h]

variable (data : Param → Word w) (mem : Memory w) (vs : Fin 1 → Word w)
local notation "V" => Formula.value data mem vs

theorem div_value (x y : F) : (V (.op .div x y)).val=(V x).val/(V y).val := by
  change _ % 2^w = _
  exact Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt (V x).isLt)

theorem mod_value (x y : F) : (V (.op .mod x y)).val=(V x).val%(V y).val := by
  change _ % 2^w = _
  exact Nat.mod_eq_of_lt ((Nat.mod_le _ _).trans_lt (V x).isLt)

private theorem lit_value (k : ℕ) (fit : k<2^w) : (V (Formula.lit k)).val=k :=
  Fin.val_cast_of_lt fit

theorem siteAt_code {S : Graph.Stage} (E : Codec B w S.colors t l) (b : B ≃ Fin N) (ptr site : F)
    (s : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))
    (base : ∀ a,E.base a=((b a).val:Word w))
    (tagsR : (V (atField (Demand.formulaOps 1) ptr tags)).val=2^t)
    (laneR : (V (atField (Demand.formulaOps 1) ptr remaining)).val=2^l)
    (siteR : (V site).val=siteNumber b s) :
    (siteAt ptr site).map V=siteCode E s := by
  let f := atField (Demand.formulaOps 1) ptr
  let q := Formula.op .div site (f remaining)
  have qv : (V q).val=2^t*(b s.1).val+(tagOrdinal t s.2.1).val := by
    change (V (.op .div site (atField (Demand.formulaOps 1) ptr remaining))).val=_
    rw [div_value,laneR,siteR,siteNumber,high _ (tagOrdinal l s.2.2).isLt]
  have bn : (b s.1).val<2^w := by
    have : (b s.1).val≤2^t*(b s.1).val := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    have room := (V q).isLt
    omega
  have bv : V (.op .div q (f tags))=E.base s.1 := by
    apply Fin.ext
    rw [div_value,qv,tagsR,high _ (tagOrdinal t s.2.1).isLt,base,Fin.val_cast_of_lt bn]
  have tv : V (.op .mod q (f tags))=tagWord E.tags s.2.1 := by
    apply Fin.ext
    rw [mod_value,qv,tagsR,low _ (tagOrdinal t s.2.1).isLt]
    rfl
  have lv : V (.op .mod site (f remaining))=tagWord E.lanes s.2.2 := by
    apply Fin.ext
    rw [mod_value,siteR,laneR,siteNumber,low _ (tagOrdinal l s.2.2).isLt]
    rfl
  change Placement.Site.mk (V (.op .div q (f tags))) (V (.op .mod q (f tags))) (V (.op .mod site (f remaining)))=_
  rw [bv,tv,lv]
  rfl

abbrev rowSite (S : Graph.Stage) (linear : F) : F := .op .div (.op .div linear (.lit 6)) (.lit (capacity S))
abbrev rowRank (S : Graph.Stage) (linear : F) : F := .op .mod (.op .div linear (.lit 6)) (.lit (capacity S))
abbrev rowField (linear : F) : F := .op .mod linear (.lit 6)

theorem split_record (S : Graph.Stage) (linear : F) (site index : ℕ) (field : Fin 6)
    (room : 6<2^w) (bound : capacity S<2^w) (hi : index<capacity S)
    (addr : (V linear).val=6*(capacity S*site+index)+field.val) :
    (V (rowSite S linear)).val=site ∧ (V (rowRank S linear)).val=index ∧ (V (rowField linear)).val=field.val := by
  have outer : (V (.op .div linear (.lit 6))).val=capacity S*site+index := by
    rw [div_value,lit_value _ _ _ 6 room,addr,high _ field.isLt]
  refine ⟨?_,?_,?_⟩
  · rw [rowSite,div_value,outer,lit_value _ _ _ _ bound,high _ hi]
  · rw [rowRank,mod_value,outer,lit_value _ _ _ _ bound,low _ hi]
  · rw [rowField,mod_value,lit_value _ _ _ 6 room,addr,low _ field.isLt]


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents

end

end OAI
