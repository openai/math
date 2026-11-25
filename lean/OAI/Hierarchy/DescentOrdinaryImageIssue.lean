import OAI.Hierarchy.DescentPackedMatchChooserInput
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # Install both literal ordinary-stage tables on the old numeric roster -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Chooser
open DescentSixParty DescentCompiler DescentColonies DescentAffineColors DescentPackedColony DescentSIMDLookup ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k age L G ℓ w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (groups : J≃Fin G) (hosts : V≃Fin L) (hv : L≤2^ℓ)
variable (C : Layout) (b quota payload unit ratio : ℕ)
local notation "H" => 2^ℓ
local notation "M" => lanes payload unit
local notation "fee" => A.wire*(A.z*gadget.b)
local notation "gap" => DescentHostDegree.gap A.degree
local notation "exp" => DescentHostDegree.packExponent 20 A.degree
local notation "cap" => 2^exp*(fee*A.cap)
local notation "roster" => DynamicSplit.Roster ℓ A.degree


local notation "CI" => Phase.CensusTables.image (w:=w) C.origin ((1+b+2*quota)*2^k) (b*2^k) M H G
  (fun fl=>PackedCensus.lookup fl b quota k A.wire 256 (A.z*gadget.b) A.hist)
local notation "PI" => Phase.Arena.image (w:=w) C.chart A.fieldBits A.degree H G b
  (2*Phase.unit k b*M) gap cap

theorem Geometry.install (rs : roster) (m : Memory w)
    (calendar : Geometry (G:=G) (w:=w) A hosts hv C b quota payload unit ratio rs)
    (forward : (CI).stop≤(PI).low ∨ (PI).stop≤(CI).low)
    (left : (CI).low+(CI).length<2^w) (right : (PI).low+(PI).length<2^w)
    (beforeC : C.chart.roster.base+H*A.degree≤(CI).low)
    (beforeP : C.chart.roster.base+H*A.degree≤(PI).low)
    (stored : ∀v i,m (C.chart.roster.base+(v.val*A.degree+i.val))=(target (rs v i):Word w)) :
    ((CI).program.seq (PI).program).Exec m ((PI).output ((CI).output m)) (8+10*((CI).length+(PI).length)) ∧
    Setup (G:=G) A hosts hv C b quota payload unit ratio rs ((PI).output ((CI).output m)) ∧
    (∀z,(z<(CI).low ∨ (CI).stop≤z)→(z<(PI).low ∨ (PI).stop≤z)→(PI).output ((CI).output m) z=m z) ∧
    CheapCode ((CI).program.seq (PI).program) ∧
    DescentStaticWordColumn.names ((CI).program.seq (PI).program)=15*((CI).length+(PI).length+2) := by
  obtain ⟨run,first,second,frame,cheap,code⟩:=(CI).pair PI m forward left right
  refine ⟨run,{toGeometry:=calendar,censusROM:=first,phaseROM:=second,stored:=?_},frame,cheap,code⟩
  intro v i
  have bound : v.val*A.degree+i.val<H*A.degree := by
    calc
      _ < v.val*A.degree+A.degree := Nat.add_lt_add_left i.isLt _
      _ = (v.val+1)*A.degree := (Nat.succ_mul _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ v.isLt
  have low := Nat.add_lt_add_left bound C.chart.roster.base
  exact (frame _ (.inl (low.trans_le beforeC)) (.inl (low.trans_le beforeP))).trans (stored v i)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Chooser

end OAI
