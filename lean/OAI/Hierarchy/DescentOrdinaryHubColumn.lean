import OAI.Hierarchy.DescentPublishedHubBits

namespace OAI
/-! # Native host-flag update on a fixed padded rectangle of successive dates -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentHostDirectory DescentHostDegree DescentCompiler DescentHubBits DescentIssuedTerminalId
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {G : PoweredGadget F} {S : AtomSchedule}
  {q ε : ℝ} {W : MarkedWorld F d P bits} {i z degree wire hist z' degree' : ℕ} {u : ℝ}
  {src : Reached W G q ε S k i z degree wire hist} {he : 0≤ε} {T : StageInput W G u ε}
  {p : (T.result he).Choice} {n : Normalize ((T.result he).state p)}
  {tgt : Reached n.result G q ε S k (i+1) z' degree' wire hist}
  (link : OrdinaryLink src he T p n tgt)
local notation "slots" => 2^packExponent 20 src.placement.degree+2
local notation "gain" => gainExponent 20 src.placement.degree
local notation "fields" => ordinaryHubRow k slots gain

/-- A slot beyond the input rectangle can occur when the next common resource bound
uses slack. Its zero branch performs no source lookup. -/
def paddedHubExpr (h : ℕ) (owners prev mask : Bank) : Expr :=
  .branch .lt (.lookup owners .row) (.lit h) (ordinary owners prev mask) (.lit 0)

theorem priorBit {h w : ℕ} (fit : Fintype.card src.V≤h) (prev : Bank) (mem : Memory w)
    (stored : ∀i : Fin h,mem (prev.base+i.val)=((Census.hub src.placement
      (src.vertex.trans (Fin.castLEEmb fit)) i).val:Word w)) (j : Fin h) :
    mem (prev.base+j.val)=((oldBit (src:=src) j.val).toNat:Word w) := by
  rw [stored]
  by_cases real : ∃v,(src.vertex v).castLE fit=j
  · obtain ⟨v,rfl⟩:=real
    simp only [Fin.val_castLE,oldBit_at]
    exact congrArg (fun x : ℕ=>(x:Word w)) (DescentHubBits.live src.placement _ v)
  · have none : ¬∃v,(src.vertex v).val=j.val:=fun ⟨v,e⟩=>real ⟨v,Fin.ext e⟩
    rw [DescentHubBits.absent src.placement _ j real]
    simp [oldBit,none]

include link in
theorem issued_hubs {w oldH H : ℕ} (oldFits : Fintype.card src.V≤oldH) (newFits : Fintype.card tgt.V≤H)
    (owners prev mask : Bank) (out : ℕ) (mem : Memory w)
    (ofit : owners.Fits w out) (pf : prev.Fits w out) (mf : mask.Fits w out)
    (rs : H≤owners.size) (ms : H≤ mask.size) (oldRoom : oldH≤prev.size) (space : out+H<2^w)
    (old : ∀j : Fin oldH,mem (prev.base+j.val)=((Census.hub src.placement
      (src.vertex.trans (Fin.castLEEmb oldFits)) j).val:Word w))
    (layout : ∀i : Fin H,mem (owners.base+i.val)=((fields i.val).1:Word w) ∧
      mem (mask.base+i.val)=((fields i.val).2.toNat:Word w)) :
    let act:=paddedHubExpr oldH owners prev mask
    let dst:=image out H act mem
    (scan w out H act).Exec mem dst (4+H*(2*act.work+4)) ∧
      (∀j : Fin H,dst (out+j.val)=((Census.hub tgt.placement
        (tgt.vertex.trans (Fin.castLEEmb newFits)) j).val:Word w)) ∧
      ∀a,a<out ∨ out+H≤a→dst a=mem a := by
  let act:=paddedHubExpr oldH owners prev mask
  have inner : (ordinary owners prev mask).Fits w out:=
    ⟨⟨mf,trivial⟩,trivial,trivial,pf,ofit,trivial⟩
  refine ⟨scan_exec out H act mem ⟨⟨ofit,trivial⟩,trivial,inner,trivial⟩ space,?_,
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _⟩
  apply link.census_ordinary newFits
  intro i
  have value:=(lookup_nat owners mem (i.val:Word w) .row i.val rfl (i.isLt.trans_le rs) ofit.2.1).trans (layout i).1
  have flag:=(lookup_nat mask mem (i.val:Word w) .row i.val rfl (i.isLt.trans_le ms) mf.2.1).trans (layout i).2
  have bound:(fields i.val).1<2^w:=by
    change i.val/slots/(2^(k+1)-1)<2^w
    exact ((Nat.div_le_self _ _).trans (Nat.div_le_self _ _)).trans_lt (i.isLt.trans_le (by omega))
  have hw:=oldRoom.trans_lt pf.2.1
  have one:=lt_of_le_of_lt pf.1 pf.2.1
  rw [ProtocolRAMGeneratedWrite.read_image]
  change (if decide ((Expr.lookup owners .row).eval mem (i.val:Word w) < (oldH:Word w)) then
    (if (Expr.lookup mask .row).eval mem (i.val:Word w) == (0:Word w) then 0
      else (Expr.lookup prev (.lookup owners .row)).eval mem (i.val:Word w)) else 0) = _
  rw [value,flag]
  simp only [Fin.lt_def,Fin.val_cast_of_lt bound,Fin.val_cast_of_lt hw,decide_eq_true_eq]
  by_cases seen : (fields i.val).1<oldH
  · have v:=(lookup_nat prev mem (i.val:Word w) _ _ value (seen.trans_le oldRoom) pf.2.1).trans
      (priorBit (src:=src) oldFits prev mem old ⟨_,seen⟩)
    rw [ite_eq_left seen,v]
    have nonzero : (1 : Word w) ≠ 0 := by
      intro eq
      have h := congrArg Fin.val eq
      simp [Nat.mod_eq_of_lt one] at h
    cases e : (fields i.val).2 <;> simp [nonzero]
  · have missing : ¬∃v,(src.vertex v).val=(fields i.val).1:=by
      rintro ⟨v,eqn⟩
      exact seen (eqn ▸ (src.vertex v).isLt.trans_le oldFits)
    simp [seen,oldBit,missing]

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
