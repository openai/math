import OAI.Hierarchy.DescentRegisteredSelectorScale
import OAI.Hierarchy.DescentRegisteredEntryPaid

namespace OAI
/-! # Coefficients of the actual four argument dictionaries, vector gather and resolver -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryBooks
open Computability.BorderVNP.Crossing DescentDatedAddressBook DescentPacking.PackedMatch.Local
open DescentGatheredVectorReshape DescentOperandVectorArena DescentSIMDLookup ProtocolRAM DescentArgumentWidthArithmetic
open DescentCompiler DescentCompiler.TerminalScale DescentDatedOperandReadPipeline DescentHaloWalkRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule}
    {d k age z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {src : Reached W G q ε S k age z D wire hist} {he : 0≤ ε} {T : StageInput W G u ε}
    {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
    {dst : Reached n.result G q ε S k (age+1) z' D' wire hist}
    (ticket : OrdinaryLink src he T c n dst)
    (gain tail p f payload seats hostLanes : ℕ) (old : Bank)
    (ordinary : ℕ→Stage.Dated.Ordinary)
variable (op : RotorSpec) (drift degree : ℕ) (ports : DatePorts) (stageFloor : ℕ)
local notation "Lₑ" => atDate G S op gain k age p tail drift degree payload seats ports
local notation "Tₑ" => (Lₑ).onTicket ticket gain tail p f payload seats hostLanes old ordinary
local notation "Eₑ" => (Tₑ).datedEntry ports stageFloor



/-- A common coefficient for every local register expression in the three phases.
The bounds use the same eleven field widths of the physically selected date.
The origins and pitches of the previous archive do not enter this coefficient. -/
theorem registered_middle_factors (U : ℕ) (positive : 16384≤ U)
    (sizes : ∀j,(Lₑ).bookMouthParameters j≤ U)
    (degreeFits : src.placement.degree ≤ (Lₑ).reference.degree) :
    let v:=Tₑ
    let W:=v.registeredFrom ports stageFloor
    let A:=v.registeredEntry ports stageFloor
    let L:=A.population W stageFloor
    let B:=W.bornBook
    let f:=W.reference
    let V:=W.vector
    let n:=DescentPackedActorMask.nodes (breadth f.degree*2^f.k) f.oldNodes f.capacity
    (L.count≤ U^14 ∧ 1024+4096*(L.donors+1)≤ U^14 ∧
      2048*(B.fields+1)≤ U^14 ∧ 256*(f.oldNodes+f.count+1)≤ U^14 ∧
      rowFactor V.pageCount V.lows V.radix n 26≤ U^14 ∧
      W.resolverFactor 745≤ U^14 ∧ 16384*(W.resolver.pageFactor+1)≤ U^14) :=by
  intro v W A L B f V n
  have deg : f.degree+1≤ U:=(Nat.add_le_add_right degreeFits 1).trans (sizes 1)
  have r : 2^f.k≤ U:=sizes 2
  have old_ : f.oldNodes≤ U:=sizes 3
  have cap : f.capacity≤ U:=sizes 4
  have nd : W.resolver.nodes≤ U:=sizes 5
  have lows : V.lows≤ U:=sizes 6
  have args : V.operands≤ U:=sizes 7
  let P:=U^4*U
  let N:=P*(U+U*6)
  let jobs:=U*(U*U)
  let pages:= (jobs+1)*(7*U*U+U+1)
  have donors : L.donors≤ P:=by
    change (f.degree+1)^4*2^f.k≤ U^4*U
    exact Nat.mul_le_mul (Nat.pow_le_pow_left deg 4) r
  have nn : n≤ N:=by
    change ((f.degree+1)^4*2^f.k)*(f.oldNodes+f.capacity*6)≤ P*(U+U*6)
    exact Nat.mul_le_mul donors (Nat.add_le_add old_ (Nat.mul_le_mul_right 6 cap))
  have jf : W.resolver.jobs≤ jobs:=Nat.mul_le_mul r (Nat.mul_le_mul nd args)
  have pf : W.resolver.pageFactor≤ pages:=
    Nat.mul_le_mul (Nat.add_le_add_right jf 1)
      (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 7 args) nd) nd) 1)
  have born : B.fields≤((U*U*6)*U)*7:=
    Nat.mul_le_mul_right 7 (Nat.mul_le_mul (Nat.mul_le_mul_right 6 (Nat.mul_le_mul r cap)) args)
  have rc : f.count≤(3+N)*2:=Nat.mul_le_mul_right 2 (Nat.add_le_add_left nn 3)
  have vf : rowFactor V.pageCount V.lows V.radix n 26≤
      1024*(7*U+1)*(U+1)*(U+1)*(26+34+N*61+1):=by
    change 1024*(7*V.operands+1)*(V.lows+1)*(2^f.k+1)*(26+34+n*61+1)≤_
    gcongr
  have counts : L.count≤1+(P*2+U):=
    Nat.add_le_add_left (Nat.add_le_add (Nat.mul_le_mul_right 2 donors) lows) 1
  have v₀ : 1024+4096*(L.donors+1)≤1024+4096*(P+1):=by gcongr
  have v₁ : 2048*(B.fields+1)≤2048*((U*U*6)*U*7+1):=by gcongr
  have v₂ : 256*(f.oldNodes+f.count+1)≤256*(U+(3+N)*2+1):=by gcongr
  have v₃ : W.resolverFactor 745≤512+128*(jobs*8+1)*746+16384*(pages+1):=by
    unfold PhysicalOrdinary.resolverFactor;gcongr
  have v₄ : 16384*(W.resolver.pageFactor+1)≤16384*(pages+1):=by gcongr
  have prices : (1+(P*2+U)≤ U^14) ∧ (1024+4096*(P+1)≤ U^14) ∧
      (2048*((U*U*6)*U*7+1)≤ U^14) ∧ (256*(U+(3+N)*2+1)≤ U^14) ∧
      (1024*(7*U+1)*(U+1)*(U+1)*(26+34+N*61+1)≤ U^14) ∧
      (512+128*(jobs*8+1)*746+16384*(pages+1)≤ U^14) ∧ (16384*(pages+1)≤ U^14) :=by
    dsimp only [N,P,pages,jobs]
    generalize U=u at positive ⊢
    obtain ⟨x,rfl⟩:=Nat.exists_eq_add_of_le positive
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> ring_nf <;> omega
  rcases prices with ⟨p₀,p₁,p₂,p₃,p₄,p₅,p₆⟩
  exact ⟨counts.trans p₀,v₀.trans p₁,v₁.trans p₂,v₂.trans p₃,vf.trans p₄,v₃.trans p₅,v₄.trans p₆⟩

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryBooks

end OAI
