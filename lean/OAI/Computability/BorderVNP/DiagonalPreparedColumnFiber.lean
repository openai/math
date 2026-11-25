import OAI.Computability.BorderVNP.DiagonalAcceptedGuardedCores
import OAI.Computability.BorderVNP.DiagonalJointFiberColumn

/-! # The live column on the original exterior and the decoded guarded paths -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing ResidueBox ResiduePins ResidueIndex TeamContraction ProcessorSlots TeamContraction.JointHeader
open RoutingISA RoutingISA.Evaluator CellMacro.Generator BorderVNP.Cube
open scoped Classical BigOperators

variable {F : Type} [Field F] {D m : ℕ} {ι : Type} [Fintype ι] {G : PaidIdentity F D m}
    {aux : ι → F} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField G aux q k s ord} {chart : AdvisedBranch C} [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r mult tally w pin exp : ℕ} (reader : ChosenReader chart (R+1) r mult tally w pin)

local notation "pdim" => pairedTableParameters (k+1) s
local notation "Idx" => Index (Fin (Module.finrank (ZMod C.p) chart.E)) (Fin pdim) (chart.pinRadius (R+1) r)

variable {axes box lanes sel sym n dim width : ℕ} {id : TableEntry axes box lanes sel sym → ℕ} {gen : Fragment IO}
    {X Hist : Type} [Fintype X] [Fintype Hist] {Route : Hist → Type} {Bank : Hist → Type}
    {Report : (i : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → (q : Hist) → Route q → Type}
    (S : X → Fin (R+1) → PositiveTeam id gen n w)
    (J : ∀ x (p : (u : Fin (R+1)) → (S x u).Prefix),
      JoinedCells (fun u => (S x u).pub) (fun u => (S x u).postMemory) (fun u => (S x u).generated) p)
    (prep : JointBeforeCells S ≃ PreparedFields (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) Hist
      (Fin ((R+1)*dim*width) → Bool) Route Report)
    (banks : ∀ f : PreparedFields (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) Hist
      (Fin ((R+1)*dim*width) → Bool) Route Report, (J (prep.symm f).1 (prep.symm f).2).Private ≃ Bank f.2.1)
    (rows : ∀ i z v, PreparedCellRows S J prep banks i z v)

variable {reserve groups cap : ℕ}
    (header : (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → (z : Hist) → Route z × Bank z → PositiveFields reserve axes groups cap (R+1) dim width)
    (guard : (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → (z : Hist) → Route z × Bank z → Prop)
    (sound : ∀ i z v rr c, let A := (rows i z v).candidate
      (A.joined rr c (A.candidate rr c).1).privateWeight (A.candidate rr c).2 ≠ 0 → guard i z v)
    (complete : ∀ i z v, guard i z v → ((rows i z v).candidate).Completion (header i z v))
    {Term : (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → Hist → Type}
    [∀ i z, Fintype (Term i z)]
    (decode : ∀ i z, {v : Route z × Bank z // guard i z v} ≃ Term i z)
    (assigned : ∀ i, (Σ z, Term i z) → Tally (Fin (R+1)) (Fin (pairedTableParameters (k+1) s)) (G.Entry ⊕ ι) exp)

local notation3 (prettyPrint := false) "restored(" i "," z "," v "," hv ")" =>
  restoreGuarded S J prep banks rows header guard complete i z v hv

set_option maxHeartbeats 1200000 in
/-- Combine the actual supported execution, its physical report checks and
the original per-history path decoders. Readback is needed only on canonical
inverse paths. The result handles every complete execution, including every
zero-valued matrix entry, with the original team numbers and reader input. -/
noncomputable def NativeColumnFiber.ofPrepared (j : Idx)
    (teamAt : ∀ i z v (hv : guard i z v) u, let a := restored(i,z,v,hv)
      ((S a.1 u).finish (a.2.val.1 u) (a.2.property.2 u)).val.2.2 ((S a.1 u).pub 0).val = u.val)
    (imageAt : ∀ i z v (hv : guard i z v), let a := restored(i,z,v,hv)
      let term := assigned i ⟨z,decode i z ⟨v,hv⟩⟩
      ReaderImage reader (S a.1 0).pub ((S a.1 0).finish (a.2.val.1 0) (a.2.property.2 0)).val.2.2 i
        ((boxPinCodec pdim reader.rankFits reader.boxFits).encode j) term.exponents (fun l => ∑ u,term.counts u l)) :
    NativeColumnFiber reader S J (fun i => Σ z, Term i z) assigned j := by
  let accepted := acceptedGuardedEquiv S J prep banks rows header guard sound complete
  let term := Equiv.sigmaCongrRight fun i => Equiv.sigmaCongrRight (decode i)
  refine ⟨accepted.trans term,acceptedGuarded_privateWeight S J prep banks rows header guard sound complete,?_,?_⟩
  · intro a u
    let z := accepted a
    have back : accepted.symm z=a := accepted.symm_apply_apply a
    rw [←back]
    exact teamAt z.1 z.2.1 z.2.2.val z.2.2.property u
  · intro a
    let z := accepted a
    let t := assigned z.1 ⟨z.2.1,decode z.1 z.2.1 z.2.2⟩
    let goal (a' : AcceptedExterior S J) := ReaderImage reader (S a'.1 0).pub
      ((S a'.1 0).finish (a'.2.val.1 0) (a'.2.property.2 0)).val.2.2 z.1
      ((boxPinCodec pdim reader.rankFits reader.boxFits).encode j) t.exponents (fun l => ∑ u,t.counts u l)
    change goal a
    exact Eq.mp (congrArg goal (accepted.symm_apply_apply a)) (imageAt z.1 z.2.1 z.2.2.val z.2.2.property)

end Diagonal

end BorderVNP
end Computability
end OAI
