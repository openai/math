import OAI.Hierarchy.DescentUniformColony
import OAI.Hierarchy.DescentColonyReindex
import OAI.Hierarchy.DescentMeasuredHistory

namespace OAI
/-! # Exact return of the concrete binary multiplier in the chosen physical stage -/

namespace Hierarchy.DescentColonies
open DescentGL DescentBinaryField
open scoped BigOperators Classical
noncomputable section
variable {k s : ℕ} {V : Type} [Fintype V] [DecidableEq V]

/-- The finite-address implementation has the identical modulus, score, and tie resolution
as the one-group scan used to construct the physical stage on arbitrary named sites. -/
theorem finiteColonyChoice_named (hk : 0<k) (e : V≃Fin s) (incoming : V→List V)
    (weight : V→Block k→ℕ) (adj : V→V→Prop) (spec : ∀u v,u∈incoming v↔adj u v)
    (a B Δ : ℕ) (branch : 2≤Δ) (limit : ∀v i,weight v i≤B) :
    let D := 32*Nat.clog 2 (2*Δ)
    let cost := fun μ : Nonzero k=>colonyCount (fun _ : Unit=>weight) adj a B Δ (fun _=>limit) (multiplier hk μ)
    finiteColonyChoice (fun t=>(incoming (e.symm t)).map e)
      (fun _ : Fin 1=>fun t=>weight (e.symm t)) D (2^a*B) =
      ((scanMinimum cost (nonzeroWords k)).1.map fun winner=>(modulus hk,winner.1)) := by
  dsimp only
  let D := 32*Nat.clog 2 (2*Δ)
  let cap := 2^a*B
  let cost := fun μ : Nonzero k=>colonyCount (fun _ : Unit=>weight) adj a B Δ (fun _=>limit) (multiplier hk μ)
  let input := fun t=>(incoming (e.symm t)).map e
  let load := fun _ : Fin 1=>fun t=>weight (e.symm t)
  have scores (μ : Nonzero k) : uniformColonyScore input load D cap (modulus hk) μ=cost μ := by
    let w := multiplierLoad weight (modulus hk) μ.val
    have lifted : multiplierLoad (fun t => weight (e.symm t)) (modulus hk) μ.val =
        fun t => w (e.symm t) := by
      funext t x
      unfold w multiplierLoad
      cases preimageWord (modulus hk) μ.val x <;> rfl
    have reindex := Scan.leafScore_reindex e incoming w D cap
    have actual := scannedColonyCount_eq incoming (fun _ : Unit=>weight) adj spec a B Δ branch
      (fun _=>limit) (multiplier hk μ)
    calc
      _ = Scan.leafScore input (fun t=>w (e.symm t)) D cap := by
        simp [uniformColonyScore,load,lifted]
      _ = Scan.leafScore incoming w D cap := reindex
      _ = cost μ := by
        rw [show w=rearrangedLoad weight (multiplier hk μ) from multiplierLoad_eq _ _ _ _ (multiplier_native hk μ)]
        simpa [scannedColonyCount,D,cap,cost] using actual
  change finiteColonyChoice input load D cap=_
  rw [finiteColonyChoice_eq]
  unfold uniformColonyChoice
  rw [(measuredLookup_spec k).1,modulus_found hk]
  change (scanMinimum (uniformColonyScore input load D cap (modulus hk)) (nonzeroWords k)).1.bind
    (fun winner => some (modulus hk,winner.1)) = (scanMinimum cost (nonzeroWords k)).1.map _
  rw [funext scores]; cases (scanMinimum cost (nonzeroWords k)).1 <;> rfl

end
end Hierarchy.DescentColonies

namespace Hierarchy.DescentSixParty.StageInput
open DescentColonies DescentGL DescentPacking DescentWalshTables StarKeys
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {G : PoweredGadget F} {u ε : ℝ} (T : StageInput W G u ε)
local notation "a" => DescentHostDegree.packExponent 20 T.Δ
local notation "D" => DescentHostDegree.gap T.Δ
local notation "cap" => T.wire*(T.z*G.b)*T.cap
local notation "weight" => blockMass W.graph T.pos T.block (W.siteUnits T.hub T.records T.wire 256 T.hist)

/-- State readback at the multiplier returned by the executable search, with the same
actual old-edge injection, coloring, and profile equivalence as the measured history. -/
theorem result_native_multiplier {s : ℕ} (he : 0≤ε) (e : T.V≃Fin s) (incoming : T.V→List T.V)
    (listed : ∀v w,v∈incoming w↔w∈T.near v) :
    ∃ (μ : Nonzero T.k) (α : DescentWalshTables.Bits T.k) (β : ZMod 2),
      finiteColonyChoice (fun t=>(incoming (e.symm t)).map e)
        (fun _ : Fin 1=>fun t=>weight (e.symm t)) D (2^a*cap)=some (modulus T.fieldBits,μ) ∧
      let L := multiplier T.fieldBits μ
      let blocks := reindexedBlock W.graph T.block L
      let fits := small_reindexed W.graph T.pos T.block (W.siteUnits T.hub T.records T.wire 256 T.hist) T.small L
      let home := occupiedHome W.graph T.pos blocks (W.siteUnits T.hub T.records T.wire 256 T.hist) T.near D a cap fits
      let color := fun v=>decide (binaryRow α ((address T.k).symm (blocks v))+β=0)
      let I := NativePair W.graph W.core home color T.cap
      let pick := colorPick W.graph W.core home color T.cap
      ∃ (hz : 0<T.z) (fit : ∀(i : I) s,W.graph.width (pick (i,s))=T.z*G.b)
        (profile : (T.result he).Choice ≃ (I→Profile G.C)),
        ∀ c,(T.result he).state c=W.selected G pick (fun _=>T.z) (fun _=>hz) fit
          (coloredPack W.graph W.core home color T.cap) (profile c) := by
  obtain ⟨μ,α,β,⟨winner,states⟩,_⟩ := T.result_scanned he
  refine ⟨μ,α,β,?_,states⟩
  have selected := finiteColonyChoice_named T.fieldBits e incoming weight
    (fun v x => x ∈ T.near v) listed a cap T.Δ T.degreeMin T.small
  dsimp only at selected
  rw [winner] at selected
  exact selected

end
end Hierarchy.DescentSixParty.StageInput

end OAI
