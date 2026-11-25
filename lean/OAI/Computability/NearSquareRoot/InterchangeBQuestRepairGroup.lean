import OAI.Computability.NearSquareRoot.InterchangeConfiguredRows
import OAI.Computability.NearSquareRoot.InterchangeRepairPayload
import OAI.Computability.NearSquareRoot.InterchangeBQuestRepair
import OAI.Computability.NearSquareRoot.InterchangeBQuestRepairComponents
import OAI.Computability.NearSquareRoot.InterchangeBQuestRepairTag
import OAI.Computability.NearSquareRoot.InterchangeBQuestRepairSweep
import OAI.Computability.NearSquareRoot.InterchangeBQuestPredictPayload

/-!
# Space-bounded execution of a configured repair group

The stack and continuation bounds use the local frame plus a single child
peak for the entire sequence of predictors, spectral sweeps and tables.
The resulting stream exchanges every main-field pair and preserves the
payload position, the independent register and its Hamming label.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace Interchange.StageKernel

open NearSquareRoot.InterchangeSpace
open OAI.LinearAlgebra.FiniteFourier SwapRepair StageRoute RepairSchedule
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom InterchangeAddress InterchangePayloadBank Support RectangleAtlas

variable {U : Type} {p k m b : ℕ} [Fact p.Prime] [NeZero b]
    {A : RectangleAtlas (nodeRectangles p k) (hammingReserve p k)}

/-- Execute one complete Hamming repair group on the native P192 stack machine.
Every requested record contains an original ground-field payload. -/
theorem execute_group_bounded {D : U → Type} {ρ : Regime U} {l : U → ℕ}
    (K : StageKernel p k m) (frame : Frame A m b)
    (P G S : U → Tape) (f : U → ℕ) (hb : 2 ≤ b) (hf : ρ.Has (tally ∘ f))
    (hP : Told ρ P) (hG : Told ρ G) (hS : Told ρ S)
    (data : (i : U) → Series (D i)) (hd : ∀ i, (data i).count ≤ l i)
    (digit : ZMod p → Tree) (hinj : Function.Injective digit)
    (lanes : Series (PackedPencil.Index m)) (labels : Series (HammingLabels p k))
    (x : (i : U) → GroupRow p k m →
      domain (J:=Fin (hammingReserve p k+m+hammingReserve p k)) (b:=b) P G S f i × D i → ZMod p) :
    let a := hammingReserve p k
    let ord := Equiv.refl (Fin (a+m+a))
    let records := layoutRows (b:=b) ord P G S f
    let result := fun i w (z : domain (J:=Fin (a+m+a)) (b:=b) P G S f i × D i) =>
      x i w (InterchangeSpectralFibre.swapMain (mainSlots a m) z.1,z.2)
    BChargedTyped (r:=ρ) (l:=l) (b:=b) ord P G S f (Good data digit) (K.calls A)
      (render records data (lanes.cart labels) digit x)
      (render records data (lanes.cart labels) digit result) := by
  intro a ord records result
  let Z i := domain (J:=Fin (a+m+a)) (b:=b) P G S f i × D i
  let slot := mainSlots a m
  let fields := (List.finRange m).map slot
  let basis := Series.natural (2^primeRepairExtensionExponent 2 m)
  let cell := RepairRun.payloadCell records data digit
  let st := layoutRows_station (b:=b) ord P G S f hb hf hP hG hS
  let base := RepairRun.payloadStore (r:=ρ) records st data hd digit hinj
  let zone (i : U) (t : Request b) :=
    (allowed f (countRows (b:=b) ord P G S f) l i t ∧ ∀ j, Good data digit i (t.contents j)) ∧
      inherited b (P i) (G i) (S i) t
  let price := fun u : Move (nodeRectangles p k) (Fin m) K.source K.target => (A.routeWord u).price
  let predCost := order m * (moveCharges (PackedPencil.Index m) price).count
  let paid := Fintype.card (BasisIndex m) * m
  let machine := RepairRun.groupStore base (components (ZMod p) m).toEquiv basis
  let tag (i : U) (z : Z i) := InterchangeSpectralFibre.tag slot z.1
  let fw (i : U) := InterchangeSpectralFibre.lift (D:=D i) (forward (a:=a) (b:=b) (P:=P i) (G:=G i) (S:=S i) (f i) K.env)
  let bw (i : U) := InterchangeSpectralFibre.lift (D:=D i) (backward (a:=a) (b:=b) (P:=P i) (G:=G i) (S:=S i) (f i) K.env)
  let pred i := predict (nodeRectangles p k) K.source K.target K.matrix K.env
    (InterchangeSpectralFibre.withPayload (D i) (extendLayout (P i) (G i) (S i) (frame.layout (f i))))
  let obs (i : U) := RepairRun.groupCell (components (ZMod p) m).toEquiv basis cell i
  have htag : BRepairRun.Tagged (Request.job b) ρ (countRows (b:=b) ord P G S f) l zone obs tag :=
    RepairChecks.bounded_groupedTag (Request.job b) zone ord P G S f hb hf hP hG hS data hd
    digit hinj slot basis
  have hpred (y : (i : U) → Data (ZMod p) (HammingLabels p k) (Z i) (width m) m) :
      BRepairRun.Runs (Request.job b) ρ (countRows (b:=b) ord P G S f) l zone obs predCost
        (RepairRun.flatten y) (RepairRun.flatten fun i => pred i (y i)) := by
    apply BRepairRun.predictorRuns base basis (lanes.cart labels)
    exact execute_predict_payload_bounded frame K.source K.target K.matrix K.env P G S f hb hf hP hG hS data hd
      digit hinj lanes labels y
  have hfwd (v : (i : U) → Z i → Coeff (ZMod p) m) :
      BHop (Request.job b) ρ (countRows (b:=b) ord P G S f) l zone paid
        (together ρ.header (fun i => obs i (v i))) (fun i => obs i (fw i (v i))) := by
    have h := BRepairRun.extension_sweep (r:=ρ) ord P G S f l data basis digit hinj hb hf hP hG hS
      hd K.env false fields v
    dsimp only at h
    rw [show fields.length = m by simp [fields]] at h
    exact h
  have hinv (v : (i : U) → Z i → Coeff (ZMod p) m) :
      BHop (Request.job b) ρ (countRows (b:=b) ord P G S f) l zone paid
        (together ρ.header (fun i => obs i (v i))) (fun i => obs i (bw i (v i))) := by
    have h := BRepairRun.extension_sweep (r:=ρ) ord P G S f l data basis digit hinj hb hf hP hG hS
      hd K.env true fields.reverse v
    dsimp only at h
    rw [show fields.reverse.length = m by simp [fields]] at h
    exact h
  let input := packGroup x
  let output i := RepairSchedule.payload (D i) frame K.source K.target K.matrix K.env K.table
    (P i) (G i) (S i) (f i) (input i)
  have hr := BRepairRun.execute machine K.env K.table tag htag fw bw pred predCost paid hpred hfwd hinv input
  have final := BRepairRun.ungroupRuns base basis (labels.cart (Series.natural (width m)))
    (lanes.cart labels) input output hr
  have hout : streams output = result := by
    funext i t z
    rcases t with ⟨⟨s,d⟩,w⟩
    dsimp only [streams,output]
    rw [payload_of_table _ frame K.source K.target K.matrix K.factor K.env K.table K.correct]
    exact congrFun ((components (ZMod p) m).apply_symm_apply _) d
  change BChargedTyped (r:=ρ) (l:=l) (b:=b) ord P G S f (Good data digit) (K.calls A) _ _
  rw [←K.calls_eq_schedule A]
  rw [hout, show streams input = x from streams_packGroup x] at final
  exact final

end Interchange.StageKernel

end

end NearSquareRoot
end Computability
end OAI
