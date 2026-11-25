import OAI.Computability.NearSquareRoot.InterchangeBQuestRepairComponents
import OAI.Computability.NearSquareRoot.InterchangeBQuestSpectral
import OAI.Computability.NearSquareRoot.InterchangeSpectralComponents
import OAI.Computability.NearSquareRoot.InterchangeSpectralFibre

/-!
# Bounded spectral conversion of an extension-valued check row

The collector runs one bounded ground-field sweep per basis element and
accounts for the accumulating output bank in the parent's data-space bound.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace Interchange.BRepairRun

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom InterchangeAddress InterchangeSpectralRequest SwapRepair
open RepairRun (groupCell payloadCell payloadStore)

variable {I J K : Type} [DecidableEq J] [Field K] [Finite K] {m b n : ℕ} [NeZero b]
  {D : I → Type} {r : Regime I}

/-- Both spectral sweep directions on a grouped extension coefficient use
one recursive request per basis coordinate per field. -/
theorem extension_sweep (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f l : I → ℕ)
    (payload : (i : I) → Series (D i)) (basis : Series (BasisIndex m))
    (digit : K → Tree) (hd : Function.Injective digit)
    (hb : 2 ≤ b) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (hw : ∀ i, (payload i).count ≤ l i) (e : Environment K m)
    (inv : Bool) (fields : List J) (v : (i : I) → domain (J:=J) (b:=b) P G B f i × D i → Coeff K m) :
    let cell := groupCell (components K m).toEquiv basis (payloadCell (layoutRows ord P G B f) payload digit)
    let sweep := fun i => InterchangeSpectralFibre.lift
      (fun x => fields.foldl (fun y j => advance inv e.invRadix j y) x) (v i)
    BChargedTyped (r:=r) (l:=l) (b:=b) ord P G B f (InterchangePayloadBank.Good payload digit)
      (Fintype.card (BasisIndex m) * fields.length) (fun i => cell i (v i)) (fun i => cell i (sweep i)) := by
  intro cell sweep
  let records := layoutRows (b:=b) ord P G B f
  have st := layoutRows_station (b:=b) ord P G B f hb hf hp hg hs
  let machine := payloadStore records st payload hw digit hd
  apply groupStep machine (components K m).toEquiv basis v sweep
  intro d
  let x i t a := components K m (v i (a,t)) d
  let y i t := fields.foldl (fun g j => advance inv ((2:K)⁻¹) j g) (x i t)
  have coord i t : (fun a => components K m (sweep i (a,t)) d) = y i t :=
    InterchangeSpectralComponents.fold_component e ((2:K)⁻¹)
      (InterchangeSpectralComponents.ground_half e) inv fields d (fun a => v i (a,t))
  have eqout : (fun i => payloadCell records payload digit i (fun k => components K m (sweep i k) d)) =
      stackRun records (InterchangeSpectralPacked.pack P G B f payload digit y) := by
    funext i
    apply congrArg (stripe (records i))
    funext a
    apply congrArg (stripe (payload i))
    funext t
    exact congrArg digit (congrFun (coord i t) a)
  change BChargedTyped _ _ _ _ _ _ _
    (stackRun records (InterchangeSpectralPacked.pack P G B f payload digit x))
    (fun i => payloadCell records payload digit i (fun k => components K m (sweep i k) d))
  rw [eqout]
  exact InterchangeSpectralPacked.bounded_charged ord P G B f payload digit hb hf hp hg hs
    l hw hd inv ((2:K)⁻¹) fields x

end Interchange.BRepairRun

end

end NearSquareRoot
end Computability
end OAI
