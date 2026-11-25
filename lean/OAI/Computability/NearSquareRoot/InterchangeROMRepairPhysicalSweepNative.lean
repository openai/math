import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepPivot
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBroadcast
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepTableLanes

/-! # The compiled one-field spectral operation on packed ground-ring records -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Sweep

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  CommonRegisters Space InterchangeROMAddress InterchangeAddress GeneratorSyntax
open InterchangeROMRepair.Physical (Allowance)
open InterchangeROMTable (numeral)

/-- One scalar stream of the external lane bank. Each symbol has the ground modulus p+1. -/
abbrev row {A D : Type} (rows : Series A) (payload : Series D) {p : ℕ}
    (x : A → D → ZMod (p+1)) :=
  stripe rows fun a => stripe payload fun d => numeral (x a d).val

def command (mask : Cmd) (b n j p half : ℕ) (inv : Bool) : Cmd :=
  one mask Physical.Broadcast.command (pivot b n j) (SweepTable.lookup p half inv)

def regs (maskRegs : ℕ) := max maskRegs (max Physical.Broadcast.regs (max pivotRegs 4))

theorem command_within {mask : Cmd} {R : ℕ} (hm : Within R mask) (b n j p half : ℕ) (inv : Bool) :
    Within (regs R) (command mask b n j p half inv) := by
  apply one_within (by unfold regs; omega)
  · exact RegisterSelect.within_mono (le_max_left ..) _ hm
  · exact RegisterSelect.within_mono (by unfold regs; omega) _ Physical.Broadcast.within
  · exact RegisterSelect.within_mono (by unfold regs; omega) _ (pivot_within b n j)
  · exact RegisterSelect.within_mono (by unfold regs; omega) _ (SweepTable.lookup_within p half inv)

theorem effective_command {X : Type} [Primcodable X] {mask : X → Cmd}
    {b n j p half : X → ℕ} {inv : X → Bool} (hm : Effective ltr mask)
    (hb : Computable b) (hn : Computable n) (hj : Computable j) (hp : Computable p)
    (hh : Computable half) (hi : Computable inv) :
    Effective ltr (fun x => command (mask x) (b x) (n x) (j x) (p x) (half x) (inv x)) :=
  effective_one hm (effective_const ltr Physical.Broadcast.command)
    (effective_pivot hb hn hj) (SweepTable.effective_lookup hp hh hi)

def uniformCost (k : ℕ) : Allowance := ⟨k,k,k⟩

variable {I J D : Type} [DecidableEq J] {b n : ℕ}
  (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f l : I → ℕ)
  (payload : I → Series D) (j : J) (p half : ℕ) (inv : Bool)
  (x : (i : I) → domain (J:=J) (b:=b) P G B f i → D → ZMod (p+1)) (i : I)

abbrev data (k : domain (J:=J) (b:=b) P G B f i) :=
  stripe (payload i) fun d => numeral (x i k d).val

abbrev direction (k : domain (J:=J) (b:=b) P G B f i) :=
  InterchangeSpectralStep.direction (number (k.2.1 j)) (number (k.2.2.2.1 j))

abbrev request := child ord P G B f l j (data P G B f payload p x) i

/-- The allowance records a single recursive prediction cost and the linear shape/lookup passes. -/
def packedCost (am ac : Allowance) : Allowance :=
  let rows := layoutRows (b:=b) ord P G B f i
  let h := header (f i) (P i) (G i) (B i)
  let q := request ord P G B f l payload j p x i
  let u := row rows (payload i) (x i)
  let v := row rows (payload i) fun k => x i (InterchangeSpectralRequest.swapAt j k)
  let y := row rows (payload i) fun k d =>
    InterchangeSpectralRequest.advance inv (half : ZMod (p+1)) j (fun k => x i k d) k
  let tm := fun k => SweepTable.mark (direction P G B f j i k)
  let mark := stripe rows tm
  let tags := Physical.Broadcast.output rows (fun _ => payload i) tm
  let a := Physical.Broadcast.factor * ((Task.forest id [mark,u]).count + tags.count + 1)
  let z := SweepTable.factor p half inv * (rows.count * (l i + 1) + 1)
  oneCost (send h) u v mark tags y am (uniformCost a) (pivotCost b n (ord j) h q.header u v ac)
    (uniformCost z)

/-- Each scalar in each physical record computes the requested forward or inverse spectral step. -/
theorem packed_bounded (mask parent : Cmd) (env : Env) (am ac : Allowance)
    (hw : (payload i).count ≤ l i)
    (hm : Run (parent::env) mask (send (header (f i) (P i) (G i) (B i)))
      (stripe (layoutRows (b:=b) ord P G B f i) fun k => SweepTable.mark (direction P G B f j i k)) am)
    (hc : let q := request ord P G B f l payload j p x i
      Run (parent::env) parent ((Request.job b).issue q) ((Request.job b).reply q) ac) :
    let rows := layoutRows (b:=b) ord P G B f i
    let h := send (header (f i) (P i) (G i) (B i))
    Run (parent::env) (command mask b n (ord j) p half inv) (.fork h (row rows (payload i) (x i)))
      (row rows (payload i) fun k d =>
        InterchangeSpectralRequest.advance inv (half : ZMod (p+1)) j (fun k => x i k d) k)
      (packedCost ord P G B f l payload j p half inv x i am ac) := by
  apply run_one hm
  · exact Physical.Broadcast.bounded _ (fun _ => payload i) _ _
      (parent::env)
  · exact pivot_bounded ord P G B f l j (data P G B f payload p x) i parent env ac hc
  · exact SweepTable.lookup_bounded p half inv _ (fun _ => payload i) (l i) (fun _ => hw)
      (direction P G B f j i) (x i) (fun k => x i (InterchangeSpectralRequest.swapAt j k))
      (parent::env)

end InterchangeROMRepair.Sweep

end

end NearSquareRoot
end Computability
end OAI
