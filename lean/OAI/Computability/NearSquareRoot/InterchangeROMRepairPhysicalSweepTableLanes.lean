import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepTable
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomROM

/-! # Compiling the three spectral inputs over packed variable-width records -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.SweepTable

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open InterchangeROMTable LoomRegisters CommonRegisters Space GeneratorSyntax

def lookup (p half : ℕ) (inv : Bool) : Cmd :=
  romPayload 0 1 (spelledTable (table p half inv))

def factor (p half : ℕ) (inv : Bool) : ℕ :=
  romPayloadFactor 3 1 (spelledTable (table p half inv))

theorem lookup_within (p half : ℕ) (inv : Bool) : Within 4 (lookup p half inv) :=
  romPayload_within _ _ _

theorem effective_lookup {X : Type} [Primcodable X] {p half : X → ℕ} {inv : X → Bool}
    (hp : Computable p) (hh : Computable half) (hi : Computable inv) :
    Effective ltr (fun x => lookup (p x) (half x) (inv x)) :=
  effective_romPayload (Computable.const 0) (Computable.const 1) (computable_spelled_table hp hh hi)

theorem computable_factor {X : Type} [Primcodable X] {p half : X → ℕ} {inv : X → Bool}
    (hp : Computable p) (hh : Computable half) (hi : Computable inv) :
    Computable (fun x => factor (p x) (half x) (inv x)) :=
  ((primrec_romPayloadFactor (Primrec.const 3) (Primrec.const 1) Primrec.id).to_comp).comp
    (computable_spelled_table hp hh hi)

def mark (tag : Ordering) := comparisonMark (comparisonCode tag)

/-- Every tagged symbol is replicated across the payload of its outer record.
Empty outer and inner streams need no special branch in the command. -/
theorem lookup_bounded {A : Type} {P : A → Type} (p half : ℕ) (inv : Bool)
    (rows : Series A) (payload : (a : A) → Series (P a)) (width : ℕ)
    (hw : ∀ a, (payload a).count ≤ width)
    (tag : A → Ordering) (x y : (a : A) → P a → ZMod (p+1))
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let row (v : (a : A) → P a → Tree) := stripe rows fun a => stripe (payload a) (v a)
    let v₀ := row (fun a _ => mark (tag a))
    let v₁ := row (fun a i => numeral (x a i).val)
    let v₂ := row (fun a i => numeral (y a i).val)
    let result := row (fun a i => numeral (InterchangeSpectralStep.value inv
      (half : ZMod (p+1)) (tag a) (x a i) (y a i)).val)
    let cost := factor p half inv * (rows.count * (width+1) + 1)
    BoundedFits env (lookup p half inv) (pile 0 (Task.forest id [v₀,v₁,v₂]) r)
      (pile 0 (Task.forest id [result]) r) cost (base+cost) cost := by
  let v (a : A) (i : P a) : Fin 3 → Tree := ![mark (tag a),numeral (x a i).val,numeral (y a i).val]
  let w (a : A) (i : P a) (_ : Fin 1) :=
    numeral (InterchangeSpectralStep.value inv (half : ZMod (p+1)) (tag a) (x a i) (y a i)).val
  exact romPayload_bounded (0 : Fin 3) rows payload width hw v w (table p half inv)
    (fun a i => correct p half inv (tag a) (x a i) (y a i)) env r base hr

end InterchangeROMRepair.SweepTable

end NearSquareRoot
end Computability
end OAI
