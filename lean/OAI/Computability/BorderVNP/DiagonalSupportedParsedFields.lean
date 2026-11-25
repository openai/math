import OAI.Computability.BorderVNP.DiagonalExteriorParsedPrefixes

/-! # Recovering the actual header and pin on joint pre-call support -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open TeamContraction TeamContraction.ProcessorSlots CellMacro.Generator BorderVNP.Cube

variable {X : Type} {R n w axes box lanes selectors symbols : ℕ}
    {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    {positive support : X → Prop} (U : {x // positive x} → Fin (R+1) → PinStart gen n w)
    (prepared : ∀ x : {x // positive x}, support x.val ↔ jointSupport id (U x))
    (T : {x // positive x ∧ support x} → Fin (R+1) → PositiveTeam id gen n w)
    (same : ∀ x u, (T x u).start=U ⟨x.val,x.property.1⟩ u)

/-- The pre-call domain used by the signed contraction is restricted to
shared wires at which every team can return. Removing that restriction after
choosing the whole tuple of returns preserves the wires and every return. -/
noncomputable def positivePrefixes :
    JointBeforeCells T ≃ ((x : {x // positive x}) × ((u : Fin (R+1)) → (U x u).Prefix id)) := by
  let e : {x // positive x ∧ support x} ≃ {x : {x // positive x} // jointSupport id (U x)} :=
    ⟨fun x => ⟨⟨x.val,x.property.1⟩,(prepared _).1 x.property.2⟩,
     fun x => ⟨x.val.val,x.val.property,(prepared x.val).2 x.property⟩,fun _ => rfl,fun _ => rfl⟩
  let retitle := Equiv.sigmaCongrLeft' (β:=fun x => (u : Fin (R+1)) → (T x u).Prefix) e
  exact retitle.trans (supportedPrefixes U (fun x => T (e.symm x)) fun x u => same (e.symm x) u)

/-- Every physical exterior bit survives the inverse reindexing. -/
theorem positivePrefixes_symm_wire (a : (x : {x // positive x}) × ((u : Fin (R+1)) → (U x u).Prefix id)) :
    ((positivePrefixes U prepared T same).symm a).1.val = a.1.val := rfl

private theorem castPrefixReturn {A B : PinStart gen n w} (eqn : A=B) (v : A.Prefix id) :
    ((Equiv.cast (congrArg (fun z : PinStart gen n w => z.Prefix id) eqn) v).2.val) = v.2.val := by
  subst B
  rfl

private theorem castPrefixDigits {A B : PinStart gen n w} (eqn : A=B) (v : A.Prefix id) :
    List.ofFn ((Equiv.cast (congrArg (fun z : PinStart gen n w => z.Prefix id) eqn) v).1) = List.ofFn v.1 := by
  subst B
  rfl

/-- Support proofs leave the actual returned chronological trace and memory intact. -/
theorem positivePrefixes_symm_return (a : (x : {x // positive x}) × ((u : Fin (R+1)) → (U x u).Prefix id))
    (u : Fin (R+1)) : (((positivePrefixes U prepared T same).symm a).2 u).2.val = (a.2 u).2.val := by
  let x : {x // positive x ∧ support x} := ⟨a.1.val,a.1.property,(prepared a.1).2 (fun v => ⟨a.2 v⟩)⟩
  exact castPrefixReturn (same x u).symm (a.2 u)

/-- Every actual pin guess retains its original physical digit order. -/
theorem positivePrefixes_symm_digits (a : (x : {x // positive x}) × ((u : Fin (R+1)) → (U x u).Prefix id))
    (u : Fin (R+1)) : List.ofFn (((positivePrefixes U prepared T same).symm a).2 u).1 = List.ofFn (a.2 u).1 := by
  let x : {x // positive x ∧ support x} := ⟨a.1.val,a.1.property,(prepared a.1).2 (fun v => ⟨a.2 v⟩)⟩
  exact castPrefixDigits (same x u).symm (a.2 u)

end RoutingISA.Evaluator.PinStart

namespace TeamContraction

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator Routing ProcessorSlots JointHeader
open CellMacro.Generator BorderVNP.Cube

variable {R r t d link inner n w reserve axes groups cap dim tally : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (args : Fin (R+1) → UnitAddresses)
    (live : Fin d → Bool) (L : WireLayout (R+1) r link) (fixed : Block (R+1))
    (hw : 0<w) (size : ∀ i, (args i).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ i, (G.transferFrame i (args i).header (args i).dst).Fits w (base i))
    (width : L.header=PositiveFields.width reserve axes groups cap (R+1) dim tally)

local notation "Fields" => PositiveFields reserve axes groups cap (R+1) dim tally
local notation "Cube" => Physical.Broadcast axes groups cap
local notation "Claim" => (Fin ((R+1)*dim*tally) → Bool)
local notation "headers" => positiveExteriorFieldsEquiv G args live L fixed hw size base fit width
variable {box lanes selectors symbols : ℕ} {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    (U : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext} → Fin (R+1) → PinStart gen n w)
    (ib hb sb : Fin (R+1) → ℕ)
    (pinWidth : ∀ x u, (U x u).guessWidth=(G.pinLayout u (ib u) (hb u) (sb u)).guessWidth)

/-- The entire remaining physical exterior and its actual returning
preparations at a specified raw pin and parsed positive header. -/
abbrev ParsedPreCall (id : TableEntry axes box lanes selectors symbols → ℕ)
    (i : Fin d → Bool) (p : PositiveFields reserve axes groups cap (R+1) dim tally) :=
  (ext : HeaderExterior L p.bits) × pinnedPreps G args live U ib hb sb pinWidth id ((headers).symm ⟨p,ext⟩) i

variable {Hist : Type} {Route : Hist → Type} {Report : (Fin d → Bool) → (q : Hist) → Route q → Type}
    (code : Hist ↪ (Fin reserve → Bool))
    (valid : ∀ (i : Fin d → Bool) (p : PositiveFields reserve axes groups cap (R+1) dim tally),
      ParsedPreCall G args live L fixed hw size base fit width U ib hb sb pinWidth id i p → ∃ q, code q=p.profile)
    (routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
      (Σ c : Physical.Broadcast axes groups cap,
        ParsedPreCall G args live L fixed hw size base fit width U ib hb sb pinWidth id i ⟨code q,c,claim⟩) ≃
      Σ v : Route q,Report i q v)

local notation3 (prettyPrint := false) "prep" => jointPreparedFields (id := id) (gen := gen) G args live L fixed hw size base fit width U ib hb sb
  pinWidth code valid routed

/-- Inverse decoding restores the entire physical exterior supplied by the
routing inverse, including every relay bit and every unused packet position. -/
theorem jointPreparedFields_symm_wire (i : Fin d → Bool) (q : Hist) (v : Route q)
    (c : Claim) (a : Report i q v) :
    ((prep).symm ⟨i,q,v,c,a⟩).1.val = ((routed i q c).symm ⟨v,a⟩).2.1.val := rfl

/-- The receiver sees this same published profile, cube declaration and
subtotal bank on each participating link of a restored shared history. -/
theorem jointPreparedFields_symm_header (i : Fin d → Bool) (q : Hist) (v : Route q)
    (c : Claim) (a : Report i q v) (block : Block (R+1)) :
    observed L ((prep).symm ⟨i,q,v,c,a⟩).1.val block =
      ((⟨code q,((routed i q c).symm ⟨v,a⟩).1,c⟩ : Fields)).bits := by
  rw [jointPreparedFields_symm_wire]
  exact ((routed i q c).symm ⟨v,a⟩).2.1.property block

/-- The restored preparation uses precisely this raw substituted index at
the lead team; all other teams use the unique empty guess. -/
theorem jointPreparedFields_symm_pin (i : Fin d → Bool) (q : Hist) (v : Route q)
    (c : Claim) (a : Report i q v) (u : Fin (R+1)) :
    let z := (prep).symm ⟨i,q,v,c,a⟩
    (z.2 u).1 = (Equiv.arrowCongr (finCongr (pinWidth z.1 u).symm) (Equiv.refl Bool))
      ((G.jointGuess ib hb sb).symm i u) := rfl

/-- The returned trace, registers and RAM are those reconstructed by the
routing inverse. In particular this reindexing adds no private decisions. -/
theorem jointPreparedFields_symm_return (i : Fin d → Bool) (q : Hist) (v : Route q)
    (c : Claim) (a : Report i q v) (u : Fin (R+1)) :
    let z := (prep).symm ⟨i,q,v,c,a⟩
    (z.2 u).2.val = (((routed i q c).symm ⟨v,a⟩).2.2 u).val := rfl

variable {support : (Exterior R r link → Bool) → Prop}
    (prepared : ∀ x : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext},
      support x.val ↔ PinStart.jointSupport id (U x))
    (T : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext ∧ support ext} →
      Fin (R+1) → PositiveTeam id gen n w)
    (same : ∀ x u, (T x u).start=U ⟨x.val,x.property.1⟩ u)

/-- The joint pre-call histories used by the actual clocked bodies, including
the physical-support restriction in the positive sum. The inverse supplies a
genuine reaching preparation for each team at its actual substituted pin. -/
noncomputable def supportedPreparedFields :
    JointBeforeCells T ≃ PreparedFields (Fin d → Bool) Hist Claim Route Report :=
  (PinStart.positivePrefixes U prepared T same).trans prep

local notation3 (prettyPrint := false) "decoded" => supportedPreparedFields G args live L fixed hw size base fit width
  U ib hb sb pinWidth code valid routed prepared T same

/-- On supported physical teams, inverse decoding gives the exact original
complete exterior, including all the unobserved routing and padding positions. -/
theorem supportedPreparedFields_symm_wire (i : Fin d → Bool) (q : Hist) (v : Route q)
    (c : Claim) (a : Report i q v) :
    ((decoded).symm ⟨i,q,v,c,a⟩).1.val = ((routed i q c).symm ⟨v,a⟩).2.1.val := rfl

/-- The real supported team path has the very trace, register file and memory
reconstructed by the routed return for this pin, history and proposed subtotal. -/
theorem supportedPreparedFields_symm_return (i : Fin d → Bool) (q : Hist) (v : Route q)
    (c : Claim) (a : Report i q v) (u : Fin (R+1)) :
    let z := (decoded).symm ⟨i,q,v,c,a⟩
    (z.2 u).2.val = (((routed i q c).symm ⟨v,a⟩).2.2 u).val :=
  PinStart.positivePrefixes_symm_return U prepared T same ((prep).symm ⟨i,q,v,c,a⟩) u

private theorem ofFn_digits_cast {d e : ℕ} (h : d=e) (f : Fin d → Bool) :
    List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) f) = List.ofFn f := by
  subst e
  rfl

/-- The exact pin guessed on the supported team in the inverse image of a
substituted row, with the authentic empty pin stream away from team zero. -/
theorem supportedPreparedFields_symm_digits (i : Fin d → Bool) (q : Hist) (v : Route q)
    (c : Claim) (a : Report i q v) (u : Fin (R+1)) :
    let z := (decoded).symm ⟨i,q,v,c,a⟩
    List.ofFn (z.2 u).1 = List.ofFn ((G.jointGuess ib hb sb).symm i u) := by
  exact (PinStart.positivePrefixes_symm_digits U prepared T same ((prep).symm ⟨i,q,v,c,a⟩) u).trans
    (ofFn_digits_cast (pinWidth _ u).symm _)

/-- Reading the decoder in the forward direction identifies all physical
exterior bits and the exact original preparation on every supported team,
including histories whose later contraction weight vanishes. -/
theorem supportedPreparedFields_read (z : JointBeforeCells T) :
    let out := decoded z
    let seen := (routed out.1 out.2.1 out.2.2.2.1).symm ⟨out.2.2.1,out.2.2.2.2⟩
    z.1.val=seen.2.1.val ∧ ∀ u : Fin (R+1),
      (z.2 u).2.val=(seen.2.2 u).val ∧ List.ofFn (z.2 u).1=List.ofFn ((G.jointGuess ib hb sb).symm out.1 u) := by
  obtain ⟨⟨i,q,v,c,a⟩,rfl⟩ := (decoded).symm.surjective z
  dsimp only
  rw [(decoded).apply_symm_apply ⟨i,q,v,c,a⟩]
  exact ⟨supportedPreparedFields_symm_wire G args live L fixed hw size base fit width U ib hb sb pinWidth code
    valid routed prepared T same i q v c a,fun u => ⟨supportedPreparedFields_symm_return G args live L fixed hw size
    base fit width U ib hb sb pinWidth code valid routed prepared T same i q v c a u,
    supportedPreparedFields_symm_digits G args live L fixed hw size base fit width U ib hb sb pinWidth code
      valid routed prepared T same i q v c a u⟩⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
