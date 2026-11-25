import OAI.Computability.MultitapeWeakETH.WitnessWalkRank
import OAI.Computability.MultitapeWeakETH.TerminalProgram

/-! # Bounding local replies on malformed private candidates -/

namespace OAI.Computability.MultitapeWeakETH.WitnessWalk

open IntegerMultiplication Code
open private Meter.count Meter.program Meter.length stored fits fits_poly fits_iff from OAI.Computability.MultitapeWeakETH.WitnessWalkClock
open private sublist_size from OAI.Computability.MultitapeWeakETH.WitnessWalkSpace

variable {D : Type}

def replySize (jobs : List Job) := size (((jobs,([] : Bits.Word)),([] : List Tally)) : Store)

def SafeReply (degree room : ℕ) (bits : Bits.Word) (answer : Answer) : Prop :=
  answer.1.1.length ≤ degree ∧ replySize answer.1.1 ≤ room ∧ answer.1.2.length ≤ bits.length

instance (degree room : ℕ) (bits : Bits.Word) (a : Answer) : Decidable (SafeReply degree room bits a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private abbrev ReplyInput := (Tally × Bits.Word) × Answer

private def gate (degree : ℕ) (q : ReplyInput) : Option Answer :=
  if SafeReply degree q.1.1.length q.1.2 q.2 then some q.2 else none

private theorem gate_poly (degree : ℕ) : Poly (gate degree) := by
  have js : Poly (fun q : ReplyInput => q.2.1.1) := by fun_prop
  have emptyStore := (js.pair (Code.Poly.const ([] : Bits.Word))).pair (Code.Poly.const ([] : List Tally))
  let bounds (q : ReplyInput) := fits (tally degree,ruler q.2.1.1)
  let space (q : ReplyInput) := fits (q.1.1,Meter.count stored ((q.2.1.1,[]),[]))
  let shorter (q : ReplyInput) := fits (ruler q.1.2,ruler q.2.1.2)
  have p : Poly bounds := ((Code.Poly.const _).pair (js.compose (Easy.ruler Easy.identity).poly)).compose fits_poly
  have s : Poly space := ((Easy.fst.compose Easy.fst).poly.pair (emptyStore.compose (Meter.program stored))).compose fits_poly
  have n : Poly shorter :=
    (((Easy.ruler (Easy.fst.compose Easy.snd)).pair (Easy.ruler ((Easy.snd.compose Easy.fst).compose Easy.snd))).poly).compose fits_poly
  have result := Poly.choose p (Poly.choose s (Poly.choose n (Easy.snd.compose Easy.some).poly (Code.Poly.const none))
    (Code.Poly.const none)) (Code.Poly.const none)
  convert result using 1
  funext q
  unfold gate SafeReply
  dsimp only [bounds,space,shorter,replySize]
  simp only [Bool.cond_eq_ite,fits_iff,Meter.length,tally_length,ruler_length]
  by_cases h₁ : q.2.1.1.length ≤ degree
    <;> by_cases h₂ : size (((q.2.1.1,([] : Bits.Word)),([] : List Tally)) : Store) ≤ q.1.1.length
    <;> by_cases h₃ : q.2.1.2.length ≤ q.1.2.length
    <;> simp [h₁,h₃] at *

def boundedVisit (degree : ℕ) (room : D → Tally) (visit : Visit D) : Visit D := fun q =>
  (visit q).bind fun a => gate degree ((room q.1.1,q.2),a)

open private bind_poly from OAI.Computability.MultitapeWeakETH.TerminalProgram

theorem boundedVisit_poly [Codec D] (degree : ℕ) {room : D → Tally} {visit : Visit D} (hr : Poly room) (hv : Poly visit) :
    Poly (boundedVisit degree room visit) := by
  let X := ((D × Job) × Bits.Word) × Answer
  have ctx : Poly (fun q : X => q.1.1.1) := by dsimp only [X]; fun_prop
  have arg := (((ctx.compose hr).pair (Easy.fst.compose Easy.snd).poly).pair Easy.snd.poly).compose (gate_poly degree)
  exact bind_poly default hv arg

theorem boundedVisit_iff (degree : ℕ) (room : D → Tally) (visit : Visit D) (ctx : D) (j : Job) (bits : Bits.Word) (a : Answer) :
    boundedVisit degree room visit ((ctx,j),bits) = some a ↔
      visit ((ctx,j),bits) = some a ∧ SafeReply degree (room ctx).length bits a := by
  unfold boundedVisit gate
  cases h : visit ((ctx,j),bits) with
  | none => simp
  | some v =>
    simp only [Option.bind_some,Option.some.injEq]
    split_ifs with ok <;> grind

/-- Every guarded success has enough potential to pay for all child visits,
even on an invalid site number or malformed input packet. -/
theorem bounded_descent (degree : ℕ) (room : D → Tally) (visit : Visit D) (ctx : D)
    (lower : ∀ j bits a, visit ((ctx,j),bits) = some a → ∀ child ∈ a.1.1, child.1.1.length < j.1.1.length) :
    Descent (boundedVisit degree room visit) ctx (fun j => size j ≤ (room ctx).length)
      (fun j => (degree+1)^j.1.1.length) := by
  intro j _ bits children next names hit
  obtain ⟨raw,hc,hs,small⟩ := (boundedVisit_iff degree room visit ctx j bits _).mp hit
  refine ⟨?_,layer_weight children hc (lower j bits _ raw),small⟩
  intro c member
  have fits := sublist_size (List.singleton_sublist.mpr member)
  change size (((children,([] : Bits.Word)),([] : List Tally)) : Store) ≤ _ at hs
  simp only [size_prod,size_cons] at fits hs ⊢
  omega

end OAI.Computability.MultitapeWeakETH.WitnessWalk
