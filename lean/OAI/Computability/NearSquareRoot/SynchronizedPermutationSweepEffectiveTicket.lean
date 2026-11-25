import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveRuler
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveSeed

/-! # Effective compilation of the full Beneš directory from a Fourier ticket -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer

open IntegerMultiplication Code FixedCandidate FixedPoint EffectiveBoundedTask DigitPacking FixedLayerTickets
open ShortFourier.BatchWord Benes.PackedBatchHeader

private def generateTicket {H : Type} (key : Tally × RowPass → H) (z : Tally × Ticket) :=
  PermDirectory.emitted (fun pass => key (z.1,pass)) (PermDirectory.ticketQuery z.2)

private theorem generateTicket_poly {H : Type} [Codec H] [Inhabited H]
    (key : Tally × RowPass → H) (hp : Poly key) : Poly (generateTicket key) := by
  let keep (z : Tally × Ticket) := (z.1,PermDirectory.ticketQuery z.2)
  have input : Poly keep := (Easy.fst (X := Tally) (Y := Ticket)).poly.pair
    ((Easy.snd (X := Tally) (Y := Ticket)).poly.compose PermDirectory.ticketQuery_easy.poly)
  let emit (z : Tally × PermDirectory.Query) := PermDirectory.emitted (fun pass => key (z.1,pass)) z.2
  have output : Poly emit := PermDirectory.emittedWith_poly key hp
  exact Poly.compose (f := keep) (g := emit) input output

private theorem generateTicket_render {H : Type} [Codec H] (key : Tally × RowPass → H)
    (D : Tally) (dir : Bool) (k s : ℕ) (hs : s < (directedPlan (dir,tally k)).length) :
    send (generateTicket key (D,phaseStageTicket k dir s hs)) =
      passDirectory (fun z => key (D,z)) dir k s := by
  change send (PermDirectory.emitted (fun z => key (D,z)) (dir,tally k,tally s)) = _
  rw [PermDirectory.emitted_eq,← Task.forest_send,Task.forest_map]
  rfl

/-- The generated command supplies its own reserve exponent to a fixed directory
compiler. Each candidate handles all ticket widths, directions and legal row indices
with linear time and workspace in the operand size. -/
theorem preparePermutationTicketFamily {P : Type} [Primcodable P] {I : P → Type}
    {H : Type} [Codec H] [Inhabited H] (key : Tally × RowPass → H) (program : Poly key)
    (D : P → ℕ) (eff : Computable D) (n : ∀ p, I p → ℕ) (hn : ∀ p i, 2 ≤ n p i)
    (dir : ∀ p, I p → Bool)
    (s : ∀ p (i : I p), Fin (directedPlan (dir p i,tally (addressBits (n p i)))).length) :
    let t p (i : I p) := phaseStageTicket (addressBits (n p i)) (dir p i) (s p i).val (s p i).isLt
    let d p (i : I p) := passDirectory (fun z => key (tally (D p),z)) (dir p i) (addressBits (n p i)) (s p i).val
    (∃ A : P → ℕ, ∀ p i, (d p i).count ≤ A p*(n p i+1)) ∧ Family n n (fun p i => send (t p i)) d := by
  intro t d
  have short (p : P) : Dom (fun i => addressBits (n p i)) (fun i => size (t p i)) :=
    by
      refine ⟨1,10000000000,?_⟩
      intro i
      simpa only [pow_one] using phaseStageTicket_size (addressBits (n p i)) (dir p i) (s p i).val (s p i).isLt
  have render (p : P) (i : I p) : send (generateTicket key (tally (D p),t p i)) = d p i :=
    generateTicket_render key (tally (D p)) (dir p i) _ _ (s p i).isLt
  obtain ⟨⟨A,cap⟩,run⟩ := prepareWithTally (generateTicket key) (generateTicket_poly key program)
    D eff n hn t short
  refine ⟨⟨A,fun p i => ?_⟩,?_⟩
  · rw [← render p i]
    exact cap p i
  · rw [← funext (fun p => funext (render p))]
    exact run

/-- Compile the two position tables and switch plan for each pass from its ticket. -/
theorem prepareFullPermutationTicketFamily {P : Type} [Primcodable P] {I : P → Type}
    (D : P → ℕ) (eff : Computable D) (n : ∀ p, I p → ℕ) (hn : ∀ p i, 2 ≤ n p i)
    (dir : ∀ p, I p → Bool)
    (s : ∀ p (i : I p), Fin (directedPlan (dir p i,tally (addressBits (n p i)))).length) :
    let t p (i : I p) := phaseStageTicket (addressBits (n p i)) (dir p i) (s p i).val (s p i).isLt
    let d p (i : I p) := passDirectory (fullHeader (D p)) (dir p i) (addressBits (n p i)) (s p i).val
    (∃ A : P → ℕ, ∀ p i, (d p i).count ≤ A p*(n p i+1)) ∧ Family n n (fun p i => send (t p i)) d := by
  simpa only [tally_length] using preparePermutationTicketFamily
    (fun z : Tally × RowPass => fullHeader z.1.length z.2) jointFullHeader_poly D eff n hn dir s

end FixedLayer

end NearSquareRoot
end Computability
end OAI
