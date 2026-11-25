import OAI.Computability.NearSquareRoot.InterchangeTable
import OAI.Computability.IntegerMultiplication.Strip.Narrow
import OAI.Computability.IntegerMultiplication.Loom.Fare

/-!
# Seeding constant rows of packed symbols

A unary width in the header determines one packed record. The outer record
count supplied by the station determines how often that record is copied.
Both the construction and all copies are charged to the stack program.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePayload

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom

variable {I B : Type} {P D : I → Type} {N l : I → ℕ} {r : Regime I}
variable (records : (i : I) → Series (P i)) (payload : (i : I) → Series (D i))
    (station : Station r records) (hN : ∀ i, (records i).count ≤ N i)
    (hwidth : ∀ i, (payload i).count ≤ l i)
    (widthReady : Rip r N l r.header (fun i => send (tally (payload i).count)))

include station hN hwidth widthReady in
private theorem constantRow (symbol : Tree) :
    Rip r N l r.header
      (stackRun records fun i _ => stripe (payload i) fun _ => symbol) := by
  have hn (i : I) : 1 ≤ N i := (station.1 i).trans (hN i)
  let row (i : I) := stripe (payload i) fun _ => symbol
  obtain ⟨u,hu⟩ := widthReady
  have blank : Rip r N l r.header (stackRun payload fun _ _ => Tree.atom false) :=
    ⟨u, seeds payload hu⟩
  have table := interchange_record_table (F := Unit) payload (fun _ _ => ())
    (fun _ => Tree.atom false) (fun _ => symbol) (fun _ _ _ => Subsingleton.elim ..)
  have make : Rip r N l r.header row := blank.chain ⟨0, table.larger fun i => by
    simp only [mass, pow_zero]
    calc
      ((payload i).count : ℝ) + 1 ≤ (l i : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right (hwidth i) 1
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (by exact_mod_cast hn i)⟩
  obtain ⟨k, prep⟩ := (station.supply hN).twice make
  apply Exists.intro k
  apply spread records row prep
  refine ⟨2 * (symbol.count + 2), fun i => ?_⟩
  have size := stripe_size (payload i) (fun _ => symbol) symbol.count (fun _ => le_rfl)
  have hs : ((row i).count : ℝ) ≤ (symbol.count + 2 : ℝ) * ((l i : ℝ) + 1) := by
    exact_mod_cast (show (row i).count ≤ (symbol.count+2)*(l i+1) from
      size.trans <| (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hwidth i)) _).trans (by nlinarith))
  have hrec : ((records i).count + 1 : ℝ) ≤ 2 * (N i : ℝ) := by
    exact_mod_cast (show (records i).count + 1 ≤ 2*N i by have := hn i; have := hN i; omega)
  have hmass : (N i : ℝ)*((l i : ℝ)+1) ≤ mass r N l k i := by
    simpa [mass] using mass_le (r:=r) (n:=N) (l:=l) (Nat.zero_le k) i
  calc
    _ ≤ (2 * (N i : ℝ)) * ((symbol.count + 2 : ℝ) * ((l i : ℝ) + 1)) :=
      mul_le_mul hrec hs (by positivity) (by positivity)
    _ = ↑(2 * (symbol.count+2)) * ((N i : ℝ)*((l i : ℝ)+1)) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

include station hN hwidth widthReady in
/-- Produce one full zero-symbol record at each outer address. -/
theorem seed : Rip r N l r.header
    (stackRun records fun i _ => stripe (payload i) fun _ => Tree.atom false) :=
  constantRow records payload station hN hwidth widthReady (.atom false)

include station hN hwidth widthReady in
/-- Emit a fixed bank of output rows from the header and an arbitrary live
source. This covers tables with an empty input row family. -/
theorem constantRows (out : Series B) (dst : B → Tree) (source : I → Tree)
    (alive : Alive r N l source) :
    Drive r N l source (fun i => stripe out fun b =>
      stripe (records i) fun _ => stripe (payload i) fun _ => dst b) := by
  have hn (i : I) : 1 ≤ N i := (station.1 i).trans (hN i)
  apply Fatigue.dry out _ (Rip.alivePair (Drive.started hn) alive)
  intro b
  exact (Drive.fetch hn alive).chain (constantRow records payload station hN hwidth widthReady (dst b))

end InterchangePayload

end NearSquareRoot
end Computability
end OAI
