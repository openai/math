import OAI.Computability.NearSquareRoot.PrecisionGridDigits
import OAI.Computability.IntegerMultiplication.Dusk.Nerve
import OAI.Computability.IntegerMultiplication.Strip.Breeze

/-!
# Passing a fixed-point record list to the physical CRT router

The router treats its payload as an array of bits in P192's `cloth` format.
Each row stores the real and imaginary components in their tape order.
A saved list of input records supplies the component boundary after routing.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace DigitPacking

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Dusk
open IntegerMultiplication.Strip IntegerMultiplication.Loom

noncomputable section

variable {X : Type} {A : X → Type} (s : (x : X) → Series (A x)) (w : X → ℕ)
variable (v : (x : X) → A x → Grain (w x))

/-- The addressed bit rows supplied to every record-preserving permutation. -/
abbrev recordCloth :=
  cloth s (fun x => Series.natural (2 * (w x + 1))) (fun x j => Dusk.stock (v x j))

private theorem recordCloth_eq :
    recordCloth s w v = fun x => send ((s x).tab (fun j => Dusk.tie (Dusk.mark (v x j)))) := by
  funext x
  unfold recordCloth cloth stackRun
  dsimp only
  simp only [stripe_eq', Dusk.stockera]

/-- Converting all rows from signed word pairs to the router's bit rows takes
one linear stack pass over the input packet. -/
theorem recordCloth_pack {R : X → ℝ} {src : X → Tree}
    (h : Carries R src (fun x => send ((s x).tab (Dusk.mark ∘ v x)))) :
    Carries R src (recordCloth s w v) := by
  let data x := (s x).tab (Dusk.mark ∘ v x)
  have g := h.chain (Carries.func (y := data) h.budget h.out _ Dusk.tie_easy.mapping)
  simpa only [data, Series.map_tab, Function.comp_def, recordCloth_eq] using g

/-- Unpack routed rows with the component widths of the saved input packet.
This applies for every target array of the same record type. -/
theorem recordCloth_unpack {R : X → ℝ} {src : X → Tree}
    (template : (x : X) → A x → Grain (w x))
    (h : Carries R src (fun x => send ((s x).tab (Dusk.mark ∘ template x))))
    (g : Carries R src (recordCloth s w v)) :
    Carries R src (fun x => send ((s x).tab (Dusk.mark ∘ v x))) := by
  simp only [recordCloth_eq] at g
  let data x := ((s x).tab (Dusk.mark ∘ template x), (s x).tab (fun j => Dusk.tie (Dusk.mark (v x j))))
  let restore (p : Dusk.Pair × Film) := Dusk.tore p.1 p.2
  have arg := h.twice g
  have prog := arg.chain (Carries.func (y := data) arg.budget arg.out _
    (easy_lock restore Dusk.tore_easy ([],[]) []))
  have correct x j : restore (Dusk.mark (template x j), Dusk.tie (Dusk.mark (v x j))) = Dusk.mark (v x j) :=
    Dusk.tied _ _ (by simp [Dusk.mark])
  simpa only [data, paired, Function.comp_def, correct] using prog

/-- A charged CRT stage on bit payloads transports the whole record stream.
The saved template and the conversion passes are included in its budget. -/
theorem route_records {r : Regime X} {n l : X → ℕ} {f : X → ℝ} {src : X → Tree}
    (target : (x : X) → A x → Grain (w x))
    (header : Breeze f r n l src r.header)
    (input : Breeze f r n l src (fun x => send ((s x).tab (Dusk.mark ∘ v x))))
    (route : Breeze f r n l (together r.header (recordCloth s w v))
      (recordCloth s w target)) :
    Breeze f r n l src (fun x => send ((s x).tab (Dusk.mark ∘ target x))) := by
  obtain ⟨hf, a, parse⟩ := input
  have packed : Breeze f r n l src (recordCloth s w v) :=
    ⟨hf, a, recordCloth_pack s w v parse⟩
  obtain ⟨_, b, routed⟩ := (header.pair packed).next route
  refine ⟨hf, a + b, recordCloth_unpack s w target v ?_ ?_⟩
  · exact parse.larger fun i => rate_higher i (hf i) (Nat.le_add_right a b)
  · exact routed.larger fun i => rate_higher i (hf i) (Nat.le_add_left b a)

end

end DigitPacking

end NearSquareRoot
end Computability
end OAI
