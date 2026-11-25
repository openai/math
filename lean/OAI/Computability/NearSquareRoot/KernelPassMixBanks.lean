import OAI.Computability.NearSquareRoot.KernelPassMixBankLayout
import OAI.Computability.NearSquareRoot.ShortWordCall
import OAI.Computability.NearSquareRoot.BoundedProgram
import OAI.Computability.IntegerMultiplication.Code.Dup

/-! # Physical lifting of fixed record maps to full row banks

A single copy of the width ruler and a unary address count are supplied. The
program copies the ruler once per address, gathers equal-address records,
runs the record map on that address, and then scatters the output rows.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPassMixBanks

open IntegerMultiplication.Code NearSquareRoot.MixBankLayout

variable {X Y J : Type} {α : J → Type} [Codec X] [Codec Y]

private def finish (i o : ℕ) (d : X) (e : Y) (mix : Tally × List X → List Y)
    (p : List Tally × List (List X)) : List (List Y) :=
  scatter o e ((zipFair [] [] (p.1, align i d (ruler p.1, p.2))).map mix)

private theorem easy_finish (i o : ℕ) (d : X) (e : Y) (mix : Tally × List X → List Y)
    (hm : Easy mix) : Easy (finish i o d e mix) := by
  have gather := ((Easy.ruler (Easy.fst : Easy (Prod.fst (α := List Tally)
    (β := List (List X))))).pair Easy.snd).compose (easy_align i d)
  exact ((((Easy.fst.pair gather).compose (easy_zip ([] : Tally) ([] : List X))).compose
    hm.mapping).compose (easy_scatter o e))

omit [Codec X] [Codec Y] in
private theorem finish_eq {A : Type} {i o : ℕ} (d : X) (e : Y) (mix : Tally × List X → List Y)
    (r : Tally) (l : List A) (x : A → Fin i → X) (y : A → Fin o → Y)
    (hm : ∀ a ∈ l, mix (r, List.ofFn (x a)) = List.ofFn (y a)) :
    finish i o d e mix (List.replicate l.length r, bank l x) = bank l y := by
  have hr : ruler (List.replicate l.length r) = tally l.length := by
    simp [ruler,tally]
  unfold finish
  dsimp only
  rw [hr, align_bank, ← List.map_const' (b := r) (l := l), fair, List.map_map]
  rw [← scatter_columns e l y]
  exact congrArg _ (List.map_congr_left (fun a ha => hm a ha))

private theorem size_replicate {Z : Type} [Codec Z] (n : ℕ) (a : Z) :
    size (List.replicate n a) = n * (size a + 1) + 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, size_cons, ih]; ring

/-- Preserve the left input header around a program that consumes it.
Only that header crosses the auxiliary tapes. -/
theorem preserveHeader {I : Type*} (header body reply : I → Tree) (budget : I → ℕ)
    (run : Task budget (fun t => .fork (header t) (body t)) reply) :
    Task (fun t => (header t).count + budget t) (fun t => .fork (header t) (body t))
      (fun t => .fork (header t) (reply t)) := by
  have dup : Task (fun t => (header t).count) (fun t => .fork (header t) (body t))
      (fun t => .fork (header t) (.fork (header t) (body t))) := by
    refine ⟨splitRoot 0 (fun _ => .pass)
      ((clone 0 1 2).join ((pack 0).join ((move 1 0 2).join (pack 0)))),
      100, fun t env r => ?_⟩
    let h := header t
    let b := body t
    have copy := fits_clone (i := 0) (j := 1) (u := 2) (by decide) (by decide)
      (by decide) h env (pile 0 b r)
    rw [pile_comm 1 _ r 0 b (by decide)] at copy
    have packBody := fits_pack h b (pile 1 h r) 0 env
    have back := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide)
      h env (pile 0 (.fork h b) r)
    rw [pile_comm 1 _ r 0 _ (by decide)] at back
    exact (fits_pair (copy.join (packBody.join (back.join (fits_pack h (.fork h b) r 0 env))))).mono
      (by dsimp only [h]; omega)
  exact (dup.compose (run.right header)).bound 2 (fun _ => by omega)

variable {i o : ℕ} (d : X) (e : Y) (mix : Tally × List X → List Y)
    (he : Easy mix) (l : (t : J) → List (α t)) (w : J → ℕ)
    (x : (t : J) → α t → Fin i → X) (y : (t : J) → α t → Fin o → Y)
    (B : ℕ) (hx : ∀ t, ∀ a ∈ l t, ∀ j, size (x t a j) ≤ B * (w t + 1))
    (hm : ∀ t, ∀ a ∈ l t, mix (tally (w t + 1), List.ofFn (x t a)) = List.ofFn (y t a))

include d e he hx hm

/-- One P192 command for all widths and address counts. A fixed-sized matrix
can mix any number of addresses with cost linear in their bit volume. -/
theorem mixBanks :
    Task (fun t => ((l t).length + 1) * (w t + 1))
      (fun t => send ((tally (l t).length, tally (w t + 1)), bank (l t) (x t)))
      (fun t => send (bank (l t) (y t))) := by
  let rulers (t : J) := List.replicate (l t).length (tally (w t + 1))
  have gen := (generate (X := Tally)).on fun t => (tally (l t).length, tally (w t + 1))
  simp only [tally_length] at gen
  have h₁ := gen.left fun t => send (bank (l t) (x t))
  have h₂ := (easy_finish i o d e mix he).on fun t => (rulers t, bank (l t) (x t))
  have hs := h₁.compose h₂
  have out (t : J) : finish i o d e mix (rulers t, bank (l t) (x t)) = bank (l t) (y t) :=
    finish_eq d e mix _ (l t) _ _ (hm t)
  simp only [out] at hs
  apply hs.bound (i * (B + 3) + 12)
  intro t
  simp only [rulers, size_prod, size_replicate, size_tally, tally_length]
  have bound := size_bank_le (l t) (x t) _ (hx t)
  ring_nf at bound ⊢
  omega

/-- Grammar packets keep both the address-count and the word-width rulers
through composition of successive mixers. -/
theorem mixBanks_header :
    Task (fun t => ((l t).length + 1) * (w t + 1))
      (fun t => send ((tally (l t).length, tally (w t + 1)), bank (l t) (x t)))
      (fun t => send ((tally (l t).length, tally (w t + 1)), bank (l t) (y t))) := by
  let header (t : J) := send (tally (l t).length, tally (w t + 1))
  have h := preserveHeader header _ _ _ (mixBanks d e mix he l w x y B hx hm)
  apply h.bound 8
  intro t
  change size (tally (l t).length, tally (w t + 1)) + _ + 1 ≤ _
  simp only [size_prod, size_tally, tally_length]
  ring_nf
  omega

/-- Both live data and return-stack depth of a grammar mixer fit in the
encoded bank volume, over and above the caller's parked data. -/
theorem bounded_mixBanks_header :
    Space.BoundedTask (fun t => ((l t).length + 1) * (w t + 1))
      (fun t => ((l t).length + 1) * (w t + 1))
      (fun t => send ((tally (l t).length, tally (w t + 1)), bank (l t) (x t)))
      (fun t => send ((tally (l t).length, tally (w t + 1)), bank (l t) (y t))) := by
  have r := mixBanks_header d e mix he l w x y B hx hm
  apply (Space.BoundedTask.of_time r).bound 1 (i * (B + 3) + 10)
  · intro t
    simp
  · intro t
    change size ((tally (l t).length, tally (w t + 1)), bank (l t) (x t)) + _ + 1 ≤ _
    simp only [size_prod, size_tally, tally_length]
    have bound := size_bank_le (l t) (x t) _ (hx t)
    ring_nf at bound ⊢
    omega

/-- Every operation from ruler replication through the inverse layout scan
executes on the fixed-tape machine, with auxiliary tapes restored on return. -/
theorem physical_mixBanks :
    ShortWord.PhysicalTask (fun t => ((l t).length + 1) * (w t + 1))
      (fun t => send ((tally (l t).length, tally (w t + 1)), bank (l t) (x t)))
      (fun t => send (bank (l t) (y t))) :=
  ShortWord.physicalTask (mixBanks d e mix he l w x y B hx hm)

end KernelPassMixBanks

end NearSquareRoot
end Computability
end OAI
