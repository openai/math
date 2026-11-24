import OAI.Computability.VPVNP.PairSimulationMapSelectors
import OAI.Computability.VPVNP.PairSimulationAnchorClock

/-!
# Exact time for a successful map selector phase

The directory scan compares every incident tag with the anchor. The
decoder then visits the successful selector codes in descending copy
order. Together they give the instruction count for the complete phase.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapSelectors.Program

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord MotifEntry
open MotifSelector (Supply Half mapHalf)
open MapPortAgreement MapResidentAgreement
open scoped Fin.CommRing

variable {X J E : Type*} {w p r k u b : ℕ} (P : Program X p r k)

/-- Exact time to check all resident tags and write the selected ordinals. -/
def successTicks (code : X ↪ Word b) (θ : Fin u → X) (ports : ℕ) : ℕ :=
  (7 * (u * b) + 6) * ports + 3 + P.decoder.successTicks code θ

theorem successTicks_le (code : X ↪ Word b) (θ : Fin u → X) (ports : ℕ) :
    P.successTicks code θ ports ≤ (7 * (u * b) + 6) * ports + 3 + (P.decoder.visitCap b * u + 1) :=
  Nat.add_le_add_left (P.decoder.successTicks_le code θ) _

variable {P} [DecidableEq J] [Fintype E] {G : Supply J E} {party : J}
  {v : E → ℕ} {M : Machine w p r k}

/-- Every successful selector sequence gives the same exact clock for all
ready configurations and yields the selector names at their destination cells. -/
theorem native_success (hl : P.Linked M) (order : Fin (Fintype.card E) ≃ E) (fits : b ≤ w)
    (code : X ↪ Word b) (keys : ∀ z, M.publicData (P.decoder.key z) = MapLookup.widen fits (code z))
    (x : Half G (fun e ↦ Fin (v e + u * b) → Bool) party) (base : Port G party → Word w)
    (dir : Word w) (dest : ℕ) (c : Config w p r) (ready : P.Ready order x base dir dest c)
    (hn : (ports G party order).length < 2 ^ w) (hlen : u * b < 2 ^ w)
    (hi : (base (anchorPort G party)).val + (v (edge (anchorPort G party)) + u * b) < 2 ^ w)
    (hd : dest + u < 2 ^ w)
    (sep : (base (anchorPort G party)).val + (v (edge (anchorPort G party)) + u * b) ≤ dest ∨
      dest + u ≤ (base (anchorPort G party)).val)
    (θ : Fin u → X) (ok : (selectorRun G P.decoder.xs code v party x).1 = some θ) :
    ∃ d, Prefix M c (List.replicate (P.successTicks code θ (ports G party order).length) .tick) d ∧
      P.Frame dest u c d ∧ d.pc = P.decoder.done ∧
      ∀ i : Fin u, d.privateMem ((dest + i.val : ℕ) : Word w) = M.publicData (P.decoder.name (θ i)) := by
  let t := anchorPort G party
  let tags := mapHalf G (fun _ ↦ readTag) x
  rw [selectorRun_value] at ok
  change (if consistent G party tags then selectors? P.decoder.xs code (anchor G party tags)
    else none) = some θ at ok
  have agree : consistent G party tags = true := by
    by_contra h
    simp only [h, ↓reduceIte, reduceCtorEq] at ok
  have anchorOK : selectors? P.decoder.xs code (readTag (field x t)) = some θ := by
    simpa only [agree, ↓reduceIte, show anchor G party tags = readTag (field x t) from read_anchor x] using ok
  obtain ⟨mid, pre, hm, frame, hmem, hp⟩ := MapResidentAgreement.native hl.scan order x base dir c
    ready.pc ready.directory ready.endDir ready.anchor ready.width ready.one ready.zero ready.resident hn hlen
  change mid.pc = (if consistent G party tags then P.decoder.pc 0 else P.decoder.bad) at hm
  rw [ite_eq_left agree] at hm
  have keep (i : Fin 9) (h₀ : i ≠ 0) (h₂ : i ≠ 2) (h₅ : i ≠ 5) :
      mid.reg (P.decoder.reg i) = c.reg (P.decoder.reg i) := frame _ (P.saved i h₀ h₂ h₅)
  have baseVal : ((base t).val : Word w) = base t := Fin.ext (Nat.mod_eq_of_lt (base t).isLt)
  have dat : P.decoder.Ready (field x t) (base t).val dest u mid := by
    constructor
    · exact hm
    · rw [keep 1 (by decide) (by decide) (by decide), ready.cursor, ready.dataEnd]
      simp only [Nat.cast_add, Nat.mul_comm b u, baseVal, t]
    · rw [keep 3 (by decide) (by decide) (by decide), ready.dataEnd]
      simp only [Nat.cast_add, baseVal, t]
    · exact (keep 4 (by decide) (by decide) (by decide)).trans ready.decoderOne
    · exact (keep 6 (by decide) (by decide) (by decide)).trans ready.output
    · exact (keep 7 (by decide) (by decide) (by decide)).trans ready.stop
    · exact (keep 8 (by decide) (by decide) (by decide)).trans ready.codeWidth
    · intro i
      simpa only [hmem, Nat.cast_add, baseVal] using ready.resident.cells t i
  obtain ⟨d, dec, f, done, stored⟩ :=
    P.decoder.native_success hl.decoder fits code keys (field x t) (base t).val dest mid dat hi hd sep θ anchorOK
  refine ⟨d, ?_, ?_, done, stored⟩
  · rw [successTicks, List.replicate_add]
    exact pre.append dec
  · exact ⟨fun a hs h₀ h₁ h₂ h₅ h₆ ↦ (f.regs a h₀ h₁ h₂ h₅ h₆).trans (frame a hs),
      fun a ha ↦ (f.memory a ha).trans (congrFun hmem a), f.persistent.trans hp⟩

end PairSimulation.MapSelectors.Program

end VPVNP
end Computability
end OAI
