import OAI.Computability.VPVNP.PairSimulationMapResidentAgreement
import OAI.Computability.VPVNP.PairSimulationAnchorDecode

/-!
# Executing the grouped motif's selector phase in private memory

Agreement across all incident fields leads directly to the decoder of the
anchor field. A disagreement or an unused code reaches the same failure
label. Each successful copy writes its selector ordinal at its own index.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapSelectors

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord MotifEntry
open MotifSelector (Supply Half mapHalf)
open MapPortAgreement MapResidentAgreement
open scoped Fin.CommRing

variable {X J E : Type*} [DecidableEq J] [Fintype E] {G : Supply J E} {party : J}
variable {w p r k u b : ℕ} {v : E → ℕ}

/-- The decoder's six incoming registers survive the directory walk.
Scratch registers may be shared between the fragments. -/
structure Program (X : Type*) (p r k : ℕ) where
  /-- The fixed selector-code table and ordinal output loop. -/
  decoder : AnchorDecode.Program X p r k
  /-- The outer port-directory control labels. -/
  scan : Fin 7 → Fin p
  /-- The selector-bit comparison control labels. -/
  inner : Fin 7 → Fin p
  /-- The port-directory register allocation. -/
  reg : Fin 11 ↪ Fin r
  saved : ∀ i : Fin 9, i ≠ 0 → i ≠ 2 → i ≠ 5 → MapPortScan.Preserved reg (decoder.reg i)

namespace Program

variable (P : Program X p r k)

/-- Both failure paths use the decoder's bad label. -/
structure Linked (M : Machine w p r k) : Prop where
  scan : MapPortScan.Linked M P.scan P.inner P.reg (P.decoder.pc 0) P.decoder.bad
  decoder : P.decoder.Linked M

/-- Entry data for a complete selector invocation. The anchor base is the
base of its resident port. The decoder starts with its two high cursors. -/
structure Ready (order : Fin (Fintype.card E) ≃ E)
    (x : Half G (fun e ↦ Fin (v e + u * b) → Bool) party) (base : Port G party → Word w)
    (dir : Word w) (dest : ℕ) (c : Config w p r) : Prop where
  pc : c.pc = P.scan 0
  directory : c.reg (P.reg 7) = dir
  endDir : c.reg (P.reg 8) = dir + ((ports G party order).length : Word w)
  anchor : c.reg (P.reg 9) = selectorStart v base (anchorPort G party)
  width : c.reg (P.reg 10) = ((u * b : ℕ) : Word w)
  one : c.reg (P.reg 3) = 1
  zero : c.reg (P.reg 4) = 0
  resident : Resident order x base c.privateMem dir
  dataEnd : c.reg (P.decoder.reg 3) = base (anchorPort G party) +
    ((v (edge (anchorPort G party)) + u * b : ℕ) : Word w)
  cursor : c.reg (P.decoder.reg 1) = c.reg (P.decoder.reg 3)
  decoderOne : c.reg (P.decoder.reg 4) = 1
  output : c.reg (P.decoder.reg 6) = ((dest + u : ℕ) : Word w)
  stop : c.reg (P.decoder.reg 7) = (dest : Word w)
  codeWidth : c.reg (P.decoder.reg 8) = (b : Word w)

/-- Registers needed by a continuation and private cells outside the ordinal
destination interval survive both phases. -/
structure Frame (dest u : ℕ) (c d : Config w p r) : Prop where
  regs : ∀ a, MapPortScan.Preserved P.reg a → a ≠ P.decoder.reg 0 → a ≠ P.decoder.reg 1 →
    a ≠ P.decoder.reg 2 → a ≠ P.decoder.reg 5 → a ≠ P.decoder.reg 6 → d.reg a = c.reg a
  memory : ∀ a : Word w, a.val < dest ∨ dest + u ≤ a.val → d.privateMem a = c.privateMem a
  persistent : d.persistent = c.persistent

/-- Native result of the full selector phase, including ordinals on success
and the genuine failure exit on every syntactic zero. -/
structure Runs (M : Machine w p r k) (result : Option (Fin u → X)) (cap dest : ℕ)
    (c : Config w p r) : Prop where
  path : ∃ ticks d, ticks ≤ cap ∧ Prefix M c (List.replicate ticks .tick) d ∧ Frame P dest u c d ∧
    match result with
    | none => d.pc = P.decoder.bad
    | some θ => d.pc = P.decoder.done ∧ ∀ i : Fin u,
        d.privateMem ((dest + i.val : ℕ) : Word w) = M.publicData (P.decoder.name (θ i))

variable {P} {M : Machine w p r k}

omit [DecidableEq J] [Fintype E] in
/-- The selector scan rejects inconsistent or unused tags on every external
memory, branch tape and instruction budget when its bad exit is a reject. -/
theorem Runs.rejects {cap dest : ℕ} {c : Config w p r} (hr : Runs (u := u) P M none cap dest c)
    (hb : M.code P.decoder.bad = .reject) (fuel : ℕ) (mem : Memory w) (bits : List Bool) :
    execute M.program fuel c mem bits = none := by
  obtain ⟨_, _, _, pre, _, hpc⟩ := hr.path
  exact MapLookup.reject_after_ticks pre (fun _ h ↦ List.eq_of_mem_replicate h)
    (hpc ▸ hb) fuel mem bits

/-- The native selector phase realizes the value of the metered motif
interpreter on its actual resident half-wires. Its pathwise work bound also
holds for unmatched half-wires and all unused anchor selector codes. -/
theorem native (hl : P.Linked M) (order : Fin (Fintype.card E) ≃ E) (fits : b ≤ w)
    (code : X ↪ Word b) (keys : ∀ z, M.publicData (P.decoder.key z) = MapLookup.widen fits (code z))
    (x : Half G (fun e ↦ Fin (v e + u * b) → Bool) party) (base : Port G party → Word w)
    (dir : Word w) (dest : ℕ) (c : Config w p r) (ready : P.Ready order x base dir dest c)
    (hn : (ports G party order).length < 2 ^ w) (hlen : u * b < 2 ^ w)
    (hi : (base (anchorPort G party)).val + (v (edge (anchorPort G party)) + u * b) < 2 ^ w)
    (hd : dest + u < 2 ^ w)
    (sep : (base (anchorPort G party)).val + (v (edge (anchorPort G party)) + u * b) ≤ dest ∨
      dest + u ≤ (base (anchorPort G party)).val) :
    Runs P M (selectorRun G P.decoder.xs code v party x).1
      (((7 * (u * b) + 6) * (ports G party order).length + 3) + (P.decoder.visitCap b * u + 1))
      dest c := by
  let scanCost := (7 * (u * b) + 6) * (ports G party order).length + 3
  let t := anchorPort G party
  let tags := mapHalf G (fun _ ↦ readTag) x
  obtain ⟨mid, pre, hm, frame, hmem, hp⟩ := MapResidentAgreement.native hl.scan order x base dir c
    ready.pc ready.directory ready.endDir ready.anchor ready.width ready.one ready.zero
    ready.resident hn hlen
  change mid.pc = (if consistent G party tags then P.decoder.pc 0 else P.decoder.bad) at hm
  rw [selectorRun_value]
  change Runs P M (if consistent G party tags
    then selectors? P.decoder.xs code (anchor G party tags) else none) (scanCost + _) dest c
  by_cases hc : consistent G party tags = true
  · rw [ite_eq_left hc] at hm ⊢
    have keep (i : Fin 9) (h₀ : i ≠ 0) (h₂ : i ≠ 2) (h₅ : i ≠ 5) :
        mid.reg (P.decoder.reg i) = c.reg (P.decoder.reg i) :=
      frame _ (P.saved i h₀ h₂ h₅)
    have baseVal : ((base t).val : Word w) = base t :=
      Fin.ext (Nat.mod_eq_of_lt (base t).isLt)
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
    obtain ⟨ticks, d, cap, dec, f, res⟩ :=
      P.decoder.native hl.decoder fits code keys (field x t) (base t).val dest mid dat hi hd sep
    refine ⟨scanCost + ticks, d, Nat.add_le_add_left cap _, ?_, ?_, ?_⟩
    · rw [List.replicate_add]
      exact pre.append dec
    · exact ⟨fun a hs h₀ h₁ h₂ h₅ h₆ ↦ (f.regs a h₀ h₁ h₂ h₅ h₆).trans (frame a hs),
        fun a ha ↦ (f.memory a ha).trans (congrFun hmem a), f.persistent.trans hp⟩
    · rw [show anchor G party tags = readTag (field x t) from read_anchor x]
      cases hsel : selectors? P.decoder.xs code (readTag (field x t)) <;>
        rw [hsel] at res <;> exact res
  · rw [ite_eq_right hc] at hm ⊢
    exact ⟨scanCost, mid, Nat.le_add_right _ _, pre,
      ⟨fun a hs _ _ _ _ _ ↦ frame a hs, fun a _ ↦ congrFun hmem a, hp⟩,
      hm⟩

end Program
end PairSimulation.MapSelectors

end VPVNP
end Computability
end OAI
