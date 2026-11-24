import OAI.Computability.VPVNP.PairShrinkCallFrameStores
import OAI.Computability.VPVNP.PairSimulationResidentMapLoopExact

/-!
# Retaining the vertex geometry through the resident map scan

The geometry array and cached verifier words lie after the histogram and
before the hidden scratch. The pointer at the live length lies below the
histogram. The exterior identity of each map therefore preserves the whole
vertex frame through the deterministic list of actions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open BurstRAM DFS NodeArguments LeafSourceLoad
open scoped Fin.CommRing

variable {w n : ℕ} {R : LeafArena.Regions} {data : Fin 10 → Word w}
  {offset : Word w} {vals : Static 34 → Word w}
local notation "G" => NativeFrame.frameBase R
local notation "hidden" => ShrinkCallABI.hiddenBase R n

/-- The exterior clause of a shrinking map preserves every word in the
tree decoder's vertex frame, including all cached verifier operands. -/
theorem VertexFrameData.after_map {saved out : Scratch w n}
    (h : VertexFrameData R data offset vals saved) {t : ℕ}
    (beforeHist : n < R.histBase) (labels : t ≤ R.histWords) (fits : hidden ≤ 2 ^ w)
    (exterior : ∀ q : Word w, q.val < hidden → (q.val < R.histBase ∨ R.histBase + t ≤ q.val) →
      rawScratch out q = rawScratch saved q) : VertexFrameData R data offset vals out := by
  have hist : R.histBase + t ≤ G := Nat.add_le_add_left labels _
  have cache : G ≤ R.cacheBase := R.hist_before
  have endCache : R.cacheBase + 38 ≤ hidden := Nat.le_add_right ..
  have atCell (q : ℕ) (lo : R.histBase + t ≤ q) (hi : q < hidden) :
      rawScratch out (q : Word w) = rawScratch saved (q : Word w) := by
    have val : (q : Word w).val = q := Nat.mod_eq_of_lt (hi.trans_le fits)
    exact exterior (q : Word w) (by rwa [val]) (.inr (by rwa [val]))
  apply h.transfer
  · have ptr : (n : Word w).val < R.histBase := (Nat.mod_le ..).trans_lt beforeHist
    apply exterior _ _ (.inl ptr)
    omega
  · intro j
    apply atCell _ (hist.trans (Nat.le_add_right ..))
    have := j.isLt
    omega
  · intro j
    have small : j.offset < 38 := by cases j <;> simp [Static.offset]; omega
    exact atCell _ ((hist.trans cache).trans (Nat.le_add_right ..))
      ((Nat.add_lt_add_left small _).trans_le endCache)

/-- Word-by-word transfer through the exact pure map scan. This induction
uses the actual scratch returned by the preceding occurrence. -/
theorem VertexFrameData.scan {t : ℕ} (actions : List (ResidentMapLoop.Exact.Action w n))
    (node : Word w) (saved : Scratch w n) (frame : VertexFrameData R data offset vals saved)
    (beforeHist : n < R.histBase) (labels : t ≤ R.histWords) (fits : hidden ≤ 2 ^ w)
    (exterior : ∀ act ∈ actions, ∀ initial events next, act node initial = some (events, next) →
      ∀ q : Word w, q.val < hidden → (q.val < R.histBase ∨ R.histBase + t ≤ q.val) →
        rawScratch next q = rawScratch initial q)
    {events : List (Event w)} {out : Scratch w n}
    (run : ResidentMapLoop.Exact.scan node actions saved = some (events, out)) :
    VertexFrameData R data offset vals out := by
  induction actions generalizing saved events out with
  | nil =>
    have eqn := (Prod.mk.inj (Option.some.inj run)).2
    exact eqn ▸ frame
  | cons act actions ih =>
    cases first : act node saved with
    | none => simp [ResidentMapLoop.Exact.scan, first] at run
    | some pair =>
      obtain ⟨es, mid⟩ := pair
      have step := frame.after_map beforeHist labels fits
        (exterior act List.mem_cons_self saved es mid first)
      cases rest : ResidentMapLoop.Exact.scan node actions mid with
      | none => simp [ResidentMapLoop.Exact.scan, first, rest] at run
      | some pair =>
        obtain ⟨tail, final⟩ := pair
        simp only [ResidentMapLoop.Exact.scan, first, rest, Option.some.injEq, Prod.mk.injEq] at run
        exact run.2 ▸ ih mid step (fun a ha ↦ exterior a (List.mem_cons_of_mem _ ha)) rest

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
