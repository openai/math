import OAI.Computability.BorderVNP.DiagonalNativePackedProduct
import OAI.Computability.BorderVNP.DiagonalNativeBudgetValue
import OAI.Computability.BorderVNP.RoutingISATypedHistoryBounds
import OAI.Computability.BorderVNP.RoutingISANativeTags

/-! # Charged resource bounds of the signed evaluator's real phases -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.Within

variable {w : ℕ} {es fs : List (TeamRAM.Event w)} {t u b c : ℕ}

/-- Concatenating actual histories adds their tick allowances and preserves the maximum burst
and private-choice bounds. -/
theorem append (h : Within t b c es) (k : Within u b c fs) : Within (t+u) b c (es++fs) :=
  ⟨(VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add h.cost k.cost),
    fun e he => (List.mem_append.mp he).elim (h.length e) (k.length e),
    fun e he => (List.mem_append.mp he).elim (h.choices e) (k.choices e)⟩

/-- Enlarge any of the three chronological resource cutoffs. -/
theorem mono {t' b' c' : ℕ} (h : Within t b c es) (ht : t ≤ t') (hb : b ≤ b') (hc : c ≤ c') :
    Within t' b' c' es := ⟨h.cost.trans ht,fun e he => (h.length e he).trans hb,fun e he => (h.choices e he).trans hc⟩

end TeamContraction.Within

namespace RoutingISA

open VPVNP.BurstRAM TeamContraction
variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

private theorem ordinaryBounds {S : Type} {i : TeamRAM.Instr w S} {a bits vs t sign}
    (ordinary : DiagonalResidueRAM.ordinary i = true) (ha : i.action = some a)
    (hb : i.advance bits vs = some (t,sign)) : a.extra = 0 ∧ bits.length ≤ 1 := by
  cases i with
  | accept | reject | call => contradiction
  | localStep | choose | load | store =>
    cases ha
    refine ⟨rfl,?_⟩
    cases bits with
    | nil => decide
    | cons b xs =>
      cases xs with
      | nil => simp
      | cons x xs => cases vs <;> simp [TeamRAM.Instr.advance] at hb

/-- Native-only assembly can guess a single bit at each event. It never reads a private burst. -/
theorem Runs.nativeOnly_limits {c : Code} {s m es t mt} (run : Runs pub mac c s m es t mt)
    (h : c.nativeOnly = true) : Within (traceCost es) 0 1 es := by
  have all : ∀ e ∈ es, e.action.extra = 0 ∧ e.choices.length ≤ 1 := by
    have pre := DiagonalResidueRAM.at_last run
    have ord (s) : DiagonalResidueRAM.ordinary (c.program.fetch pub mac s) = true := by
      simp only [TeamOpcode.Program.fetch,c.program_tag_native h]
      split
      · cases ((c.program.base.code s.pc).resize w).runLogged pub s.logged <;> try rfl
        rename_i out
        cases out <;> rfl
      · rfl
    clear run
    generalize eq : (⟨0,s⟩ : TeamOpcode.State w (c.slots+1) 64) = first at pre
    generalize eq' : (⟨Fin.last c.slots,t⟩ : TeamOpcode.State w (c.slots+1) 64) = final at pre
    clear eq eq'
    induction pre with
    | nil => simp
    | cons ha step _ ih =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ordinaryBounds (ord _) ha step
      · exact ih _ he
  exact ⟨le_rfl,fun e he => (all e he).1.le,fun e he => (all e he).2⟩

end RoutingISA

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction CompactMachine CellDispatch CellMacro.Generator
open private scan_bounds from OAI.Computability.BorderVNP.RoutingISATypedHistoryBounds
open scoped BigOperators Classical
variable {w : ℕ}

/-- The actual cost of traversing the cell directory, with the real burst length in each owned row. -/
def privateDirectoryTicks (pub : Arg → Word w) (m : Memory w) : ℕ :=
  let f := Frame.ofMemory pub m
  let owned := f.ownedRows m 0 f.count
  17+7*f.count+4*owned.length+(owned.map fun j => (m (f.address j+2)).val).sum

/-- The real accepted private choices, including zero-returning ones, satisfy all three
paper bounds using the actual packed input words and inclusive native clock. -/
theorem GeneratedCells.within {gen : Fragment IO} {n : ℕ} {pub : Arg → Word w} {s : Bank w} {m : Memory w}
    (C : GeneratedCells gen n pub m) (routines : TeamOpcode.Macros w 8)
    (hf : (pub 0).val+15 < 2^w) (room : (Frame.ofMemory pub m).base+3*(Frame.ofMemory pub m).count ≤ 2^w)
    (z : Returns callOwnedCells pub (install gen n routines) s m) :
    Within (privateDirectoryTicks pub m) (TeamScales.width n (1/2)) (n^25) z.val.1 := by
  let f := Frame.ofMemory pub m
  have mem := (cellHistoriesEquiv pub (install gen n routines) s m (mem_choices gen n routines) hf room z).property
  obtain ⟨xs,hx,ev⟩ := Finset.mem_image.mp mem
  obtain ⟨len,ad⟩ := (Frame.mem_rowProducts (mem_choices gen n routines) ..).mp hx
  change setupTrace pub m ++ f.scanTrace m 0 xs = z.val.1 at ev
  rw [← ev]
  have cost := f.directory_charge pub m (install gen n routines) xs ad
  rw [len] at cost
  have head : ∀ e ∈ setupTrace pub m, e.action.extra ≤ TeamScales.width n (1/2) ∧ e.choices.length ≤ n^25 := by
    simp [setupTrace,tick,loadEvent,TeamTranscript.Action.extra]
  have tail := scan_bounds gen routines f m C.packed.cap 0 xs (by simpa only [Nat.zero_add] using len.le) ad
  have all := fun e (he : e ∈ setupTrace pub m ++ f.scanTrace m 0 xs) =>
    (List.mem_append.mp he).elim (head e) (tail e)
  exact ⟨cost.le,fun e he => (all e he).1,fun e he => (all e he).2⟩

/-- A cost and finite per-instruction spelling bound suffice for finite enumeration even if
other parts of the evaluator later reject. -/
theorem finiteReturns_of_within (c : Code) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (t b k : ℕ) (h : ∀ z : Returns c pub mac s m, Within t b k z.val.1) :
    Finite (Returns c pub mac s m) :=
  Finite.of_injective (fun z => (⟨z,h z⟩ : BoundedReturns c pub mac s m t b k)) (fun _ _ eq => Subtype.mk.inj eq)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
