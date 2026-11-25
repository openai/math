import OAI.Computability.BorderVNP.DiagonalJointAcceptedTerms
import OAI.Computability.BorderVNP.DiagonalNativeTimedModes

/-! # Joint signed preparations on the full physical shared exterior -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM UniversalMachine RoutingISA RoutingISA.Evaluator CompactMachine CellMacro.Generator BorderVNP.Cube
open scoped Classical BigOperators

variable {R r t d link inner n w : ℕ} {Edge : Type}

/-- Every processor selected the positive branch and passed its true
prefix comparison on this shared exterior assignment. -/
def PositiveExterior (G : Wiring R r t d link inner n Edge) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool) (w : ℕ) (ext : Exterior R r link → Bool) : Prop :=
  ∀ u, modeTag (w:=w) G args pin ext u ≠ 0 ∧
    (G.transferFrame u (args u).header (args u).dst).Agrees (readings (modeMemory (w:=w) G args pin ext u))

/-- A shared assignment that fails even one real startup comparison has
zero contribution to the positive mode. -/
theorem positive_mask_reject (physical : Program) {a e : ℕ} (eval : Code) (mac : TeamOpcode.Macros w 8)
    (data : SiteData R r 64 32 w a) (pack : Fin (R+1) → ReferencePacket w d)
    (fit : fitsWith physical 64 32 r w a R link n e) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool) (he : eval.withoutAccept = true) :
    let G := wiringWith physical (withStartup eval).program (data.withPacket pack) d link n e fit
    (∀ u, (args u).Fitted G u (pack u) (data.publicWords u) (adviceOffsetWith physical r 32 64 w n)) →
    (∀ u, packetUnitBudget (args u).advice.count w (G.transferFrame u (args u).header (args u).dst)
      (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase) ≤ data.limit.val) →
    ∀ ext, ¬ PositiveExterior G args pin w ext → (∏ u, positiveMaskedNativeValue G eval mac data.publicWords
      data.registers args pin data.limit.val data.burst.val (n^25) ext u) = 0 := by
  intro G ready time ext bad
  by_contra h
  apply bad
  intro u
  have nz : positiveMaskedNativeValue G eval mac data.publicWords data.registers args pin data.limit.val
      data.burst.val (n^25) ext u ≠ 0 := fun hz => h (Finset.prod_eq_zero (Finset.mem_univ u) hz)
  have tag : modeTag (w:=w) G args pin ext u ≠ 0 := fun z => nz (ite_eq_left z)
  refine ⟨tag,packetNative_guarded physical eval mac data pack fit args pin ext u he (ready u) (time u) ?_⟩
  simpa only [positiveMaskedNativeValue,ite_eq_right tag] using nz

variable {dim box lanes selectors symbols : ℕ} {id : TableEntry dim box lanes selectors symbols → ℕ} {gen : Fragment IO}

/-- An accepting positive path across the entire wired instance. Its exterior
is shared, its team prefixes include the genuine local pin guesses, and its
private cell guesses occur once for each physically owned cell. -/
abbrev AcceptedExterior {X : Type*} (S : X → Fin (R+1) → PositiveTeam id gen n w)
    (joint : ∀ x (a : (u : Fin (R+1)) → (S x u).Prefix), JoinedCells (fun u => (S x u).pub)
      (fun u => (S x u).postMemory) (fun u => (S x u).generated) a) :=
  (x : X) × {a : PositiveAssignment (S x) (joint x) // positivePass (S x) (joint x) a}

/-- Sum over all actual shared wires, followed by all successful private
preparations and passing cells. A mathematically zero residue entry stays
in the accepted domain. The local post-boot state and its cutoff are supplied
by the physical startup execution. -/
theorem sum_accepted_exteriors (G : Wiring R r t d link inner n Edge) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool) (eval : Code) (mac : TeamOpcode.Macros w 8) (pub : Fin (R+1) → Arg → Word w)
    (reg : Fin (R+1) → Bank w) (limit burst : ℕ) (hn : 1 ≤ n)
    {supported : (Exterior R r link → Bool) → Prop}
    (S : {ext : Exterior R r link → Bool // supported ext} →
      Fin (R+1) → PositiveTeam id gen n w)
    (joint : ∀ x (a : (u : Fin (R+1)) → (S x u).Prefix), JoinedCells (fun u => (S x u).pub)
      (fun u => (S x u).postMemory) (fun u => (S x u).generated) a)
    (reject : ∀ ext, ¬ supported ext →
      (∏ u, positiveMaskedNativeValue G eval mac pub reg args pin limit burst (n^25) ext u) = 0)
    (boot : ∀ x u, positiveMaskedNativeValue G eval mac pub reg args pin limit burst (n^25) x.val u =
      boundedValue (signedBody id) (S x u).pub (install gen n (S x u).routines) (S x u).bank (S x u).memory
        ((S x u).limit-(S x u).used) (S x u).burst (n^25)) :
    (∑ ext, ∏ u, positiveMaskedNativeValue G eval mac pub reg args pin limit burst (n^25) ext u) =
      ∑ a : AcceptedExterior S joint, positiveWeight (S a.1) (joint a.1) a.2.val := by
  let f := fun ext => ∏ u, positiveMaskedNativeValue G eval mac pub reg args pin limit burst (n^25) ext u
  have split := Fintype.sum_subtype_add_sum_subtype (supported) f
  have zero (a : {ext : Exterior R r link → Bool // ¬ supported ext}) : f a.val = 0 :=
    reject a.val a.property
  simp only [zero, Finset.sum_const_zero,add_zero] at split
  refine split.symm.trans ?_
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x _
  refine (Finset.prod_congr rfl fun u _ => boot x u).trans ?_
  exact joint_accepted_sum (S x) (joint x) hn

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
