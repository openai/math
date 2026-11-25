import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSwapLiteral

/-! # Generating the actual elementary Walsh agenda from runtime parameters -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileElementaryAgenda
open IntegerMultiplication Code Staff Strip Carry PhysicalWalsh PhysicalWalshNode
open PhysicalWalshCompileSwapRulers GeneratorSyntax CommonRegisters

/-- Each entry is the binary encoding of the three mixed-radix spectator
ranges. The tape machine only expands the entry it currently executes. -/
def agenda (n : World → ℕ) (u : World) : List ElementarySchedule.Words :=
  List.ofFn fun j : Fin (n u) => ElementarySchedule.compact u.W u.src u.dst u.shape j.val

private theorem liftFig (n : World → ℕ) (q : Realizes regime n) {f : World → ℕ} (h : Figure regime f) :
    Figure (signal n q) (fun z : Across n => f z.1) := by
  obtain ⟨v,hv,ok⟩ := h
  exact ⟨_,sendRoof n q _ hv,fun z => ok z.1⟩

/-- One fixed program handles all arities, batch sizes, cutoffs and source
and destination slots. The cutoff is selected independently of the data. -/
theorem generated (n : World → ℕ) (q : Realizes regime n) : regime.Has (agenda n) := by
  apply harvest n q
  let a := arity.minused (Realizes.fix 1)
  let lo := minRealizes (a.minused src) (a.minused dst)
  let hi := maxRealizes (a.minused src) (a.minused dst)
  let r := signal n q
  let b := landing n q _ slot
  let step := floor_ n q
  let l := ((landing n q _ lo).times b).plus step
  let h := ((landing n q _ hi).times b).plus step
  let rem := ((landing n q _ arity).times b).minused (h.plus (Realizes.fix 1))
  let gap := h.minused (l.plus (Realizes.fix 1))
  let pow (v : Across n → ℕ) (pr : Realizes r v) := (Figure.natural 2).repeated pr
  let p := (liftFig n q group).multiplied (pow _ rem)
  let g := pow _ gap
  let tail := (pow _ l).multiplied (liftFig n q suff)
  exact (Header.toBinary p).pair ((Header.toBinary g).pair (Header.toBinary tail))

def steps (trim : Bool) (u : World) := if trim then SlotSwap.reserve u.depth (u.a+1) u.shape else
  ElementarySchedule.slotWidth (u.a+1) u.shape

theorem steps_realizes (trim : Bool) : Realizes regime (steps trim) := by
  cases trim
  · exact slot
  · exact reserve

theorem steps_le (trim : Bool) (u : World) : steps trim u ≤ ElementarySchedule.slotWidth (u.a+1) u.shape := by
  cases trim
  · exact le_rfl
  · exact min_le_left ..

/-- Actual emitted command and compact length bounds for either all bits or
the low reserve slice. Both degrees are uniform over every runtime parameter. -/
theorem compiled (trim : Bool) :
    ∃ (R d e : ℕ) (c : Control → Cmd), 1 ≤ d ∧ Effective ltr c ∧ (∀ k,Within R (c k)) ∧
      Configured (agenda (steps trim)) (fun _ => 0) d c ∧
      ∀ (a W : ℕ) (i j : Fin (a+1)) (D : ℕ), ∃ C : ℕ, ∀ s : Shape,
        let u : World := ⟨a,W,i,j,D,s⟩
        size (agenda (steps trim) u) ≤ C*(Header.scale (a+1) s+1)^e := by
  have h := generated _ (steps_realizes trim)
  obtain ⟨R,d,c,hd,eff,within,run⟩ := configured h
  obtain ⟨e,sz⟩ := compact_size h
  exact ⟨R,d,e,c,hd,eff,within,run,sz⟩

end PhysicalWalshCompileElementaryAgenda

end NearSquareRoot
end Computability
end OAI
