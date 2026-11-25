import OAI.Computability.NearSquareRoot.PhysicalWalshNodeRate
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileEntry

/-! # Keeping the recursive command on a descendant-closed family of shapes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.Node

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode KernelPass

variable {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)
  (scan arena : Shape → ℕ) (cost : ∀ s, arena s ≤ scan s)

/-- The same command executes every occupied root that fits the outer word width.
Its time recurrence charges exactly the number of child calls in its template. -/
def NamedTrace (cmd : Cmd) : Prop :=
  let d := (spec hw p scan arena cost).restrict (withinWidth (a+1))
  ∃ C : ℕ, ∀ T S, d.Recurrence p.calls C T S →
    ∀ x env park b, DeckCap b park →
      BoundedFits env cmd (pile 0 (d.query x) park) (pile 0 (d.reply x) park)
        (T (d.world x)) (b + S (d.world x)) (S (d.world x))

/-- The emitted base and successor execute on occupied shapes at every
lexical child jump. -/
theorem namedTrace (base step : Cmd)
    (one : let d := spec hw p scan arena cost
      ClosedRuns base (fun x : d.Base => scan x.val.shape) (fun x => arena x.val.shape)
        (fun x => d.payload x.val) (fun x => d.reply x.val))
    (next : let d := spec hw p scan arena cost
      Runs step d.meter p.calls (fun x : d.Step => x.val.shape) (fun x => d.payload x.val)
        (fun x => d.reply x.val)) :
    NamedTrace hw p scan arena cost (.tie (decodeBit base step)) := by
  let vm := spec hw p scan arena cost
  let d := vm.restrict (withinWidth (a+1))
  apply d.tieNamed base step
  · exact one.on (fun x : d.Base => (⟨x.val.val,x.property⟩ : vm.Base))
  · obtain ⟨C,run⟩ := next
    refine ⟨C,fun x env time space permit park b hp => ?_⟩
    apply run (⟨x.val.val,x.property⟩ : vm.Step) env time space _ park b hp
    intro y child
    exact permit ⟨y,withinWidth_child hw child x.val.property⟩ child

end PhysicalWalshCompile.Node

end NearSquareRoot
end Computability
end OAI
