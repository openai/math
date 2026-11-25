import OAI.Computability.NearSquareRoot.PhysicalWalshNodeHeader
import OAI.Computability.IntegerMultiplication.Code.Iter

/-! # Parking the parent descriptor across a recursive Walsh call

The caller's enriched grid packet contains a singleton work row. The down
command emits the tagged child descriptor and that same row, with the parent's
entire header beneath them. The up command restores the singleton row bank
and its original header after the child returns.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.ChildAdapter

open IntegerMultiplication Code Space PhysicalWalsh

abbrev Parent := PhysicalWalshGrid.Header × Header.Wire

/-- The five unary bank parameters precede the compact parent descriptor. -/
def saved (a W : ℕ) (s : Shape) : Parent :=
  (PhysicalWalshGrid.header (coords a W) Shape.w s, Header.wire (a+1) s)

/-- Record bit volume plus one complete word for an empty intermediate list. -/
def volume (A : ℕ) (s : Shape) := (count A s+1)*(s.w + grow A s.level + 1)

private theorem header_size (a W : ℕ) (s : Shape) (pos : 0 < s.level) :
    size (saved a W s) ≤ 30*volume (a+1) s + Header.scale (a+1) s + 9 := by
  have h := Header.grid_size W a s pos
  have n : count (a+1) s + 1 ≤ volume (a+1) s := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have w : s.w + grow (a+1) s.level + 1 ≤ volume (a+1) s := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  change size (PhysicalWalshGrid.header (coords a W) Shape.w s) + Header.scale (a+1) s + 1 ≤ _
  omega

private def expose {R : Type} (dummy : R) (p : Parent × List R) :=
  (p.1.2, p.2.headD dummy, p.1)

private theorem expose_easy {R : Type} [Codec R] (dummy : R) : Easy (expose dummy) :=
  (Easy.fst.compose Easy.snd).pair ((Easy.snd.compose (Iter.leader dummy)).pair Easy.fst)

private def tagRow {R : Type} (p : (Bool × Header.Wire) × R × Parent) :=
  ((p.1.1,(p.1.2,p.2.1)),p.2.2)

private theorem tagRow_easy {R : Type} [Codec R] : Easy (@tagRow R) := by unfold tagRow; fun_prop

private def replaceRow {R : Type} (p : (Header.Wire × R) × Parent) :=
  (p.2, [p.1.2])

private theorem replaceRow_easy {R : Type} [Codec R] : Easy (@replaceRow R) := by
  unfold replaceRow
  exact Easy.snd.pair (((Easy.fst.compose Easy.snd).pair (Easy.const [])).compose Easy.cons)

/-- The same local polynomial accommodates both directions, all parent frames,
and every depth. The additive `size (row t)` is the actual input/output scan.
A fixed `R` can contain an entire serialized stream. -/
theorem bounded {R : Type} [Codec R] (dummy : R) (a W : ℕ) (axis : Fin (a+1)) : ∃ d C : ℕ,
    ∀ {I : Type} (s : I → Shape) (row : I → R), (∀ t, 0 < (s t).level) →
    let child t := descend (a+1) W axis (s t)
    let b t := C*(Header.scale (a+1) (s t)+1)^d + volume (a+1) (s t) + size (row t)
    (BoundedTask b b (fun t => send (saved a W (s t), [row t]))
      (fun t => .fork (.fork (.atom (decide (0 < (child t).level))) (send (Header.wire (a+1) (child t),row t)))
        (send (saved a W (s t))))) ∧
    (BoundedTask b b (fun t => .fork (send (Header.wire (a+1) (child t),row t)) (send (saved a W (s t))))
      (fun t => send (saved a W (s t),[row t]))) ∧
    (∀ t, size (saved a W (s t)) ≤ 40*(b t+1)) := by
  let A := a+1
  let r := Header.regime A
  let child (s : Shape) := descend A W axis s
  let tag (s : Shape) := (decide (0 < (child s).level),Header.wire A (child s))
  have generated : r.Has tag := Header.descend_tagged A W axis
  have extent : Dom r.scale (fun s => size (tag s)) := Strip.Regime.Small.extent generated
  obtain ⟨t,dt,prog⟩ := generated
  obtain ⟨d,C,bound⟩ := (r.gauge.add dt).add extent
  refine ⟨d,C,?_⟩
  intro I s row pos
  let loc (x : I) := C*(Header.scale A (s x)+1)^d
  let b (x : I) := loc x + volume A (s x) + size (row x)
  let parent (x : I) := saved a W (s x)
  let T (x : I) := size (tag (s x))
  have pb (x : I) : Header.scale A (s x) + t (s x) + T x ≤ loc x := bound (s x)
  have hb (x : I) : size (parent x) ≤ 30*volume A (s x) + Header.scale A (s x) + 9 := header_size a W _ (pos x)
  have start := (expose_easy dummy).on (fun x : I => (parent x,[row x]))
  have gen := (prog.on s).left (fun x : I => send (row x,parent x))
  have chain := (start.compose gen).compose (tagRow_easy.on (fun x : I => (tag (s x),row x,parent x)))
  have down : Task b (fun x : I => send (parent x,[row x]))
      (fun x => .fork (.fork (.atom (tag (s x)).1) (send ((tag (s x)).2,row x))) (send (parent x))) := by
    apply chain.bound 70
    intro x
    rw [size_prod (parent x, [row x]), size_prod (tag (s x),row x,parent x)]
    dsimp only [Prod.fst, Prod.snd]
    rw [size_prod (row x, parent x), size_cons, size_nil]
    have pp := pb x; have hp := hb x
    dsimp only [T,b] at pp ⊢; omega
  have replySize (x : I) : size ((Header.wire A (child (s x)),row x),parent x) + 1 ≤ 40*(b x+1) := by
    rw [size_prod ((Header.wire A (child (s x)),row x),parent x)]
    dsimp only [Prod.fst,Prod.snd]
    rw [size_prod (Header.wire A (child (s x)),row x)]
    have pp := pb x
    have hp := hb x
    change Header.scale A (s x) + t (s x) +
      (size (decide (0 < (child (s x)).level)) + size (Header.wire A (child (s x))) + 1) ≤ loc x at pp
    dsimp only [b,Prod.fst,Prod.snd]; omega
  have up : Task b (fun x : I => .fork (send (Header.wire A (child (s x)),row x)) (send (parent x)))
      (fun x => send (parent x,[row x])) :=
    (replaceRow_easy.on (fun x : I => ((Header.wire A (child (s x)),row x),parent x))).bound 40 replySize
  refine ⟨?_,?_,?_⟩
  · apply (BoundedTask.of_time down).bound 1 80
    · intro x; change b x+1 ≤ 1*(b x+1); simp
    · intro x
      change size (parent x,[row x]) + b x + 1 ≤ 80*(b x+1)
      rw [size_prod (parent x,[row x])]
      dsimp only [Prod.fst,Prod.snd]
      rw [size_cons,size_nil]
      have pp := pb x; have hp := hb x
      dsimp only [b]; omega
  · apply (BoundedTask.of_time up).bound 1 80
    · intro x; change b x+1 ≤ 1*(b x+1); simp
    · intro x
      change size ((Header.wire A (child (s x)),row x),parent x) + b x + 1 ≤ 80*(b x+1)
      have := replySize x
      omega
  · intro x
    change size (parent x) ≤ 40*(b x+1)
    have := pb x; have := hb x
    dsimp only [b]; omega

/-- A call can send and return distinct records. For linearly sized streams
the common clock and arena depend only on the parent shape. -/
theorem boundedRows {R : Type} [Codec R] (dummy : R) (a W : ℕ) (axis : Fin (a+1)) : ∃ d C : ℕ,
    ∀ {I : Type} (s : I → Shape) (input output : I → R) (E : ℕ),
    (∀ t, 0 < (s t).level) →
    (∀ t, size (input t) ≤ E*(volume (a+1) (s t)+1)) →
    (∀ t, size (output t) ≤ E*(volume (a+1) (s t)+1)) →
    let child t := descend (a+1) W axis (s t)
    let b t := C*(Header.scale (a+1) (s t)+1)^d + volume (a+1) (s t)
    (BoundedTask b b (fun t => send (saved a W (s t), [input t]))
      (fun t => .fork (.fork (.atom (decide (0 < (child t).level))) (send (Header.wire (a+1) (child t),input t)))
        (send (saved a W (s t))))) ∧
    (BoundedTask b b (fun t => .fork (send (Header.wire (a+1) (child t),output t)) (send (saved a W (s t))))
      (fun t => send (saved a W (s t),[output t]))) ∧
    (∀ t, size (saved a W (s t)) ≤ 40*((E+1)*(b t+1))) := by
  obtain ⟨d,C,run⟩ := bounded dummy a W axis
  refine ⟨d,C,?_⟩
  intro I s input output E pos inp out
  let b t := C*(Header.scale (a+1) (s t)+1)^d + volume (a+1) (s t)
  have absorb (t : I) (x : R) (h : size x ≤ E*(volume (a+1) (s t)+1)) :
      b t + size x + 1 ≤ (E+1)*(b t+1) := by
    have hv : volume (a+1) (s t) + 1 ≤ b t+1 := by dsimp only [b]; omega
    have hsize := h.trans (Nat.mul_le_mul_left E hv)
    rw [Nat.add_mul,one_mul]; omega
  have inc := run s input pos
  have ret := run s output pos
  exact ⟨inc.1.bound (E+1) (E+1) (fun t => absorb t _ (inp t)) (fun t => absorb t _ (inp t)),
    ret.2.1.bound (E+1) (E+1) (fun t => absorb t _ (out t)) (fun t => absorb t _ (out t)),
    fun t => (inc.2.2 t).trans (Nat.mul_le_mul_left 40 (absorb t _ (inp t)))⟩

end PhysicalWalshNode.ChildAdapter

end NearSquareRoot
end Computability
end OAI
