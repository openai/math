import OAI.Computability.NearSquareRoot.CRTControlledEffectiveTemplate
import OAI.Computability.NearSquareRoot.CRTControlledFlat

/-! # A single command context for the prepared XOR with two physical chunks

The eight rotations, signed displacements, table construction, radix-sort repair,
and header copies are selected on the entire input domain. Only the rectangular
interchange calls are substituted when the outer exponent changes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.Effective

open IntegerMultiplication Code Strip Strip.Dims Loom Adic Packed

noncomputable section

variable {X : Type} {r : Regime X} {l : X → ℕ} {U : X → Type}
variable (rect : Cmd → ℝ → Prop) (H L i : X → ℕ) (P G S : X → Tape)
variable (u : (x : X) → Series (U x))

/-- Rectangular subroutine with the regime header already adapted to the
named rectangle's canonical packet. -/
abbrev RectangleProgram (n : X → ℕ) :=
  ∀ f : (x : X) → SpanKey (P x) (G x) (S x) (Block 2 (n x)) → U x → Bead,
    let s x := stock 2 (P x) (G x) (S x) (n x)
    Program rect n r (fun x => (s x).count) l (together r.header (cloth s u f))
      (cloth s u fun x a => f x (swapper _ _ _ a))

abbrev RowProgram (e : (x : X) → Pin (P x) → Equiv.Perm (Row (H x) (L x) (i x))) :=
  ∀ f : (x : X) → RotationAddress H L i P G S x → U x → Bead,
    let s := rotationLayout H L i P G S
    Program rect (extent H L i) r (fun x => (s x).count) l
      (together r.header (cloth s u f))
      (cloth s u fun x a => f x (replaceRow a ((e x a.1).symm (sourceRow a))))

variable (hp : Told r P) (hg : Told r G) (hs : Told r S)
variable (shape : r.Has (fun x => signs (H x) (L x) (i x))) (hc : r.Has (tally ∘ extent H L i))
variable (z : ∀ x, (u x).count ≤ l x)
variable (swap : RectangleProgram (r := r) (l := l) rect P G S u (extent H L i))

include swap in
theorem exchangeTemplate : RowProgram rect H L i P G S (r := r) (l := l) u
    (fun _ _ => Equiv.prodComm _ _) := by
  intro f
  let row := rotationLayout H L i P G S
  let raw x := stock 2 (P x) (G x) (S x) (extent H L i x)
  let v (x : X) : Adopt (row x) (raw x) :=
    let q := package (H x) (L x) (i x)
    (Adopt.same _).split (q.split ((Adopt.same _).split (q.split (Adopt.same _))))
  have w := swap (fun x a => f x ((v x).cast.symm a))
  have countEq (x : X) : (raw x).count = (row x).count := (v x).cost.symm
  have transfer (g : (x : X) → RotationAddress H L i P G S x → U x → Bead) :
      cloth raw u (fun x a => g x ((v x).cast.symm a)) = cloth row u g := by
    funext x
    unfold cloth stackRun
    rw [(v x).packet]
    apply congrArg (stripe _)
    funext a
    change strip (u x) (g x ((v x).cast.symm ((v x).cast a))) = _
    rw [Equiv.symm_apply_apply]
  have swapped (x : X) (a : _) : (v x).cast.symm (swapper _ _ _ a) =
      replaceRow ((v x).cast.symm a) (sourceRow ((v x).cast.symm a)).swap := rfl
  change Program _ _ _ (fun x => (raw x).count) _
    (together _ (cloth raw u (fun x a => f x ((v x).cast.symm a))))
    (cloth raw u (fun x a => f x ((v x).cast.symm (swapper _ _ _ a)))) at w
  simp only [countEq, swapped] at w
  rw [transfer f, transfer (fun x a => f x (replaceRow a (sourceRow a).swap))] at w
  exact w

include z in
private theorem composeTemplate (st : Station r (rotationLayout H L i P G S))
    {a b : (x : X) → Pin (P x) → Equiv.Perm (Row (H x) (L x) (i x))}
    (ha : RowProgram rect H L i P G S (r := r) (l := l) u a)
    (hb : RowProgram rect H L i P G S (r := r) (l := l) u b) :
    RowProgram rect H L i P G S (r := r) (l := l) u (fun x p => (a x p).trans (b x p)) := by
  intro f
  exact (ha f).pipe (hb (fun x v => f x (replaceRow v ((a x v.1).symm (sourceRow v)))))
    st.1 (cloth_size _ _ st f z)

variable (ctrl : (x : X) → Pin (P x) → Queue (H x) (L x) (i x))
variable (ready : Strip.Trace r (fun x => layout (P x)) fun x a => send (badge (ctrl x a)))

include hp hg hs shape hc swap ready z in
private theorem walkTemplate (t : Turn) (ht : t.shift = 1 ∨ t.shift = -1) :
    RowProgram rect H L i P G S (r := r) (l := l) u (fun x p => rowWalk (ctrl x p) t) := by
  have last : RowProgram rect H L i P G S (r := r) (l := l) u (fun x p => lastTurn (ctrl x p) t) :=
    fun f => Program.fixed (lastTurnStage H L i shape hc t ht P G S 0 u hg hs le_rfl z ctrl ready f)
  let exchange := exchangeTemplate rect H L i P G S u swap
  let st := rotationStation H L i hc P G S hp hg hs
  cases e : t.wing with
  | true =>
    have eq (x p) : rowWalk (ctrl x p) t = lastTurn (ctrl x p) t := by
      ext yz : 1
      change (Packed.walk t (ctrl x p,yz)).2 = _
      rw [Packed.walk,e,ite_eq_left rfl]
      rfl
    simp_rw [eq]
    exact last
  | false =>
    have eq (x p) : rowWalk (ctrl x p) t =
        ((Equiv.prodComm _ _).trans (lastTurn (ctrl x p) t)).trans (Equiv.prodComm _ _) := by
      ext yz : 1
      change (Packed.walk t (ctrl x p,yz)).2 = _
      rw [Packed.walk,e,ite_eq_right (by decide)]
      rfl
    simp_rw [eq]
    exact composeTemplate rect H L i P G S u z st (composeTemplate rect H L i P G S u z st exchange last) exchange

include hp hg hs shape hc swap ready z in
private theorem cruiseTemplate :
    RowProgram rect H L i P G S (r := r) (l := l) u (fun x p => rowCruise (ctrl x p) Packed.order) := by
  have st := rotationStation H L i hc P G S hp hg hs
  suffices bound : ∀ o : List Turn, (∀ t ∈ o, t ∈ Packed.order) →
      RowProgram rect H L i P G S (r := r) (l := l) u (fun x p => rowCruise (ctrl x p) o) from
    bound _ fun _ => id
  intro o
  induction o with
  | nil =>
    intro _ f
    exact Program.ofRip (Drive.self st.1 (cloth_size _ _ st f z))
  | cons t ts ih =>
    intro allowed
    have et := allowed t List.mem_cons_self
    have ht : t.shift = 1 ∨ t.shift = -1 := by
      simp only [Packed.order, List.mem_cons, List.not_mem_nil, or_false] at et
      rcases et with h|h|h|h|h|h|h|h <;> subst t <;> decide
    simp_rw [rowCruise_cons]
    exact composeTemplate rect H L i P G S u z st
      (walkTemplate rect H L i P G S u hp hg hs shape hc z swap ctrl ready t ht)
      (ih fun t ha => allowed t (List.mem_cons_of_mem _ ha))

include hp hg hs shape hc swap ready z in
theorem rowIdealTemplate (sparse : ∀ x, (3*extent H L i x+1)*(32*i x) ≤ 2^width (H x) (L x)) :
    RowProgram rect H L i P G S (r := r) (l := l) u (fun x p => rowIdeal (ctrl x p)) := by
  have st := rotationStation H L i hc P G S hp hg hs
  have cruise := cruiseTemplate rect H L i P G S u hp hg hs shape hc z swap ctrl ready
  have repair : RowProgram rect H L i P G S (r := r) (l := l) u (fun x p => rowRepair (ctrl x p)) :=
    fun f => Program.fixed (rowRepairStage H L i P G S 0 u ctrl hc shape sparse hg.station hs.station ready z le_rfl f)
  simpa only [rowRepaired] using composeTemplate rect H L i P G S u z st cruise repair

include hp hg hs shape hc z swap in
/-- All Boolean control masks share the same fixed setup and finite sequence
of rectangle calls for the chosen runtime family, including the repair pass. -/
theorem maskedXorTemplate (b : (x : X) → Pin (P x) → Fin (i x) → Bool)
    (sparse : ∀ x, (3*extent H L i x+1)*(32*i x) ≤ 2^width (H x) (L x))
    (controls : Strip.Trace r (fun x => layout (P x)) fun x a => send (List.ofFn (b x a)))
    (f : (x : X) → RotationAddress H L i P G S x → U x → Bead) :
    let s := rotationLayout H L i P G S
    Program rect (extent H L i) r (fun x => (s x).count) l
      (together r.header (cloth s u f)) (cloth s u fun x a =>
        f x (a.1,maskTarget (b x a.1) a.2.1,a.2.2)) := by
  have run := rowIdealTemplate rect H L i P G S u hp hg hs shape hc z swap
    (fun x p => controlMask (H x) (L x) (b x p)) (controlMaskTrace H L i shape b controls) sparse f
  simpa only [rowIdeal_controlMask_symm,replaceRow,sourceRow] using run

end
end Controlled.Effective

end NearSquareRoot
end Computability
end OAI
