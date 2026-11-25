import OAI.Computability.NearSquareRoot.InterchangeCalls
import OAI.Computability.NearSquareRoot.BoundedBranch
import OAI.Computability.IntegerMultiplication.Thin.Exchange
import OAI.Computability.IntegerMultiplication.Bits.Small

/-! # Linear-time bounded-width interchange on the recursive wire format

The leading tally in the request selects one of finitely many field widths.
Each leaf obtains its three traversal rulers from the serialized shapes. The
records are arbitrary trees and their physical sizes are included in the cost.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress.Request

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  IntegerMultiplication.Thin

/-- Every spectator radix is at least two. -/
def solidShape {b : ℕ} (a : Request b) :=
  solid a.before ∧ solid a.between ∧ solid a.after_

private theorem rows_fit {X : Type} (s : Series X) (v : X → Tree) :
    s.count ≤ (stripe s v).count := by
  rw [stripe_simple, Series.count]
  induction s.explore with
  | nil => simp [Tree.count]
  | cons x xs ih => simp only [List.length_cons, Task.forest_cons, Tree.count]; omega

private theorem makeRim {I : Type} {w : I → ℝ} {z : I → Tree} (s : I → Dims.Tape)
    (hs : ∀ i, solid (s i)) (hroom : ∀ i, (room (s i) : ℝ) ≤ w i)
    (h : Carries w z (fun i => send (shape (s i)))) : Rim w z (fun i => layout (s i)) := by
  refine ⟨?_, fun i => by rw [Dims.space]; exact wide _ (hs i)⟩
  simp only [Roll, Dims.space]
  refine h.sequence ⟨h.budget, fun i => room (s i), Dims.unary.on (fun i => ⟨s i, hs i⟩), 2, ?_⟩
  intro i
  have := h.budget i
  have := hroom i
  norm_num
  linarith

private structure Fixed (b e : ℕ) where
  P : Dims.Tape
  G : Dims.Tape
  B : Dims.Tape
  psol : solid P
  gsol : solid G
  bsol : solid B
  l : ℕ
  data : SpanKey P G B (Block b e) → Tree

private def Fixed.req {b e : ℕ} (x : Fixed b e) : Request b :=
  ⟨x.P,x.G,x.B,e,x.l,x.data⟩

private theorem fixed_task (b e : ℕ) (hb : 1 ≤ b) :
    Task (fun x : Fixed b e => ((job b).issue x.req).count)
      (fun x => (job b).issue x.req) (fun x => (job b).reply x.req) := by
  let I := Fixed b e
  let tag (x : I) := x.req.header
  let data (x : I) := stripe x.req.rows x.data
  let z (x : I) := (job b).issue x.req
  let w (x : I) : ℝ := (z x).count
  have pos (x : I) : 1 ≤ w x := by simpa only [w, Nat.one_le_cast] using (show 1 ≤ (z x).count from (z x).count_pos)
  have vol : Volume w z := ⟨1,by simp [w]⟩
  have both : Volume w (fun x => Tree.fork (tag x) (data x)) := vol
  have tagRead : Carries w z tag := Carries.dropRight pos both.left both.right
  have readData : Carries w z data := Carries.dropLeft pos both.left both.right
  let P (x : I) := layout x.P
  let G (x : I) := layout x.G
  let B (x : I) := layout x.B
  have hroom (x : I) : room x.P * (room x.G * room x.B) ≤ (z x).count := by
    have hh := rows_fit x.req.rows x.data
    change ((layout x.P).cart ((line b e).cart ((layout x.G).cart
      ((line b e).cart (layout x.B))))).count ≤ (data x).count at hh
    have num : room (field b e) = b^e := (Dims.space _).symm.trans (lineSize b e)
    simp only [Series.count_cart, Dims.space, num] at hh
    have he := one_le_pow₀ hb (n := e)
    have hx : room x.P * (room x.G * room x.B) ≤
        room x.P * (b^e * (room x.G * (b^e * room x.B))) := by
      exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ he)).trans
        (Nat.le_mul_of_pos_left _ he))
    exact (hx.trans hh).trans (Nat.le_add_left _ _ |>.trans (Nat.le_succ _))
  have hp (x : I) := wide x.P x.psol
  have hg (x : I) := wide x.G x.gsol
  have hs (x : I) := wide x.B x.bsol
  have rP : Rim w z P := makeRim _ (fun x => x.psol) (fun x => by
    dsimp only [w]
    exact_mod_cast (Nat.le_mul_of_pos_right _ (Nat.mul_pos (hg x) (hs x))).trans (hroom x))
    (tagRead.chain (Carries.func pos both.left (fun x => x.2.1) (by fun_prop)))
  have rG : Rim w z G := makeRim _ (fun x => x.gsol) (fun x => by
    dsimp only [w]
    exact_mod_cast ((Nat.le_mul_of_pos_right _ (hs x)).trans
      (Nat.le_mul_of_pos_left _ (hp x))).trans (hroom x))
    (tagRead.chain (Carries.func pos both.left (fun x => x.2.2.1) (by fun_prop)))
  have rB : Rim w z B := makeRim _ (fun x => x.bsol) (fun x => by
    dsimp only [w]
    exact_mod_cast ((Nat.le_mul_of_pos_left _ (hg x)).trans
      (Nat.le_mul_of_pos_left _ (hp x))).trans (hroom x))
    (tagRead.chain (Carries.func pos both.left (fun x => x.2.2.2) (by fun_prop)))
  have fit : ∃ D : ℕ, ∀ x, ((fusion P (fusion G B) x).count:ℝ) ≤ (D:ℝ)*w x := by
    refine ⟨1,fun x => ?_⟩
    simp only [fusion,P,G,B,Series.count_cart,Dims.space,Nat.cast_one,one_mul]
    dsimp only [w]
    exact_mod_cast hroom x
  have he : 1 ≤ (line b e).count := by rw [lineSize]; exact one_le_pow₀ hb
  have result := Thin.skew P G B (line b e) he rP rG rB fit (fun x => x.data) readData
  change Carries w z (fun x => (job b).reply x.req) at result
  simpa only [w, Nat.ceil_natCast] using result.runs.release

private def freeze {b e : ℕ} (a : Request b) (h : solidShape a) (eq : a.width = e) : Fixed b e :=
  ⟨a.before,a.between,a.after_,h.1,h.2.1,h.2.2,a.recordWidth,eq ▸ a.contents⟩

private theorem req_freeze {b e : ℕ} (a : Request b) (h : solidShape a) (eq : a.width = e) :
    (freeze a h eq).req = a := by cases a; cases eq; rfl

/-- A single stack program handles all requests of field width at most `q`,
including the zero-width case. The program reads the field width from the
request and traverses its variable spectator layouts. -/
theorem bounded_leaf_task {I : Type} (b q : ℕ) (hb : 1 ≤ b) (a : I → Request b)
    (solid : ∀ i, solidShape (a i)) (bound : ∀ i, (a i).width ≤ q) :
    Task (fun i => ((job b).issue (a i)).count)
      (fun i => (job b).issue (a i)) (fun i => (job b).reply (a i)) := by
  let which (i : I) : Fin (q+1) := ⟨(a i).width, by have := bound i; omega⟩
  let z i := (job b).issue (a i)
  let w i : ℝ := (z i).count
  have pos (i : I) : 1 ≤ w i := by simpa only [w, Nat.one_le_cast] using (show 1 ≤ (z i).count from (z i).count_pos)
  have vol : Volume w z := ⟨1,by simp [w]⟩
  have both : Volume w (fun i => Tree.fork (a i).header (stripe (a i).rows (a i).contents)) := vol
  have extra : Carries w z (fun i => send (which i)) :=
    (Carries.dropRight pos both.left both.right).chain (Carries.func pos both.left Prod.fst Easy.fst)
  have prep := (extra.twice (Carries.idles pos vol)).runs.release
  have cases' := Task.finite_select (p := z) (q := fun i => (job b).reply (a i))
    (a := fun i => (z i).count) which fun s => by
      let f (i : {i // which i = s}) := freeze (a i) (solid i) (congrArg Fin.val i.property)
      have eq (i : {i // which i = s}) : (f i).req = a i := req_freeze _ _ _
      exact ((fixed_task b s.val hb).on f).conform
        (fun i => congrArg (fun u => ((job b).issue u).count) (eq i))
        (fun i => congrArg (job b).issue (eq i)) (fun i => congrArg (job b).reply (eq i))
  exact (prep.compose cases').bound 2 fun i => by
    change ⌈w i⌉₊ + (z i).count + 1 ≤ 2 * ((z i).count + 1)
    simp only [w, Nat.ceil_natCast]; omega

/-- The linear leaf may run after any bounded contractor which produces the issue. -/
theorem bounded_leaf_carries {I : Type} (b q : ℕ) (hb : 1 ≤ b) (a : I → Request b)
    (solid : ∀ i, solidShape (a i)) (bound : ∀ i, (a i).width ≤ q)
    {w : I → ℝ} {input : I → Tree} (h : Carries w input (fun i => (job b).issue (a i))) :
    Carries w input (fun i => (job b).reply (a i)) :=
  h.chain (Carries.cheap h.budget h.out _ (bounded_leaf_task b q hb a solid bound))

/-- The same leaf in the space-aware P192 compiler. Both the data registers
and the physical return stack have linear capacity above the parked deck. -/
theorem bounded_leaf_space {I : Type} (b q : ℕ) (hb : 1 ≤ b) (a : I → Request b)
    (solid : ∀ i, solidShape (a i)) (bound : ∀ i, (a i).width ≤ q) :
    Space.BoundedTask (fun i => ((job b).issue (a i)).count)
      (fun i => ((job b).issue (a i)).count) (fun i => (job b).issue (a i))
      (fun i => (job b).reply (a i)) :=
  (Space.BoundedTask.of_time (bounded_leaf_task b q hb a solid bound)).bound 1 2
    (by simp) (by intro; omega)

/-- A fleet can manufacture the leaf's entire query from its ordinary header
and stream, for any family of bounded widths visible at that header. -/
theorem bounded_leaf_fleet {I : Type} {r : Regime I} {b : ℕ} [NeZero b] (q : ℕ) (hb : 2 ≤ b)
    (a : I → Request b) (hw : r.Has (fun i => tally (a i).width))
    (hp : Told r (fun i => (a i).before)) (hg : Told r (fun i => (a i).between))
    (hs : Told r (fun i => (a i).after_)) (bound : ∀ i, (a i).width ≤ q)
    (hv : Manifest _ (fun i => (a i).recordWidth) (fun i => (a i).contents)) :
    Fleet r (fun i => (a i).recordWidth) (fun i => (a i).rows) (fun i => (a i).rows)
      (fun i => (a i).contents) (fun i => (a i).contents ∘ swapper _ _ _) := by
  have fld := (Told.carrier hb (fun i => (a i).width) hw).station
  have st : Station r (fun i => (a i).rows) :=
    hp.station.product (fld.product (hg.station.product (fld.product hs.station)))
  have tag : r.Small (fun i => (a i).header) := hw.pair (hp.shape.pair (hg.shape.pair hs.shape))
  have hdata := hv.lives st
  have pre := (Drive.small st.1 hdata tag).twice (Drive.self st.1 hdata)
  obtain ⟨k,run⟩ := pre
  exact ⟨k,bounded_leaf_carries b q (by omega) a (fun i => ⟨hp.solid i,hg.solid i,hs.solid i⟩)
    bound run⟩

/-- Apply the leaf in an enclosing physical layout. The supplied axis proves
that constructing the child's issue and consuming its reply preserves the
serialized order. This covers both end fields of a split interchange. -/
theorem bounded_axis_fleet {I : Type} {r : Regime I} {b : ℕ} [NeZero b] (q : ℕ) (hb : 2 ≤ b)
    {K : I → Type} (rows : (i : I) → Series (K i)) (P G B : I → Dims.Tape)
    (w l : I → ℕ) (axis : ∀ i, Axis (rows i) (P i) (line b (w i)) (G i)
      (line b (w i)) (B i)) (hw : r.Has (tally ∘ w))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (bound : ∀ i, w i ≤ q)
    (swap : (i : I) → K i → K i)
    (wire : ∀ i k, (axis i).view.cast (swap i k) = swapper _ _ _ ((axis i).view.cast k))
    (v : (i : I) → K i → Tree) (hv : Manifest _ l v) :
    Fleet r l rows rows v (fun i => v i ∘ swap i) := by
  let child (i : I) : Request b :=
    ⟨P i,G i,B i,w i,l i,v i ∘ (axis i).view.cast.symm⟩
  have h := bounded_leaf_fleet q hb child hw hp hg hs bound
    (hv.shift fun i => (axis i).view.cast.symm)
  have hin (i : I) : stripe (child i).rows (child i).contents = stripe (rows i) (v i) := by
    rw [(axis i).view.packet]
    exact congrArg (stripe _) (funext fun k => congrArg (v i) ((axis i).view.cast.symm_apply_apply k))
  have hout (i : I) : (job b).reply (child i) = stripe (rows i) (v i ∘ swap i) := by
    change stripe (child i).rows _ = _
    rw [(axis i).view.packet]
    apply congrArg (stripe _)
    funext k
    change v i ((axis i).view.cast.symm (swapper _ _ _ ((axis i).view.cast k))) = _
    rw [← wire, Equiv.symm_apply_apply]
    rfl
  change Drive r (fun i => (child i).rows.count) l
    (fun i => stripe (child i).rows (child i).contents) (fun i => (job b).reply (child i)) at h
  have hc : (fun i => (child i).rows.count) = fun i => (rows i).count :=
    funext fun i => (axis i).view.cost.symm
  rw [hc, funext hin, funext hout] at h
  exact h

end InterchangeAddress.Request

end NearSquareRoot
end Computability
end OAI
