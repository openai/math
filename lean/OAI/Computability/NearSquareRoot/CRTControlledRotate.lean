import OAI.Computability.NearSquareRoot.CRTControlledRow
import OAI.Computability.NearSquareRoot.CRTControlledXor

/-! # Rotation of a guarded address chunk from a virtual control word

The external control word is computed from each prefix. Reading the remote chunk from
the actual address permits a whole-chunk rotation with a signed displacement. Composing
these rotations and charged two-chunk interchanges carries out the eight-turn walk.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
open IntegerMultiplication.Code IntegerMultiplication.Loom IntegerMultiplication.Adic
open IntegerMultiplication.Packed IntegerMultiplication.Port

noncomputable section

private theorem slide_package_symm {H L i} (o : Packed.Span ℤ i) (z : Block 2 (cap i H L)) :
    (slide (H := H) (L := L) o).symm ((package H L i).cast.symm z) =
      (package H L i).cast.symm ((glide (offsets (H := H) (L := L) o)).symm z) := by
  apply plane.injective
  have hp (b) : plane ((package H L i).cast.symm b) = Adic.index 2 (cap i H L) b :=
    congrArg (Adic.index 2 _) ((package H L i).cast.apply_symm_apply b)
  rw [hp, Packed.slide, Equiv.symm_trans_apply, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply, hp]
  let v := offsets (H := H) (L := L) o
  let b := (glide v).symm z
  have e : Adic.index 2 (cap i H L) z = Adic.index 2 (cap i H L) b + v := by
    simpa only [b, Equiv.apply_symm_apply] using move_nat v b
  change Adic.index 2 (cap i H L) z + -v = Adic.index 2 _ b
  rw [e, add_assoc, add_neg_cancel, add_zero]

variable {X : Type} {r : Regime X} {l : X → ℕ}
variable (H L i : X → ℕ) (shape : r.Has fun x => signs (H x) (L x) (i x))
variable (extentReady : r.Has (tally ∘ extent H L i))
variable (t : Turn) (ht : t.shift = 1 ∨ t.shift = -1)

include shape extentReady ht

open Fleet in
/-- Rotate one fibre, including its whole spectator suffix, after both control words
are available as encoded words in the current header. -/
theorem rotateFibre {B : X → Type} (s : (x : X) → Series (B x)) (hs : Station r s)
    (ctrl remote : (x : X) → Queue (H x) (L x) (i x))
    (hc : r.Has fun x => badge (ctrl x)) (hr : r.Has fun x => badge (remote x))
    (f : (x : X) → Queue (H x) (L x) (i x) × B x → Tree) (hf : Manifest _ l f) :
    Fleet r l (cartS (Qt H L i) s) (cartS (Qt H L i) s) f
      (fun x v => f x ((slide (start t (ctrl x) (remote x))).symm v.1, v.2)) := by
  let A x := (package (H x) (L x) (i x)).split (Adopt.same (s x))
  let n := extent H L i
  let v x := offsets (H := H x) (L := L x) (start t (ctrl x) (remote x))
  let f' (x : X) (b : Block 2 (n x) × B x) := f x ((A x).cast.symm b)
  obtain ⟨w, ready, value⟩ := revealed H L i shape ctrl remote hc hr t ht
  have move := Adic.offset (p := 2) (by decide) n extentReady hs w v value ready f'
    (hf.shift _) Pinpoint.unit
  apply Fleet.align _ _ (t := cartS (fun x => line 2 (n x)) s)
    (u := cartS (fun x => line 2 (n x)) s) A A
  suffices e :
      (fun x => (fun v => f x ((slide (start t (ctrl x) (remote x))).symm v.1, v.2)) ∘
          (A x).cast.symm) = fun x b => f' x ((glide (v x)).symm b.1, b.2) by
    rw [e]
    simp only [Pinpoint.one, one_mul] at move
    exact move
  funext x b
  change f x ((Packed.slide _).symm ((package ..).cast.symm b.1), b.2) =
    f x ((package ..).cast.symm ((glide (v x)).symm b.1), b.2)
  rw [slide_package_symm]

open Fleet in
/-- There is one stream entry for every setting of the two physical chunks and both
spectators. For each address of the first chunk its actual bits supply the second
control word of the packed rotation. -/
theorem rotateRowRight {G S : X → Type} (g : (x : X) → Series (G x))
    (s : (x : X) → Series (S x)) (hg : Station r g) (hs : Station r s)
    (ctrl : (x : X) → Queue (H x) (L x) (i x)) (hc : r.Has fun x => badge (ctrl x))
    (f : (x : X) → Queue (H x) (L x) (i x) × G x × Queue (H x) (L x) (i x) × S x → Tree)
    (hf : Manifest _ l f) :
    let q := Qt H L i
    let rows := cartS q (cartS g (cartS q s))
    Fleet r l rows rows f (fun x a => f x
      (a.1, a.2.1, (slide (start t (ctrl x) a.1)).symm a.2.2.1, a.2.2.2)) := by
  let Q x := Queue (H x) (L x) (i x)
  let q := Qt H L i
  let badgeLabel (x : X) (a : Q x) := send (badge a)
  have z := initiative H L i extentReady
  have st := z.valid.product hs
  apply Fleet.guide z.valid (hg.product st) hf badgeLabel z.meter
    (z.offer.monoSize (fun _ => le_rfl) (fun _ => Nat.zero_le _))
  let Y := Sigma Q
  let r' := onboard r badgeLabel z.meter
  let g' (x : Y) := g x.1
  let s' (x : Y) := s x.1
  let f' (x : Y) (b : G x.1 × Q x.1 × S x.1) := f x.1 (x.2,b)
  have hf' : Manifest _ (fun x : Y => l x.1) f' :=
    Manifest.localize (s := fun x a b => f x (a,b)) hf
  apply Fleet.wind (hg.adapt badgeLabel z.meter g) (st.adapt badgeLabel z.meter _) hf'
  let Y' := Sigma (fun x : Y => G x.1)
  let rr := r'.pull (Sigma.fst : Y' → Y)
  have lift {F : Type} [Codec F] {p : X → F} (hp : r.Has p) :
      rr.Has (fun x : Y' => p x.1.1) :=
    Task.BT.map (onboard_small (r := r) badgeLabel z.meter (send ∘ p) hp) Sigma.fst
  have rem : rr.Has (fun x : Y' => badge x.1.2) :=
    Task.BT.map (onboard_hat (r := r) badgeLabel z.meter) Sigma.fst
  have hm : Manifest _ (fun x : Y' => l x.1.1) (fun x b => f x.1.1 (x.1.2,x.2,b)) :=
    Manifest.localize (s := fun (x : Y) a b => f' x (a,b)) hf'
  exact rotateFibre (r := rr) (fun x => H x.1.1) (fun x => L x.1.1) (fun x => i x.1.1)
    (lift shape) (lift extentReady) t ht (fun x => s x.1.1)
    ((hs.adapt badgeLabel z.meter s).pull _) (fun x => ctrl x.1.1) (fun x => x.1.2)
    (lift hc) rem _ hm

open Fleet in
/-- The virtual controls may depend on the preceding address. Their production is
charged by a P192 trace computing the per-prefix `badge` from the original header. -/
theorem rotateRowRightWithPrefix {P G S : X → Type} (p : (x : X) → Series (P x))
    (g : (x : X) → Series (G x)) (s : (x : X) → Series (S x))
    (hg : Station r g) (hs : Station r s)
    (ctrl : (x : X) → P x → Queue (H x) (L x) (i x))
    (hc : Strip.Trace r p fun x a => send (badge (ctrl x a)))
    (f : (x : X) → P x × Queue (H x) (L x) (i x) × G x × Queue (H x) (L x) (i x) × S x → Tree)
    (hf : Manifest _ l f) :
    let q := Qt H L i
    let rows := cartS p (cartS q (cartS g (cartS q s)))
    Fleet r l rows rows f fun x a => f x (a.1, a.2.1, a.2.2.1,
      (Packed.slide (start t (ctrl x a.1) a.2.1)).symm a.2.2.2.1, a.2.2.2.2) := by
  let header (x : X) (a : P x) := send (badge (ctrl x a))
  let Y := Sigma P
  let rr := onboard r header hc.meter
  have stations := (initiative H L i extentReady).valid
  apply Fleet.guide hc.valid (stations.product (hg.product (stations.product hs))) hf header hc.meter
    (hc.offer.monoSize (fun _ => le_rfl) (fun _ => Nat.zero_le _))
  have lift {F : Type} [Codec F] {v : X → F} (h : r.Has v) : rr.Has (fun x : Y => v x.1) :=
    onboard_small header hc.meter (send ∘ v) h
  exact rotateRowRight (r := rr) (fun y => H y.1) (fun y => L y.1) (fun y => i y.1)
    (lift shape) (lift extentReady) t ht (fun y => g y.1) (fun y => s y.1)
    (hg.adapt header hc.meter g) (hs.adapt header hc.meter s)
    (fun y => ctrl y.1 y.2) (onboard_hat header hc.meter)
    _ (Manifest.localize (s := fun x a b => f x (a,b)) hf)

omit shape extentReady ht

/-- Coordinates of the active chunks together with three spectator ranges. -/
abbrev RotationAddress (P G S : X → Tape) (x : X) :=
  SpanKey (P x) (G x) (S x) (Queue (H x) (L x) (i x))

/-- Physical order of the two chunks in all the rows. -/
abbrev rotationLayout (P G S : X → Tape) (x : X) :=
  Path (P x) (Qt H L i x) (G x) (Qt H L i x) (S x)

variable (P G S : X → Tape) (ρ : ℝ) {U : X → Type} (u : (x : X) → Series (U x))

abbrev replaceRow {T : Type} {P G S : Tape} (a : SpanKey P G S T)
    (newRow : T × T) : SpanKey P G S T :=
  (a.1, newRow.1, a.2.2.1, newRow.2, a.2.2.2.2)

abbrev sourceRow {T : Type} {P G S : Tape} (a : SpanKey P G S T) : T × T :=
  (a.2.1,a.2.2.2.1)

/-- A charged operation on the two addressed chunks. The other three address fields
and all payload bits are carried unchanged to the image. -/
abbrev RowStage (e : (x : X) → Pin (P x) → Equiv.Perm (Row (H x) (L x) (i x))) :=
  ∀ f : (x : X) → RotationAddress H L i P G S x → U x → Bead,
    let s := rotationLayout H L i P G S
    Breeze (Spindle.modes (extent H L i) (τ := ρ)) r (fun x => (s x).count) l
      (together r.header (cloth s u f))
      (cloth s u (fun x a => f x (replaceRow a ((e x a.1).symm (sourceRow a)))))

variable (hP : Told r P) (hG : Told r G) (hS : Told r S)
variable (guard : ∀ x j, j ∈ P x ++ G x ++ S x → j ≤ Net.Shuttle.base)
variable (sw : RectInterchange r (extent H L i) ρ) (hρ : 0 ≤ ρ)
variable (z : ∀ x, (u x).count ≤ l x)

include extentReady hP hG hS in
theorem rotationStation : Station r (rotationLayout H L i P G S) := by
  let q := (initiative H L i extentReady).valid
  exact hP.station.product (q.product (hG.station.product (q.product hS.station)))

private def packagePair (x : X) : Adopt (rotationLayout H L i P G S x)
    (Loom.stock 2 (P x) (G x) (S x) (extent H L i x)) :=
  let q := package (H x) (L x) (i x)
  (Adopt.same _).split (q.split ((Adopt.same _).split (q.split (Adopt.same _))))

include extentReady hP hG hS guard sw z in
/-- Apply physical field interchange to the two packed chunks. -/
theorem exchangeRow : RowStage H L i P G S ρ (r := r) (l := l) u
    (fun _ _ => Equiv.prodComm _ _) := by
  intro f
  let v := packagePair H L i P G S
  let raw := fun x => Loom.stock 2 (P x) (G x) (S x) (extent H L i x)
  let row := rotationLayout H L i P G S
  have w := sw P G S extentReady hP hG hS guard l u z (fun x a => f x ((v x).cast.symm a))
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
      replaceRow ((v x).cast.symm a) ((sourceRow ((v x).cast.symm a)).swap) := rfl
  change Breeze _ _ (fun x => (raw x).count) _
    (together _ (cloth raw u (fun x a => f x ((v x).cast.symm a))))
    (cloth raw u (fun x a => f x ((v x).cast.symm (swapper _ _ _ a)))) at w
  simp only [countEq, swapped] at w
  rw [transfer f, transfer (fun x a => f x (replaceRow a (sourceRow a).swap))] at w
  exact w

include z in
theorem composeRows (st : Station r (rotationLayout H L i P G S))
    {a b : (x : X) → Pin (P x) → Equiv.Perm (Row (H x) (L x) (i x))}
    (ha : RowStage H L i P G S ρ (r := r) (l := l) u a)
    (hb : RowStage H L i P G S ρ (r := r) (l := l) u b) :
    RowStage H L i P G S ρ (r := r) (l := l) u (fun x p => (a x p).trans (b x p)) := by
  intro f
  exact Spindle.Breeze.pipe (ha f)
    (hb (fun x v => f x (replaceRow v ((a x v.1).symm (sourceRow v)))))
    (Drive.fetch st.1 (cloth_size _ _ st f z))

/-- A header-supplied word can be used throughout a stationary prefix stream. -/
theorem traceHeaderWord {B : X → Type} {s : (x : X) → Series (B x)} (hs : Station r s)
    {F : Type} [Codec F] {v : X → F} (h : r.Has v) :
    Strip.Trace r s (fun x _ => send (v x)) :=
  ⟨hs, (Regime.Small.extent h).map Sigma.fst, clones hs (fun _ => le_rfl) _ h⟩

variable (ctrl : (x : X) → Pin (P x) → Queue (H x) (L x) (i x))
variable (hc : Strip.Trace r (fun x => layout (P x)) fun x a => send (badge (ctrl x a)))

/-- One conditional displacement towards the last chunk. -/
def lastTurn {H L i} (c : Queue H L i) (t : Turn) : Equiv.Perm (Row H L i) where
  toFun a := (a.1, Packed.slide (start t c a.1) a.2)
  invFun a := (a.1, (Packed.slide (start t c a.1)).symm a.2)
  left_inv a := by simp
  right_inv a := by simp

include shape extentReady ht hG hS hc z hρ in
theorem lastTurnStage : RowStage H L i P G S ρ (r := r) (l := l) u
    (fun x p => lastTurn (ctrl x p) t) := by
  intro f
  apply Strip.Breeze.launch _ (Spindle.belly _ hρ)
  exact rotateRowRightWithPrefix H L i shape extentReady t ht _ _ _
    hG.station hS.station ctrl hc _ (visible u f z)

include shape extentReady ht hP hG hS guard sw hρ z hc in
theorem rowWalkStage : RowStage H L i P G S ρ (r := r) (l := l) u
    (fun x p => rowWalk (ctrl x p) t) := by
  let last := lastTurnStage H L i shape extentReady t ht P G S ρ u hG hS hρ z ctrl hc
  let exchange := exchangeRow H L i extentReady P G S ρ u hP hG hS guard sw z
  let st := rotationStation H L i extentReady P G S hP hG hS
  cases e : t.wing with
  | true =>
    have eq (x p) : rowWalk (ctrl x p) t = lastTurn (ctrl x p) t := by
      apply Equiv.ext
      intro yz
      change (Packed.walk t (ctrl x p, yz)).2 = _
      rw [Packed.walk, e, ite_eq_left rfl]
      rfl
    simp_rw [eq]
    exact last
  | false =>
    let pair := composeRows H L i P G S ρ u z st exchange last
    have eq (x p) : rowWalk (ctrl x p) t =
        ((Equiv.prodComm _ _).trans (lastTurn (ctrl x p) t)).trans (Equiv.prodComm _ _) := by
      apply Equiv.ext
      intro yz
      change (Packed.walk t (ctrl x p, yz)).2 = _
      rw [Packed.walk, e, ite_eq_right (by decide)]
      rfl
    simp_rw [eq]
    exact composeRows H L i P G S ρ u z st pair exchange

include shape extentReady hP hG hS guard sw hρ z hc in
/-- All eight guarded signed shifts with arbitrary controls generated from each
external prefix. The priced P192 interchange is used exactly for the opposite wing. -/
theorem rowCruiseStage : RowStage H L i P G S ρ (r := r) (l := l) u
    (fun x p => rowCruise (ctrl x p) Packed.order) := by
  have st := rotationStation H L i extentReady P G S hP hG hS
  suffices bound : ∀ o : List Turn, (∀ t ∈ o, t ∈ Packed.order) →
      RowStage H L i P G S ρ (r := r) (l := l) u (fun x p => rowCruise (ctrl x p) o) from
    bound _ fun _ => id
  intro o
  induction o with
  | nil =>
    intro _ f
    exact Strip.Breeze.launch (Drive.self st.1 (cloth_size _ _ st f z)) (Spindle.belly _ hρ)
  | cons t ts ih =>
    intro allowed
    have et := allowed t List.mem_cons_self
    have ht : t.shift = 1 ∨ t.shift = -1 := by
      simp only [Packed.order, List.mem_cons, List.not_mem_nil, or_false] at et
      rcases et with h|h|h|h|h|h|h|h <;> subst t <;> decide
    simp_rw [rowCruise_cons]
    exact composeRows H L i P G S ρ u z st
      (rowWalkStage H L i shape extentReady t ht P G S ρ u hP hG hS guard sw hρ z ctrl hc)
      (ih fun t ha => allowed t (List.mem_cons_of_mem _ ha))

end
end Controlled

end NearSquareRoot
end Computability
end OAI
