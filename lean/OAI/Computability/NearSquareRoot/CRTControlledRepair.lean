import OAI.Computability.NearSquareRoot.CRTControlledRotate

/-! # Sparse tape repair for two chunks with an external control

Each addressed record is a pair of chunks. The control word is read from the current
row's descriptor. The sort compares full destination keys and only transports the
exceptional records, preserving all unmarked records.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Packed IntegerMultiplication.Strip
open IntegerMultiplication.Code IntegerMultiplication.Fix IntegerMultiplication.Loom
open IntegerMultiplication.Strip.Optic

noncomputable section

variable {X : Type} {r : Regime X} (H L i : X → ℕ)
variable (ctrl : (x : X) → Queue (H x) (L x) (i x))

abbrev rowSeries (x : X) := (Qt H L i x).cart (Qt H L i x)

private abbrev rows (x : X) := Row (H x) (L x) (i x)

/-- Stream the full key on each two-chunk address. The descriptor provides its
constant first component, and the ordinary lexicographic scans provide the other two. -/
theorem rowKeys (hc : r.Has (tally ∘ extent H L i)) (hx : r.Has fun x => badge (ctrl x)) :
    Strip.Trace r (rowSeries H L i) (fun x yz => send (names (ctrl x,yz))) := by
  let qr := initiative H L i hc
  let rs := rowSeries H L i
  let label (x : X) (yz : rows H L i x) := send (badge yz.1,badge yz.2)
  have t : Strip.Trace r rs label := qr.product qr
  apply t.tune
  let rt := onboard r label t.meter
  have a : rt.Has (fun z : Sigma (rows H L i) => badge (ctrl z.1)) :=
    onboard_small label t.meter (send ∘ _) hx
  have b : rt.Has (fun z : Sigma (rows H L i) => (badge z.2.1,badge z.2.2)) :=
    onboard_hat label t.meter
  exact a.pair b

attribute [local irreducible] repair rowRepair

set_option synthInstance.maxSize 1000

private theorem cancelRate {w k n t b : ℕ} (h : w*b ≤ n*t) (u : k*n ≤ w)
    (hw : 0 < w) : k*b ≤ t := by
  apply le_of_mul_le_mul_left (a := w) _ hw
  calc
    w * (k*b) = k * (w*b) := by ring
    _ ≤ k * (n*t) := Nat.mul_le_mul_left _ h
    _ ≤ w*t := by rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ u

/-- Apply the row repair on a selected two-chunk coordinate of a larger layout.
The stable-sort machine keeps spectator coordinates in their original order. -/
theorem repairRowFile (hc : r.Has (tally ∘ extent H L i))
    (hs : r.Has fun x => signs (H x) (L x) (i x))
    (sparse : ∀ x, (3 * extent H L i x + 1) * (32 * i x) ≤ 2 ^ width (H x) (L x))
    {O B : X → Type} [(x : X) → Fintype (O x)] [(x : X) → DecidableEq (O x)]
    [(x : X) → Fintype (B x)] [(x : X) → DecidableEq (Row (H x) (L x) (i x))]
    {s : (x : X) → Series (O x)} {b : (x : X) → Series (B x)}
    (g : (x : X) → File (s x) (Row (H x) (L x) (i x)) (b x))
    (tags : Strip.Trace r s (fun x yz => send (names (ctrl x, slot (g x) yz))))
    {l : X → ℕ} (f : (x : X) → O x → Tree) (vol : Manifest O l f) :
    Fleet r l s s f (fun x => travel (field (g x).focus (rowRepair (ctrl x))) (f x)) := by
  let key (x : X) (yz : Row (H x) (L x) (i x)) := emblem (names (ctrl x,yz))
  let bad (x : X) (yz : Row (H x) (L x) (i x)) := spotted (ctrl x,yz)
  let tag (x : X) (yz : O x) := send (names (ctrl x,slot (g x) yz))
  let rt := onboard r tag tags.meter
  let V (z : Sigma O) := (ctrl z.1,slot (g z.1) z.2)
  have v : rt.Has fun z : Sigma O => names (V z) := onboard_hat tag tags.meter
  have h : rt.Has (fun z : Sigma O => signs (H z.1) (L z.1) (i z.1)) :=
    onboard_small tag tags.meter (send ∘ _) hs
  have dst : Strip.Trace r s (fun x yz => send (sheet (g x) (bad x) (key x ∘ rowRepair (ctrl x)) yz)) := by
    apply tags.tune
    change rt.Has (fun z : Sigma O => (spotted (V z),
      emblem (names (ctrl z.1,rowRepair (ctrl z.1) (slot (g z.1) z.2)))))
    simp_rw [rowRepair_packed]
    exact send0 h V v
  have src : Strip.Trace r s (fun x yz => send (sheet (g x) (bad x) (key x) yz)) :=
    tags.tune (send1 h V v)
  have st := tags.valid
  have hv := vol.lives st
  have fetch := Drive.fetch st.1 hv
  obtain ⟨C, c⟩ := vol.size
  let : (x : X) → Fintype (Row (H x) (L x) (i x)) := fun _ => inferInstance
  refine Palace g (fun x => rowRepair (ctrl x)) bad key
    (fun x _ _ hk => congrArg Prod.snd (identify hk))
    f (fun x => rowRepair_fixed (ctrl x))
    (d := fun x => 3 * extent H L i x) (fun x yz => size_key (ctrl x,yz))
    (Drive.self st.1 hv) (fetch.chain (dst.offer.monoSize (fun _ => le_rfl) (fun _ => Nat.zero_le _)))
    (fetch.chain (src.offer.monoSize (fun _ => le_rfl) (fun _ => Nat.zero_le _)))
    (fun _ => le_rfl) ?_ C c ?_
  · have hsize : Dom r.scale (extent H L i) :=
      (Regime.Small.extent (k := fun x => send (tally (extent H L i x))) hc).mono
        (fun x => by change _ ≤ size (tally _); rw [size_tally,tally_length]; omega)
    exact (Dom.const _ 3).mul hsize
  · refine ⟨1, fun x => ?_⟩
    rw [one_mul]
    exact cancelRate (row_spotted_rate (ctrl x)) (sparse x) (by positivity)

/-- P192's radix-sort repair specialized to a pair of contiguous chunks. -/
theorem repairRow (hc : r.Has (tally ∘ extent H L i)) (hx : r.Has fun x => badge (ctrl x))
    (hs : r.Has fun x => signs (H x) (L x) (i x))
    (sparse : ∀ x, (3 * extent H L i x + 1) * (32 * i x) ≤ 2 ^ width (H x) (L x))
    {l : X → ℕ} {U : X → Type} (u : (x : X) → Series (U x))
    (z : ∀ x, (u x).count ≤ l x)
    (f : (x : X) → Row (H x) (L x) (i x) → U x → Bead) :
    let s := rowSeries H L i
    Drive r (fun x => (s x).count) l (cloth s u f)
      (cloth s u (fun x => travel (rowRepair (ctrl x)) (f x))) := by
  classical
  let D := rows H L i
  let : (x : X) → Fintype (D x) := fun _ => inferInstanceAs (Fintype (Row _ _ _))
  let : (x : X) → DecidableEq (D x) := fun _ => Classical.decEq _
  let : (x : X) → Fintype ((fun _ : X => Unit) x) := fun _ => inferInstance
  exact repairRowFile H L i ctrl hc hs sparse (fun x => File.look (rowSeries H L i x))
    (rowKeys H L i ctrl hc hx) (fun x yz => strip (u x) (f x yz)) (visible u f z)


private def window {G S Q : Type} [DecidableEq Q] (q : Series Q) (g : Series G) (s : Series S) :
    File (q.cart (g.cart (q.cart s))) (Q × Q)
      (Series.one.cart (g.cart (Series.one.cart s))) :=
  let f := (File.look q).unite ((File.shade g).unite ((File.look q).unite (File.shade s)))
  f.selectCongr {
    toFun a := (a.1,a.2.2.1)
    invFun a := (a.1,(),a.2,())
    left_inv _ := rfl
    right_inv _ := rfl }

open Fleet in
private theorem repairSpan {G S : X → Type} [(x : X) → Fintype (G x)] [(x : X) → Fintype (S x)]
    (g : (x : X) → Series (G x)) (s : (x : X) → Series (S x))
    (hg : Station r g) (hs : Station r s)
    (hc : r.Has (tally ∘ extent H L i)) (hx : r.Has fun x => badge (ctrl x))
    (shape : r.Has fun x => signs (H x) (L x) (i x))
    (sparse : ∀ x, (3 * extent H L i x + 1) * (32 * i x) ≤ 2 ^ width (H x) (L x))
    {l : X → ℕ}
    (f : (x : X) → Queue (H x) (L x) (i x) × G x × Queue (H x) (L x) (i x) × S x → Tree)
    (vol : Manifest _ l f) :
    let q := Qt H L i
    let t := cartS q (cartS g (cartS q s))
    Fleet r l t t f (fun x a => let yz := (rowRepair (ctrl x)).symm (a.1,a.2.2.1)
                                f x (yz.1,a.2.1,yz.2,a.2.2.2)) := by
  classical
  let Q x := Queue (H x) (L x) (i x)
  let O x := Q x × G x × Q x × S x
  let B x := Unit × G x × Unit × S x
  let q := Qt H L i
  let t := cartS q (cartS g (cartS q s))
  let : (x : X) → Fintype (O x) := fun _ => inferInstanceAs (Fintype (_ × _ × _ × _))
  let : (x : X) → Fintype (B x) := fun _ => inferInstanceAs (Fintype (_ × _ × _ × _))
  let : (x : X) → DecidableEq (O x) := fun _ => Classical.decEq _
  let : (x : X) → DecidableEq (Q x) := fun _ => Classical.decEq _
  let : (x : X) → DecidableEq (Row (H x) (L x) (i x)) := fun x => inferInstanceAs (DecidableEq (Q x × Q x))
  let labels (x : X) (a : O x) := send (badge a.1, false, badge a.2.2.1, false)
  have z := initiative H L i hc
  have trace : Strip.Trace r t labels :=
    z.product ((Strip.Trace.always hg (send false)).product (z.product (Strip.Trace.always hs (send false))))
  apply repairRowFile H L i ctrl hc shape sparse (fun x => window (q x) (g x) (s x)) _ f vol
  apply trace.tune
  let rt := onboard r labels trace.meter
  have c : rt.Has (fun z : Sigma O => badge (ctrl z.1)) := onboard_small labels trace.meter (send ∘ _) hx
  have v : rt.Has (fun z : Sigma O => (badge z.2.1,false,badge z.2.2.2.1,false)) := onboard_hat labels trace.meter
  exact c.pair (v.ez (f := fun (a : Adic.Raw 2 × Bool × Adic.Raw 2 × Bool) => (a.1,a.2.2.1)) (by fun_prop))

open Dims

variable {l : X → ℕ} (P G S : X → Tape) (ρ : ℝ)
variable {U : X → Type} (u : (x : X) → Series (U x))
variable (c : (x : X) → Pin (P x) → Queue (H x) (L x) (i x))

/-- Charge a radix repair independently at each prefix, with the two active
chunks separated or followed by any stationary spectator fields. -/
theorem rowRepairStage (hc : r.Has (tally ∘ extent H L i))
    (shape : r.Has fun x => signs (H x) (L x) (i x))
    (sparse : ∀ x, (3 * extent H L i x + 1) * (32 * i x) ≤ 2 ^ width (H x) (L x))
    (hg : Station r (fun x => layout (G x))) (hs : Station r (fun x => layout (S x)))
    (ready : Strip.Trace r (fun x => layout (P x)) (fun x p => send (badge (c x p))))
    (z : ∀ x, (u x).count ≤ l x) (hr : 0 ≤ ρ) :
    RowStage H L i P G S ρ (r := r) (l := l) u (fun x p => rowRepair (c x p)) := by
  intro f
  apply Strip.Breeze.launch _ (Spindle.belly _ hr)
  let Y := Sigma (fun x => Pin (P x))
  let header (x : X) (p : Pin (P x)) := send (badge (c x p))
  let rr := onboard r header ready.meter
  have hq := (initiative H L i hc).valid
  have vol := visible u f z
  apply Fleet.guide ready.valid (hq.product (hg.product (hq.product hs))) vol header ready.meter
    (ready.offer.monoSize (fun _ => le_rfl) (fun _ => Nat.zero_le _))
  let : (y : Y) → Fintype (Pin (G y.1)) := fun _ => inferInstance
  let : (y : Y) → Fintype (Pin (S y.1)) := fun _ => inferInstance
  have lift {F : Type} [Codec F] {v : X → F} (h : r.Has v) : rr.Has (fun y : Y => v y.1) :=
    onboard_small header ready.meter (send ∘ v) h
  exact repairSpan (r := rr) (fun y => H y.1) (fun y => L y.1) (fun y => i y.1)
    (fun y => c y.1 y.2) (fun y => layout (G y.1)) (fun y => layout (S y.1))
    (hg.adapt header ready.meter _) (hs.adapt header ready.meter _)
    (lift hc) (onboard_hat header ready.meter) (lift shape) (fun y => sparse y.1) _
    (Manifest.localize (s := fun x p a => strip (u x) (f x (p,a))) vol)


/-- The complete controlled row permutation, including the eight guarded rotations
and the stable radix-sort repair. -/
theorem rowIdealStage (hc : r.Has (tally ∘ extent H L i))
    (shape : r.Has fun x => signs (H x) (L x) (i x))
    (sparse : ∀ x, (3 * extent H L i x + 1) * (32 * i x) ≤ 2 ^ width (H x) (L x))
    (hp : Told r P) (hg : Told r G) (hs : Told r S)
    (guard : ∀ x j, j ∈ P x ++ G x ++ S x → j ≤ Net.Shuttle.base)
    (sw : RectInterchange r (extent H L i) ρ)
    (ready : Strip.Trace r (fun x => layout (P x)) (fun x p => send (badge (c x p))))
    (z : ∀ x, (u x).count ≤ l x) (hr : 0 ≤ ρ) :
    RowStage H L i P G S ρ (r := r) (l := l) u (fun x p => rowIdeal (c x p)) := by
  have st := rotationStation H L i hc P G S hp hg hs
  have cruise := rowCruiseStage H L i shape hc P G S ρ u hp hg hs guard sw hr z c ready
  have repair := rowRepairStage H L i P G S ρ u c hc shape sparse hg.station hs.station ready z hr
  simpa only [rowRepaired] using composeRows H L i P G S ρ u z st cruise repair

end
end Controlled

end NearSquareRoot
end Computability
end OAI
