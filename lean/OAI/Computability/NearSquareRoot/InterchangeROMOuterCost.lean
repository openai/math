import OAI.Computability.NearSquareRoot.InterchangeROMStarsStage
import OAI.Computability.NearSquareRoot.InterchangeROMOuterHeader
import OAI.Computability.NearSquareRoot.InterchangeROMFrontNode

/-! # Local work of the native outer interchange stage

The bank, the main cubic swap, the inverse bank and the reserve calls may use
different polynomial degrees. Choosing their maximum does not multiply the
coefficient of any recursive call. The enclosing header moves and the three
command joins are charged as local work.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter

open IntegerMultiplication IntegerMultiplication.Code NearSquareRoot.InterchangeAddress
  NearSquareRoot.InterchangeROMRecursion NearSquareRoot.InterchangeROMExpose

/-- Raise the local polynomial degree while preserving the coefficient. -/
theorem localMass_mono {b : ℕ} (q : Request b) {k j : ℕ} (h : k ≤ j) :
    localMass q k ≤ localMass q j :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_left
    (Nat.pow_le_pow_right (by omega : 0 < q.header.count + 1) h) _)

/-- One unit of local mass covers each row even at degree zero. -/
theorem rows_le_localMass {b : ℕ} (q : Request b) (k : ℕ) : q.rows.count ≤ localMass q k := by
  have h := Nat.one_le_pow k (q.header.count + 1) (by omega)
  exact Nat.le_mul_of_pos_right _ (by omega)

/-- Common degree for the bank, cubic, inverse bank and stars, in order. -/
def stageDegree (kb kc ku ks : ℕ) := max (max kb kc) (max ku ks)

theorem computable_stageDegree {P : Type} [Primcodable P] {kb kc ku ks : P → ℕ}
    (hb : Computable kb) (hc : Computable kc) (hu : Computable ku) (hs : Computable ks) :
    Computable (fun p => stageDegree (kb p) (kc p) (ku p) (ks p)) :=
  Primrec.nat_max.to_comp.comp (Primrec.nat_max.to_comp.comp hb hc)
    (Primrec.nat_max.to_comp.comp hu hs)

/-- Local coefficients add. The parked header costs 100 steps per tree node
including one unit of overhead, and each of three joins costs two steps. -/
def stageRate (bank core unbank stars header : ℕ) :=
  bank + core + unbank + stars + 100*(header+1) + 6

theorem computable_stageRate {P : Type} [Primcodable P] {B C U S H : P → ℕ}
    (hb : Computable B) (hc : Computable C) (hu : Computable U) (hs : Computable S)
    (hh : Computable H) :
    Computable (fun p => stageRate (B p) (C p) (U p) (S p) (H p)) :=
  Primrec.nat_add.to_comp.comp
    (Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp hb hc) hu) hs)
      (Primrec.nat_mul.to_comp.comp (.const 100) (Primrec.succ.to_comp.comp hh))) (.const 6)

/-- Aggregate a composed native sequence, retaining its literal join order and
the exact move-under-header charge. The header bound is measured in parent rows.
This inequality applies directly in the work argument of `At.mono`. -/
theorem stage_work_le {b : ℕ} (q : Request b) (h : Tree)
    {bank core unbank stars B C U S H kb kc ku ks : ℕ}
    (hb : bank ≤ B*(localMass q kb+1)) (hc : core ≤ C*(localMass q kc+1))
    (hu : unbank ≤ U*(localMass q ku+1)) (hs : stars ≤ S*(localMass q ks+1))
    (hh : h.count ≤ H*q.rows.count) :
    bank + (core+100*(h.count+1)) + 2 + unbank + 2 + stars + 2 ≤
      stageRate B C U S H*(localMass q (stageDegree kb kc ku ks)+1) := by
  let k := stageDegree kb kc ku ks
  let M := localMass q k + 1
  have lift {x A j : ℕ} (hx : x ≤ A*(localMass q j+1)) (hj : j ≤ k) : x ≤ A*M :=
    hx.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ (localMass_mono q hj)))
  have hb' := lift hb ((Nat.le_max_left kb kc).trans (Nat.le_max_left ..))
  have hc' := lift hc ((Nat.le_max_right kb kc).trans (Nat.le_max_left ..))
  have hu' := lift hu ((Nat.le_max_left ku ks).trans (Nat.le_max_right ..))
  have hs' := lift hs ((Nat.le_max_right ku ks).trans (Nat.le_max_right ..))
  have hM : 1 ≤ M := Nat.succ_le_succ (Nat.zero_le _)
  have rows : q.rows.count ≤ M := (rows_le_localMass q k).trans (Nat.le_succ _)
  have hh' := hh.trans (Nat.mul_le_mul_left H rows)
  change _ ≤ (B+C+U+S+100*(H+1)+6)*M
  simp only [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  omega

/-- Coefficient for the native body at an epoch. The reserve-stage coefficient
uses the size of a physical record of digits modulo `p+1`. -/
def bodyRate (A k b a m p B C U : ℕ) := stageRate B C U
  (InterchangeROMStars.coefficient A k b a m (2*(p+1)+3)) (header_coefficient b (a+m+a))

theorem computable_bodyRate {P : Type} [Primcodable P] {b a m p B C U : P → ℕ} (A k : ℕ)
    (hb : Computable b) (ha : Computable a) (hm : Computable m) (hp : Computable p)
    (hB : Computable B) (hC : Computable C) (hU : Computable U) :
    Computable (fun x => bodyRate A k (b x) (a x) (m x) (p x) (B x) (C x) (U x)) := by
  have hcell : Computable (fun x => 2*(p x+1)+3) :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (.const 2) (Primrec.succ.to_comp.comp hp)) (.const 3)
  exact computable_stageRate hB hC hU (InterchangeROMStars.computable_coefficient A k hb ha hm hcell)
    (computable_header_coefficient b (fun x => a x+m x+a x))

/-- The literal clock returned by the native body's composition theorem. Given
the three component bounds for its entry, middle and exit, the cost of both
header moves, every reserve call's local overhead, and all joins is covered by
the computable template coefficient above. -/
theorem body_work_le {b a m : ℕ} (q : Request b) (hb : 2 ≤ b) (hn : 0 < a+m+a)
    (hw : a+m+a < q.width) (ok : q.Admissible) (A k p : ℕ)
    {entry middle exitTime B C U kb kc ku : ℕ}
    (he : entry ≤ B*(localMass q kb+1)) (hc : middle ≤ C*(localMass q kc+1))
    (hu : exitTime ≤ U*(localMass q ku+1)) :
    let i := InterchangeROMStars.frame a m q hb hn hw ok
    let tag := send (centerHeader i)
    entry+(middle+100*(tag.count+1))+2+exitTime+2+
      InterchangeROMStars.coefficient A k b a m (2*(p+1)+3)*(localMass q k+1)+2 ≤
      bodyRate A k b a m p B C U*(localMass q (stageDegree kb kc ku k)+1) := by
  let i := InterchangeROMStars.frame a m q hb hn hw ok
  exact stage_work_le q (send (centerHeader i)) he hc hu le_rfl (center_count i)

/-- The selected body's polynomial degree is independent of the header
preparation degree. Their two coefficients add at the larger degree. -/
theorem add_work_le {b : ℕ} (q : Request b) {left right A B i j : ℕ}
    (hl : left ≤ A*(localMass q i+1)) (hr : right ≤ B*(localMass q j+1)) :
    left + right ≤ (A+B)*(localMass q (max i j)+1) := by
  rw [Nat.add_mul]
  exact Nat.add_le_add
    (hl.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ (localMass_mono q (Nat.le_max_left ..)))))
    (hr.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ (localMass_mono q (Nat.le_max_right ..)))))

/-- One computable coefficient for the node's front end followed by its
actual staged body. The modulus is `p+1` and the exposed lane count is `a+m+a`. -/
def nodeRate (F : InterchangeROMFront.Core) (A k b a m p B C U : ℕ) :=
  InterchangeROMFront.rate F (p+1) b (a+m+a) + bodyRate A k b a m p B C U

theorem computable_nodeRate (F : InterchangeROMFront.Core) (A k : ℕ) {P : Type} [Primcodable P]
    {b a m p B C U : P → ℕ} (hb : Computable b) (ha : Computable a) (hm : Computable m)
    (hp : Computable p) (hB : Computable B) (hC : Computable C) (hU : Computable U) :
    Computable (fun x => nodeRate F A k (b x) (a x) (m x) (p x) (B x) (C x) (U x)) :=
  Primrec.nat_add.to_comp.comp
    (InterchangeROMFront.computable_rate F (Primrec.succ.to_comp.comp hp) hb
      (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp ha hm) ha))
    (computable_bodyRate A k hb ha hm hp hB hC hU)

theorem computable_nodeDegree (F : InterchangeROMFront.Core) {P : Type} [Primcodable P]
    {kb kc ku ks : P → ℕ} (hb : Computable kb) (hc : Computable kc)
    (hu : Computable ku) (hs : Computable ks) :
    Computable (fun x => max (F.degree+1) (stageDegree (kb x) (kc x) (ku x) (ks x))) :=
  Primrec.nat_max.to_comp.comp (.const (F.degree+1)) (computable_stageDegree hb hc hu hs)

/-- Price the exact sum emitted by the native front-end wrapper. -/
theorem node_work_le (F : InterchangeROMFront.Core) {b : ℕ} (q : Request b)
    (A k a m p B C U kb kc ku : ℕ) {work : ℕ}
    (hw : work ≤ bodyRate A k b a m p B C U*(localMass q (stageDegree kb kc ku k)+1)) :
    InterchangeROMFront.rate F (p+1) b (a+m+a)*localMass q (F.degree+1) + work ≤
      nodeRate F A k b a m p B C U*(localMass q (max (F.degree+1) (stageDegree kb kc ku k))+1) :=
  add_work_le q (Nat.mul_le_mul_left _ (Nat.le_succ _)) hw

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
