import OAI.LinearAlgebra.MatrixExponent.Processor.Skip
import OAI.LinearAlgebra.MatrixExponent.Processor.DispatchSize
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels
import OAI.LinearAlgebra.MatrixExponent.Processor.Guard
import OAI.LinearAlgebra.MatrixExponent.Processor.Capacity

/-!
# Numbering encoded records

A static partition names each record by a key and a row number.
The two endpoints and number of transmitted bits may depend on the
public report, but are shared by all rows with a given key.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Diagonal Classical Finset
variable {R : ℕ} {E J : Type} {src dst : E → Fin R} {size : E → ℕ}

structure Records (E J : Type) where
  length : J → ℕ
  row : E ≃ (Σ j, Fin (length j))

namespace Records

variable (p : Records E J)

def key (e : E) := (p.row e).1
def index (e : E) := (p.row e).2.val

theorem index_lt (e : E) : p.index e < p.length (p.key e) := (p.row e).2.isLt

private theorem unique {e e' : E} (h : p.key e = p.key e') (hi : p.index e = p.index e') :
    e = e' := by
  apply p.row.injective
  unfold key at h
  unfold index at hi
  generalize p.row e = a, p.row e' = b at *
  rcases a with ⟨a, i⟩
  rcases b with ⟨b, j⟩
  change a = b at h
  subst b
  rw [show i = j from Fin.ext hi]

structure Routing (src dst : E → Fin R) (size : E → ℕ) where
  fromKey : J → Fin R
  toKey : J → Fin R
  bits : J → ℕ
  atSrc : ∀ e, fromKey (p.key e) = src e
  atDst : ∀ e, toKey (p.key e) = dst e
  atSize : ∀ e, bits (p.key e) = size e

namespace Routing
variable {p} (s : p.Routing src dst size)

def width (j : J) := if s.fromKey j = s.toKey j then 0 else p.length j * s.bits j

def digit (e : Encoded.Bits src dst size) := p.index e.1.val * size e.1.val + e.2.val

private def label (e : Encoded.Bits src dst size) : Σ j, Fin (s.width j) :=
  ⟨p.key e.1.val, ⟨digit (p := p) e, by
    rw [width, s.atSrc, s.atDst, ite_eq_right e.1.property, s.atSize]
    exact (Nat.add_lt_add_left e.2.isLt _).trans_le (by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (p.index_lt _))⟩⟩

private theorem digit_unique {u v a b w : ℕ} (ha : a < w) (hb : b < w)
    (he : u * w + a = v * w + b) : u = v ∧ a = b := by
  have h : a = b := by
    have hh := congrArg (fun x => x % w) he
    simpa [Nat.add_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hh
  refine ⟨Nat.eq_of_mul_eq_mul_right (by omega : 0 < w) (by omega), h⟩

private theorem label_injective : Function.Injective s.label := by
  rintro ⟨⟨e, he⟩, i⟩ ⟨⟨f, hf⟩, j⟩ h
  have hk := congrArg Sigma.fst h
  change p.key e = p.key f at hk
  have hw : size e = size f := by rw [← s.atSize, ← s.atSize, hk]
  have hn := congrArg (fun z => z.2.val) h
  change p.index e * size e + i.val = p.index f * size f + j.val at hn
  obtain ⟨hl, hj⟩ := digit_unique i.isLt (j.isLt.trans_eq hw.symm) (by simpa only [hw] using hn)
  have heq := p.unique hk hl
  subst f
  rw [show i = j from Fin.ext hj]

variable [Fintype E] [Fintype J]

private theorem same_count :
    Fintype.card (Encoded.Bits src dst size) = Fintype.card (Σ j, Fin (s.width j)) := by
  simp only [Encoded.Bits, Fintype.card_sigma, Fintype.card_fin]
  rw [← sum_subtype (univ.filter (fun i => src i ≠ dst i))
    (p := fun e => src e ≠ dst e) (by simp) size, sum_filter]
  simp_rw [← s.atSrc, ← s.atDst, ← s.atSize]
  rw [← p.row.symm.sum_comp, Fintype.sum_sigma]
  unfold key
  simp only [Equiv.apply_symm_apply]
  apply sum_congr rfl
  intro j _
  by_cases he : s.fromKey j = s.toKey j <;> simp [width, he]

def channels : Channels (Encoded.left src dst size) (Encoded.right src dst size) J where
  width := s.width
  left := s.fromKey
  right := s.toKey
  label := Equiv.ofBijective s.label ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨s.label_injective, s.same_count⟩)
  src_eq _ := (s.atSrc _).symm
  dst_eq _ := (s.atDst _).symm

theorem channels_index (e : Encoded.Bits src dst size) :
    (s.channels.label e).2.val = p.index e.1.val * size e.1.val + e.2.val := rfl

theorem channels_key (e : Encoded.Bits src dst size) :
    (s.channels.label e).1 = p.key e.1.val := rfl

end Routing
end Records
end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-! # Computing group membership and channel lengths from the public report -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
open Classical Processor Install Finset
variable {F : Type} [Field F] {n h r d : ℕ} (A : Expansion F n h)

def chargeBits (i : Fin n) (z : A.I) := A.cross z i + Nat.clog 2 (Fintype.card A.I)

def mass (i : Fin n) (g : Fin r) : Form (Class r × A.I) :=
  ⟨fun z => 256 * ((if z.1.1 = g then A.chargeBits i z.2 else 0) +
    (if z.1.2.1 = g then A.chargeBits i z.2 else 0)), 0⟩

def groupFlags (N : ℕ) (i : Fin n) (x : A.CountBit r d → Bool) (g : Fin r) :=
  decide (N < (A.mass i g).value x)

theorem groupFlags_report (N : ℕ) (R : A.Report r d) (g : Fin r) :
    A.groupFlags N R.1 (A.countBits R) g = true ↔ g ∈ A.reportGroups N R := by
  have he (z : Class r × A.I) : number (fun i => A.countBits R (z, i)) = (R.2 z).val :=
    A.cnt_countBits R z
  simp only [groupFlags, decide_eq_true_eq, mass, Form.value, linear, add_zero, he,
    reportGroups, mem_filter, mem_univ, true_and, total, chargeBits, mul_sum, mul_left_comm]

def classForm (i : Fin n) (c : Class r) : Form (Class r × A.I) :=
  ⟨fun z => if z.1 = c then A.chargeBits i z.2 else 0, 0⟩

theorem classForm_report (R : A.Report r d) (c : Class r) :
    (A.classForm R.1 c).value (A.countBits R) = A.classWidth R c := by
  have he (z : Class r × A.I) : number (fun i => A.countBits R (z, i)) = (R.2 z).val :=
    A.cnt_countBits R z
  simp only [classForm, Form.value, linear, add_zero, he]
  rw [Fintype.sum_prod_type, sum_comm]
  simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true, chargeBits, classWidth]

def flagCost (r d w : ℕ) := (1 + r) * 100000 * (1 + Fintype.card (A.CountBit r d)) * (1 + w)

theorem groupFlags_net {N w M : ℕ} (i : Fin n)
    (hc : ∀ z, A.chargeBits i z ≤ M) (hN : N < 2 ^ w)
    (hv : Fintype.card (Class r × A.I) * (2 ^ registerWidth n r d * (512 * M)) < 2 ^ w) :
    BNet F (A.groupFlags (d := d) (r := r) N i) (A.flagCost r d w) := by
  let n₀ : Form (Class r × A.I) := ⟨fun _ => 0, N⟩
  have hn (x : A.CountBit r d → Bool) : n₀.value x = N := by simp [n₀, Form.value, linear]
  have hm (g : Fin r) (x : A.CountBit r d → Bool) : (A.mass i g).value x < 2 ^ w := by
    apply lt_of_le_of_lt _ hv
    apply linear_le
    intro z
    have h := hc z.2
    simp only [mass]
    split_ifs <;> omega
  let k := 90000 * (1 + Fintype.card (A.CountBit r d)) * (1 + w)
  have hg (g : Fin r) : BNet F (fun (x : A.CountBit r d → Bool) (_ : Unit) =>
      A.groupFlags N i x g) k := by
    have he := n₀.compare F (A.mass i g) w (registerWidth n r d) (fun x => by rwa [hn]) (hm g)
    simp only [hn] at he
    unfold k
    rw [Fintype.card_prod, Fintype.card_fin]
    exact he
  have hp := (BNet.collect _ hg).rename (.refl _) (Equiv.prodUnique _ Unit)
  apply hp.mono
  rw [Fintype.card_fin]
  unfold k flagCost
  ring_nf
  omega

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end

/-!
# Fixed classes of processor symbols

The only classes with variable-length rows are the singleton selector
classes. Literal rows use a numbering that is independent of the
processor. Slot rows use the packet repetition and bit index.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Diagonal Spectral Classical
namespace Records

variable {A B I J : Type}

def partition [Fintype A] [DecidableEq I] (f : A → I) : Records A I where
  length i := multiplicity f i
  row := (Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight (fun _ => Fintype.equivFin _))

def indexed (p : Records A I) (J : Type) : Records (J × A) (J × I) where
  length t := p.length t.2
  row :=
    ((Equiv.refl J).prodCongr p.row).trans
      ⟨fun t => ⟨(t.1, t.2.1), t.2.2⟩, fun q => (q.1.1, ⟨q.1.2, q.2⟩), fun _ => rfl, fun _ => rfl⟩

def union (p : Records A I) (q : Records B J) : Records (A ⊕ B) (I ⊕ J) where
  length := Sum.elim p.length q.length
  row := (p.row.sumCongr q.row).trans
    (Equiv.sumSigmaDistrib (fun k => Fin (Sum.elim p.length q.length k))).symm

def uniform {w : ℕ} (e : A ≃ I × Fin w) : Records A I where
  length _ := w
  row := e.trans (Equiv.sigmaEquivProd _ _).symm

end Records

abbrev Name (n r : ℕ) := ((Fin (3 * r) × Label n r) ⊕ Label n r) ⊕
  (Template n r × Cube n × Bool) ⊕ Class r

variable {F : Type} [Field F] {N l n r h t : ℕ}

private def slotRows : Position n r t h × Bool ≃ (Template n r × Cube n × Bool) × Fin (t * h) where
  toFun a := ((a.1.1.1, a.1.2.1, a.2), finProdFinEquiv (a.1.1.2, a.1.2.2))
  invFun p := (((p.1.1, (finProdFinEquiv.symm p.2).1), p.1.2.1, (finProdFinEquiv.symm p.2).2), p.1.2.2)
  left_inv _ := by simp only [Equiv.symm_apply_apply]
  right_inv _ := by simp only [Prod.mk.eta, Equiv.apply_symm_apply]

variable (fa : Machine.Ports N l l → Label n r)

def records (h t : ℕ) : Records (Pin N l l r ⊕ Expansion.Edge n r t h) (Name n r) :=
  let lit := (Records.partition (fun i => fa (.inl i))).indexed (Fin (3 * r))
  let privatePins := Records.partition (fun q => fa (Pin.position (.inr q)))
  let pos := Records.uniform (slotRows (n := n) (r := r) (t := t) (h := h))
  let sel := Records.uniform (Equiv.prodUnique (Class r) (Fin 1)).symm
  (lit.union privatePins).union (pos.union sel)

theorem name_card (n r : ℕ) :
    Fintype.card (Name n r) = 3 * r * r ^ n + r ^ n + (r ^ n) ^ 2 * 2 ^ n * 2 + r ^ 3 := by
  simp [Name]
  ring

def descriptor (A : Expansion F n h) (hn : 2 ≤ n) (N : ℕ) (R : A.Report r t) :
    Name n r → Worker r × Worker r × ℕ
  | .inl (.inl (u, z)) => ((Worker.index r).symm u, A.owner hn N R z, 1)
  | .inl (.inr z) => (A.owner hn N R z, A.owner hn N R z, 1)
  | .inr (.inl (p, x, b)) =>
    let c := (group p R.1 false, group p R.1 true, group p (other hn R.1) false)
    let v := A.owner hn N R (corner p (if b then Cube.flip Finset.univ x else x))
    (v, if A.shared N R c then v else .packet c.2.2, 1)
  | .inr (.inr c) => (A.src hn N R (.inr c), A.dst hn N R (.inr c), A.classWidth R c)

def grouping (A : Expansion F n h) (hn : 2 ≤ n) (R : A.Report r t) :
    let f := A.owner hn N R ∘ fa
    (records fa h t).Routing (A.extraSrc hn N R (Worker.index r) (Pin.src f))
      (A.extraDst hn N R (Worker.index r) (Pin.dst f)) (A.extraSize R) where
  fromKey j := Worker.index r (descriptor A hn N R j).1
  toKey j := Worker.index r (descriptor A hn N R j).2.1
  bits j := (descriptor A hn N R j).2.2
  atSrc := by rintro ((⟨u, i⟩|q)|⟨p, x⟩|c) <;> rfl
  atDst := by rintro ((⟨u, i⟩|q)|⟨p, x⟩|c) <;> rfl
  atSize := by rintro ((⟨u, i⟩|q)|⟨p, x⟩|c) <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Processor
end

section
/-! # Endpoints from at most three group flags -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Install Diagonal Spectral
variable {n r : ℕ} (hn : 2 ≤ n) (i : Fin n) (mask : Fin r → Bool)

private def home (z : Label n r) : Worker r :=
  if mask (z i) then .station (z (other hn i)) else .home (z i)

def pairOf : Name n r → Worker r × Worker r
  | .inl (.inl (u, z)) => ((Worker.index r).symm u, home hn i mask z)
  | .inl (.inr z) => (home hn i mask z, home hn i mask z)
  | .inr (.inl (p, x, b)) =>
    let v := home hn i mask (corner p (if b then Cube.flip Finset.univ x else x))
    (v, if mask (p.1 i) = false ∧ mask (p.2 i) = false then v else .packet (p.1 (other hn i)))
  | .inr (.inr c) =>
    if mask c.1 = false ∧ mask c.2.1 = false then (.home c.1, .home c.2.1)
    else (.packet c.2.2, .packet c.2.2)

theorem support (k : Name n r) :
    ∃ S : Finset (Fin r), S.card ≤ 3 ∧ ∀ a b,
      (∀ j ∈ S, a j = b j) → pairOf hn i a k = pairOf hn i b k := by
  rcases k with (⟨u, z⟩|z)|⟨p, x, s⟩|c
  · exact ⟨{z i}, by simp, fun a b h => by simp only [pairOf, home, h (z i) (by simp)]⟩
  · exact ⟨{z i}, by simp, fun a b h => by simp only [pairOf, home, h (z i) (by simp)]⟩
  · let t := corner p (if s then Cube.flip Finset.univ x else x) i
    refine ⟨{t, p.1 i, p.2 i}, Finset.card_le_three, fun a b h => ?_⟩
    have ht := h t (by simp)
    unfold t at ht
    simp only [pairOf, home, ht, h (p.1 i) (by simp), h (p.2 i) (by simp)]
  · exact ⟨{c.1, c.2.1}, Finset.card_le_two.trans (by decide),
      fun a b h => by simp only [pairOf, h c.1 (by simp), h c.2.1 (by simp)]⟩

theorem endpoint_net (F : Type) [Field F] (k : Name n r) (f : Worker r × Worker r → Bool) :
    BNet F (fun t (_ : Unit) => f (pairOf hn i t k)) (r + 134) := by
  obtain ⟨S, hS, h⟩ := support hn i k
  have hd : Depends (fun t (_ : Unit) => f (pairOf hn i t k)) 3 :=
    fun _ => ⟨S, hS, fun x y he => congrArg f (h x y he)⟩
  simpa [localCost] using hd.bnet F

variable {F : Type} [Field F] {h d : ℕ} (A : Expansion F n h) (N : ℕ)

theorem pairOf_report (R : A.Report r d) (j : Name n r) :
    pairOf hn R.1 (A.groupFlags N R.1 (A.countBits R)) j =
      ((descriptor A hn N R j).1, (descriptor A hn N R j).2.1) := by
  have hf (g : Fin r) : A.groupFlags N R.1 (A.countBits R) g = false ↔ g ∉ A.reportGroups N R := by
    rw [← A.groupFlags_report]
    simp
  rcases j with (⟨u, z⟩|z)|⟨p, x, b⟩|c
  · simp only [pairOf, descriptor, home, Expansion.owner, A.groupFlags_report]
  · simp only [pairOf, descriptor, home, Expansion.owner, A.groupFlags_report]
  · simp only [pairOf, descriptor, home, Expansion.owner, A.groupFlags_report, hf, Expansion.shared,
      decide_eq_true_eq, group, Bool.false_eq_true, ite_false, ite_true]
  · simp only [pairOf, descriptor, Expansion.src, Expansion.dst, Expansion.shared, hf, decide_eq_true_eq]
    split <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-! # Computing prefix lengths for the relay schedule -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor
open Classical Diagonal Install

variable {F : Type} [Field F] {N l n h r d : ℕ}
  (A : Expansion F n h) (hn : 2 ≤ n) (fa : Machine.Ports N l l → Label n r)

private def selectLink (u v : Fin (3 * r)) (e : Worker r × Worker r) :=
  let a := Worker.index r e.1
  let b := Worker.index r e.2
  decide (a ≠ b ∧ (a = u ∧ b = v ∨ a = v ∧ b = u))

def capacity (d : ℕ) (i : Fin n) (p : Name n r) : Form (Class r × A.I) :=
  match p with
  | .inr (.inr c) => A.classForm i c
  | _ => ⟨fun _ => 0, (records fa h d).length p⟩

def bandwidth (i : Fin n) (p : Name n r) (u v : Fin (3 * r)) (x : A.CountBit r d → Bool) :=
  if selectLink u v (pairOf hn i (A.groupFlags N i x) p)
    then (capacity A fa d i p).value x else 0

private theorem capacity_eq (p : Name n r) (R : A.Report r d) :
    (capacity A fa d R.1 p).value (A.countBits R) =
      (records fa h d).length p * (descriptor A hn N R p).2.2 := by
  rcases p with (⟨u, z⟩|z)|⟨q, x, b⟩|c
  all_goals simp only [capacity, descriptor]
  · simp [Form.value, linear]
  · simp [Form.value, linear]
  · simp [Form.value, linear]
  · change _ = 1 * A.classWidth R c
    rw [one_mul, A.classForm_report]

theorem bandwidth_eq (p : Name n r) (R : A.Report r d) (u v : Fin (3 * r)) :
    bandwidth A hn fa R.1 p u v (A.countBits R) = (grouping fa A hn R).channels.widthAt u v p := by
  rw [bandwidth, pairOf_report, capacity_eq A hn fa]
  unfold Channels.widthAt selectLink
  let s := grouping fa A hn R
  let a := s.fromKey p
  let b := s.toKey p
  let W := (records fa h d).length p * s.bits p
  change (if decide (a ≠ b ∧ (a = u ∧ b = v ∨ a = v ∧ b = u)) then W else 0) =
    if a = u ∧ b = v ∨ a = v ∧ b = u then (if a = b then 0 else W) else 0
  by_cases he : a = b <;> simp [he]

variable {A hn fa} {v w : ℕ} {i : Fin n}

theorem bandwidth_net
    (hg : BNet F (A.groupFlags (r := r) (d := d) N i) v) (p : Name n r) (x y : Fin (3 * r)) :
    Register F w (bandwidth (d := d) A hn fa i p x y)
      (v + r + 50000 * (1 + Fintype.card (A.CountBit r d)) * (1 + w)) := by
  have he := hg.comp (endpoint_net hn i F p (selectLink x y))
  have hc := (capacity A fa d i p).net F w (Expansion.registerWidth n r d)
  apply (Register.mask he hc).mono
  have hw : Fintype.card (A.CountBit r d) = Fintype.card (Class r × A.I) * Expansion.registerWidth n r d :=
    (Fintype.card_prod _ _).trans (congrArg _ (Fintype.card_fin _))
  rw [← hw]
  ring_nf
  omega

end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-! # Computing every total and every starting position in the channel numbering -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor
open Classical Diagonal Install Finset

variable {F : Type} [Field F] {N l n h r d : ℕ} [ord : LinearOrder (Name n r)]
  (A : Expansion F n h) (hn : 2 ≤ n) (fa : Machine.Ports N l l → Label n r)

abbrev Query (n r : ℕ) := Fin (3 * r) × Fin (3 * r) × Option (Name n r)

def addressSum (i : Fin n) (p : Query n r) (x : A.CountBit r d → Bool) :=
  ∑ j, if p.2.2.elim True (@LT.lt _ ord.toLT j) then bandwidth A hn fa i j p.1 p.2.1 x else 0

theorem addressSum_total (R : A.Report r d) (u v : Fin (3 * r)) :
    addressSum A hn fa R.1 (u, v, none) (A.countBits R) =
      ∑ j, (grouping fa A hn R).channels.widthAt u v j := by
  simp only [addressSum, Option.elim_none, ite_true, bandwidth_eq]

theorem addressSum_start (R : A.Report r d) (u v : Fin (3 * r)) (p : Name n r) :
    addressSum A hn fa R.1 (u, v, some p) (A.countBits R) =
      start ((grouping fa A hn R).channels.widthAt u v) p := by
  simp only [addressSum, Option.elim_some, bandwidth_eq, start, sum_filter]

def addresses (w : ℕ) (i : Fin n) (x : A.CountBit r d → Bool)
    (j : Query n r × slots (word w)) := digits w (addressSum A hn fa i j.1 x) j.2

def addressCost (A : Expansion F n h) (r d w v : ℕ) :=
  Fintype.card (A.CountBit r d) + Fintype.card (Query n r) *
    (2 * Fintype.card (A.CountBit r d) + (1 + Fintype.card (Name n r)) *
      (v + r + 60000 * (1 + Fintype.card (A.CountBit r d)) * (1 + w)))

variable {A hn fa} {v w : ℕ} {i : Fin n}

theorem addresses_net (hg : BNet F (A.groupFlags (r := r) (d := d) N i) v) :
    BNet F (addresses (d := d) A hn fa w i) (addressCost A r d w v) := by
  let c := v + r + 50000 * (1 + Fintype.card (A.CountBit r d)) * (1 + w)
  have ht (p : Query n r) (j : Name n r) :
      Register F w (fun x => if p.2.2.elim True (@LT.lt _ ord.toLT j) then
        bandwidth (d := d) A hn fa i j p.1 p.2.1 x else 0) c := by
    by_cases he : p.2.2.elim True (@LT.lt _ ord.toLT j)
    · simp only [ite_eq_left he]
      exact bandwidth_net hg _ _ _
    · simp only [ite_eq_right he]
      refine (Register.const 0).mono ?_
      unfold c
      ring_nf
      omega
  have hp (p : Query n r) : Register F w (addressSum (d := d) A hn fa i p)
      ((1 + Fintype.card (Name n r)) * (v + r + 60000 * (1 + Fintype.card (A.CountBit r d)) * (1 + w))) := by
    refine (Register.sum _ (ht p)).mono (Nat.mul_le_mul_left _ ?_)
    unfold c
    ring_nf
    omega
  exact BNet.collect _ hp

end OAI.LinearAlgebra.MatrixExponent.Processor
end

section
/-! # Uniform size bounds for all pair lengths and channel offsets -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor
open Diagonal Install

variable {F : Type} [Field F] {N l n h r d w : ℕ} (A : Expansion F n h)

private theorem address_bound (hn : 2 ≤ n) (hw : 100000000 ≤ w)
    (hr : 0 < r) (hc : 2 ^ n ≤ w) (hI : Fintype.card A.I ≤ w)
    (hd : Expansion.registerWidth n r d ≤ w * 8) :
    addressCost A r d w (A.flagCost r d (w * 14)) ≤ r ^ (16 * n) * w ^ 48 := by
  let T := r ^ (2 * n) * w ^ 6
  have hp (i : ℕ) (hi : i ≤ 2 * n) : r ^ i ≤ r ^ (2 * n) := Nat.pow_le_pow_right hr hi
  have hrr : 1 ≤ r ^ (2 * n) := by simpa using hp 0 (by omega)
  have ht : 4 ≤ T := le_trans (show 4 ≤ w ^ 6 from le_trans (by omega) (Nat.le_pow (by decide)))
    (Nat.le_mul_of_pos_left _ hrr)
  have hword : 1 + w ≤ T := by
    apply le_trans _ (Nat.le_mul_of_pos_left _ hrr)
    apply le_trans _ (Nat.pow_le_pow_right (by omega : 0 < w) (by decide : 2 ≤ 6))
    nlinarith
  have hname : 1 + Fintype.card (Name n r) ≤ T := by
    rw [name_card, ← pow_mul, show n * 2 = 2 * n by ring]
    have h₁ : r * r ^ n ≤ r ^ (2 * n) := by rw [← pow_succ']; apply hp; omega
    have h₂ := hp n (by omega)
    have h₃ := hp 3 (by omega)
    have h₄ := Nat.mul_le_mul_left (r ^ (2 * n)) hc
    refine le_trans (b := r ^ (2 * n) * (6 + 2 * w)) (by nlinarith only [h₁, h₂, h₃, h₄, hrr]) ?_
    exact Nat.mul_le_mul_left _ (le_trans (by nlinarith)
      (Nat.pow_le_pow_right (by omega : 0 < w) (by decide : 2 ≤ 6)))
  have hinput : 1 + Fintype.card (A.CountBit r d) ≤ 9 * r ^ 3 * w ^ 2 := by
    have he : Fintype.card (A.CountBit r d) = r ^ 3 * Fintype.card A.I * Expansion.registerWidth n r d := by
      simp only [Expansion.CountBit, Fintype.card_prod, Fintype.card_fin, Expansion.registerWidth]
      ring
    rw [he]
    have hm := Nat.mul_le_mul (Nat.mul_le_mul_left (r ^ 3) hI) hd
    have hz : 0 < r ^ 3 * w ^ 2 := by positivity
    nlinarith only [hm, hz]
  have hflag : A.flagCost r d (w * 14) ≤ T := by
    unfold Expansion.flagCost
    calc
      _ ≤ (2 * r) * 100000 * (9 * r ^ 3 * w ^ 2) * (15 * w) := by gcongr <;> omega
      _ = r ^ 4 * (27000000 * w ^ 3) := by ring
      _ ≤ r ^ (2 * n) * w ^ 4 := by
        apply Nat.mul_le_mul (hp 4 (by omega))
        rw [show w ^ 4 = w * w ^ 3 by ring]
        gcongr
        omega
      _ ≤ T := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by decide))
  have hdata : 1 + Fintype.card (A.CountBit r d) ≤ T := by
    apply le_trans _ hflag
    unfold Expansion.flagCost
    exact (Nat.le_mul_of_pos_left _ (by positivity)).trans (Nat.le_mul_of_pos_right _ (by positivity))
  have hpair : (3 * r) ^ 2 ≤ T := by
    rw [show (3 * r) ^ 2 = r ^ 2 * 9 by ring]
    exact Nat.mul_le_mul (hp 2 (by omega)) (le_trans (by omega) (Nat.le_pow (by decide)))
  have hquery : Fintype.card (Query n r) ≤ T ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    rw [← mul_assoc, ← pow_two, pow_two T]
    exact Nat.mul_le_mul hpair (by omega)
  have hs : r ≤ T := by nlinarith only [hpair]
  have hk : 60000 ≤ T := by omega
  unfold addressCost
  calc
    _ ≤ T + T ^ 2 * (T * T + T * (T + T + T * T * T)) := by gcongr <;> omega
    _ ≤ T ^ 8 := by
      have hv (i : ℕ) (hi : i ≤ 6) : T ^ i ≤ T ^ 6 := Nat.pow_le_pow_right (by omega) hi
      have hb : 6 * T ^ 6 ≤ T ^ 8 := by rw [show T ^ 8 = T ^ 2 * T ^ 6 by ring]; gcongr; nlinarith
      nlinarith only [hv 1 (by decide), hv 4 (by decide), hb]
    _ = _ := by unfold T; rw [mul_pow, ← pow_mul, ← pow_mul]; congr 2; ring

variable [LinearOrder (Name n r)]

theorem addresses_size (hn : 2 ≤ n) (fa : Machine.Ports N l l → Label n r) (i : Fin n)
    (hw : 100000000 ≤ w) (hN : N ≤ 2 ^ w) (hr : 0 < r) (hrN : r ^ (16 * n) ≤ 2 ^ w)
    (hc : 2 ^ n ≤ w) (hI : Fintype.card A.I ≤ w) (he : ∀ z, 512 * A.chargeBits i z ≤ w)
    (hp : Fintype.card (Packet n r d) < (2 ^ w) ^ 8) :
    BNet F (addresses (d := d) A hn fa w i) (2 ^ w * w ^ 48) ∧
      BNet F (A.groupFlags (r := r) (d := d) N i) (2 ^ w * w ^ 48) := by
  have hwN : w < 2 ^ w := Nat.lt_two_pow_self
  have hb : Expansion.registerWidth n r d ≤ w * 8 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_mul]
    exact hp
  have hrow : Fintype.card (Class r × A.I) ≤ (2 ^ w) ^ 2 := by
    rw [Fintype.card_prod, show Fintype.card (Class r) = r ^ 3 by simp [Class]; ring, pow_two]
    exact Nat.mul_le_mul ((Nat.pow_le_pow_right hr (by omega)).trans hrN) (by omega)
  have hg := A.groupFlags_net (r := r) (d := d) (w := w * 14) (N := N) (M := w / 512) i
    (fun z => by have := he z; omega)
    (hN.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega)))
    (by
      calc
        _ ≤ (2 ^ w) ^ 2 * (2 ^ (w * 8) * 2 ^ w) := by gcongr; omega
        _ = 2 ^ (w * 11) := by rw [pow_mul, pow_mul]; ring
        _ < 2 ^ (w * 14) := Nat.pow_lt_pow_right (by decide) (by omega))
  have hsize := (address_bound A hn hw hr hc hI hb).trans (Nat.mul_le_mul_right _ hrN)
  refine ⟨(addresses_net hg).mono hsize, hg.mono (le_trans ?_ hsize)⟩
  have : Nonempty (Fin (3 * r)) := ⟨⟨0, by omega⟩⟩
  unfold addressCost
  calc
    _ ≤ 0 + 1 * (0 + 1 * (A.flagCost r d (w * 14) + 0 + 0)) := by simp
    _ ≤ _ := by gcongr <;> first | exact Fintype.card_pos | omega

end OAI.LinearAlgebra.MatrixExponent.Processor
end
