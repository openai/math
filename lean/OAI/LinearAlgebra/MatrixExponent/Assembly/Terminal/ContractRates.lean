import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Shipment
import OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.DictionaryHeaders
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.BoardPush
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Assembly.Shipment.Bound

/-!
# Pairing the two contacts of a terminal wire

One extra bit distinguishes self from a numbered neighbor.
Positions naming their own host, including unused positions,
are fixed individually.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring
open scoped Classical

def hop {d : ℕ} : Option (B d) ↪ B (d + 1) :=
  (⟨fun i => i.elim (0, 0) (fun j => (j, 1)), by
    rintro (_|i) (_|j) h
    · rfl
    · exact ((by decide : (0 : B 1) ≠ 1) (congrArg Prod.snd h)).elim
    · exact ((by decide : (1 : B 1) ≠ 0) (congrArg Prod.snd h)).elim
    · exact congrArg some (Prod.mk.inj h).1⟩ : Option (B d) ↪ B d × B 1).trans
      (Match.rowIndex d 1).symm.toEmbedding

def reverseHop (d : ℕ) (p : B d → Bool) : B (d + 1) :=
  (Format.addr (d + 1)).code.symm fun i =>
    decide (∃ j, p j = true ∧ (Format.addr (d + 1)).code (hop (some j)) i = true)

private theorem reverse_of_unique {d : ℕ} {p : B d → Bool} (j : B d)
    (h : ∀ k, p k = true ↔ k = j) : reverseHop d p = hop (some j) := by
  unfold reverseHop
  apply (Format.addr (d + 1)).code.symm_apply_eq.mpr
  funext i
  simp [h]

variable {F : Type} (S : Scheme F) (r : S.format.obj)
local notation "idx" => Match.rowIndex S.m (S.d + 1)

abbrev Flags := Format.vec S.m (.vec S.d .bit)
def flags : (Flags S).obj := fun i j => decide ((r i).1 j = i)
abbrev contact (v : B S.m) (i : Option (B S.d)) := (idx).symm (v, hop i)

def extended (v : B S.m) (i : B (S.d + 1)) :=
  let j := Match.rowIndex S.d 1 i
  if j.2 = 1 then (r v).1 j.1 else v

theorem extended_self (v : B S.m) : extended S r v (hop none) = v := by
  change extended S r v ((Match.rowIndex _ _).symm (0, 0)) = v
  simp [extended]

theorem extended_peer (v : B S.m) (j : B S.d) : extended S r v (hop (some j)) = (r v).1 j := by
  change extended S r v ((Match.rowIndex _ _).symm (j, 1)) = _
  simp only [extended, Equiv.apply_symm_apply, ite_true]

def perm (i : B (S.m + (S.d + 1))) :=
  let x := idx i
  let y := extended S r x.1 x.2
  (idx).symm (y, if y = x.1 then x.2 else reverseHop S.d (fun j => decide ((r y).1 j = x.1)))

theorem perm_self (v : B S.m) : perm S r (contact S v none) = contact S v none := by
  simp only [perm, contact, Equiv.apply_symm_apply, extended_self, ite_true]

variable (hr : Fmt.Reciprocal (.vec S.h (.addr S.ℓ)) r)
include hr

theorem perm_link (v w : B S.m) (i j : B S.d) (h : v ≠ w) (hv : (r v).1 i = w) (hw : (r w).1 j = v) :
    perm S r (contact S v (some i)) = contact S w (some j) := by
  have he := hr v i (hv.trans_ne h.symm)
  rw [hv] at he
  have eq : reverseHop S.d (fun l => decide ((r w).1 l = v)) = hop (some j) := by
    apply reverse_of_unique
    intro k
    rw [decide_eq_true_eq]
    exact ⟨fun h => he.unique h hw, fun h => h ▸ hw⟩
  simp only [perm, contact, Equiv.apply_symm_apply, extended_peer, hv, ite_eq_right h.symm, eq]

theorem perm_involutive : Function.Involutive (perm S r) := by
  intro i
  obtain ⟨⟨v, j⟩, rfl⟩ := (idx).symm.surjective i
  by_cases he : extended S r v j = v
  · have hh : perm S r ((idx).symm (v, j)) = (idx).symm (v, j) := by
      simp only [perm, Equiv.apply_symm_apply, he, ite_true]
    rw [hh, hh]
  let a := Match.rowIndex S.d 1 j
  have ht : a.2 = 1 := by
    by_contra hn
    exact he (ite_eq_right hn)
  have hj : j = hop (some a.1) := (Match.rowIndex S.d 1).eq_symm_apply.mpr (Prod.ext rfl ht)
  rw [hj, extended_peer] at he
  obtain ⟨k, hk, _⟩ := hr v a.1 he
  rw [hj]
  change perm S r (perm S r (contact S v (some a.1))) = _
  rw [perm_link S r hr _ _ _ k (Ne.symm he) rfl hk, perm_link S r hr _ _ _ _ he hk rfl]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-! # A reverse address from simultaneous neighbor flags -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring Install
open scoped Classical

private theorem any_net (F : Type) [Field F] (d : ℕ) :
    Circuit F (.vec d .bit) .bit (fun x => decide (∃ i, x i = true)) (2 * 2 ^ d + 1) := by
  have h := (BNet.any F (B d)).rename (Equiv.prodUnique (B d) Unit).symm (.refl _)
  rw [Fintype.card_fin] at h
  unfold Circuit
  convert h using 1
  funext x u
  change decide (∃ i, x (i, ()) = true) = _
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq]
  rfl

theorem reverseNet (F : Type) [Field F] (d : ℕ) :
    Circuit F (.vec d .bit) (.addr (d + 1)) (reverseHop d) (100 * (2 ^ d) ^ 2) := by
  let X := Format.vec d .bit
  let Y := Format.vec d X
  let A := Format.addr (d + 1)
  have hd : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
  let e : A.pins ↪ B d := (Fintype.equivFin A.pins).toEmbedding.trans
    (Fin.castLEEmb ((Format.width_addr _).le.trans hd))
  let mask (i j : B d) := Function.extend e (A.code (hop (some j))) (fun _ => false) i
  let send (x : X.obj) : Y.obj := fun i j => x j && mask i j
  let take (x : X.obj) : A.obj := A.code.symm (fun i => x (e i))
  have hs : Depends (Y.code ∘ send ∘ X.code.symm) 1 := by
    rintro ⟨i, j, t⟩
    exact ⟨{(j, ())}, by simp, fun _ _ h => congrArg (· && mask i j) (h (j, ()) (by simp))⟩
  have hr : Circuit F X A take (X.width + 2 * A.width) :=
    Circuit.project (fun i => (e i, ())) (fun x i => congrFun (A.code.apply_symm_apply _) i)
  let row (x : X.obj) := decide (∃ j, x j = true)
  have ho : Circuit F Y X (fun x i => row (x i)) (2 ^ d * (2 * 2 ^ d + 1)) :=
    Circuit.map _ (fun _ => any_net F d)
  have hm : Circuit F X Y send (X.width + 34 * Y.width) := hs.bnet F
  have eqn : take ∘ (fun x i => row (x i)) ∘ send = reverseHop d := by
    funext x
    apply congrArg A.code.symm
    funext i
    apply Bool.eq_iff_iff.mpr
    simp [row, send, mask, e.injective.extend_apply, A]
  rw [← eqn]
  refine ((hm.comp ho).comp hr).mono ?_
  simp only [X, Y, A, Format.width_vec]
  rw [Format.width_bit, Format.width_addr, mul_one]
  have hp : 1 ≤ 2 ^ d := Nat.two_pow_pos d
  nlinarith

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-!
# Testing one proposed transfer

Both banks may contain arbitrary bits. Retain the exact indicator
on all inputs, including malformed local control records.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring Rounds.Contraction
open scoped Classical

variable {F : Type} [Field F] (W : Prices F)
variable {m k k' V V' p w n : ℕ}
local notation "Z" => Fmt.payload m V k
local notation "X" => Fmt.payload m V' k'
local notation "C" => PeerLayout.S m V k m V' k' (2 ^ p)
local notation "U" => Payload.Script m m p w n

def checker (z : ((U).pair Z).obj) (x : (X).obj) : F :=
  (C).kernel F (Payload.Script.decode le_rfl z.1, z.2) x

theorem checker_net {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u) (hm : 1 ≤ m)
    (ht : 2 ^ p * ((max k k' + 1) * (2 ^ m + 2 ^ m)) < 2 ^ W.w) :
    Kernel F u L ((U).pair Z) X checker (W.shipment (Z).width m V k m V' k' p w n) := by
  let v := (Payload.Script.item w p n).width + W.w ^ W.power
  have hm' : m ≤ W.w := ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    (((Nat.le_add_left _ _).trans ((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)))).trans_lt ht)).le
  obtain ⟨a, ha, tag⟩ := W.tag m v hm hm' (Nat.le_add_left ..)
  have decode := Payload.Script.decode_net (L := L) (V := V) (k := k) (V' := V') (k' := k')
    (w := w) (n := n) hu (le_rfl : 2 ^ p ≤ 2 ^ p) tag tag (Nat.le_add_right _ _)
  have kernel : Kernel F u L ((C).control.pair Z) X ((C).kernel F)
      (W.transferCost m V k m V' k' p) := by
    have h := payload_kernel (K := F) (L := L) m V k m V' k' (2 ^ p) hu ht W.tag
    simp only [payloadChannels] at h
    unfold PeerLayout.S PeerLayout.P Prices.transferCost
    exact h
  have go := (decode.par (Map.circuit (L := L) hu (Circuit.id F Z))).then_kernel kernel
  have hb : Payload.Script.cost m k m k' p w v a a ≤
      Payload.Script.cost m k m k' p w v (W.W * (2 ^ m * v)) (W.W * (2 ^ m * v)) := by
    unfold Payload.Script.cost; gcongr
  refine go.mono ?_
  rw [add_comm _ (4 * (Z).width)]
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right hb _) _) _

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-! # Closing the two checks and the station dictionary on a common tape -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring Rounds.Contraction
open scoped Classical

variable {F : Type} [Field F] (S : Scheme F)

abbrev instruction (V t p w n : ℕ) :=
  ((Payload.Script S.m S.m p w n).pair (Payload.Script S.m S.m 0 w n)).pair (Dictionary.headers S V t)

def price (W : Prices F) (S : Scheme F) (V t V' k' p w n : ℕ) :=
  let k := height S t
  let a := (Fmt.payload S.m V k).width
  W.shipment a S.m V k S.m V k p w n + W.shipment a S.m V k S.m V' k' 0 w n +
    Dictionary.price S V t + 64 * ((instruction S V t p w n).width + (Fmt.payload S.m V' k').width + a)

variable (V t V' k' p w n : ℕ)
local notation "J" => instruction S V t p w n
local notation "E" => Fmt.payload S.m V' k'
local notation "Z" => Fmt.payload S.m V (height S t)

def value (x : (J).obj) (y : (E).obj) :=
  ∑ z : Tape S V t, checker (F := F) (x.1.1, z) z * checker (F := F) (x.1.2, z) y *
    Dictionary.weight S V t x.2 z

theorem evaluate (W : Prices F) {u : ℕ} {L : Set (Table F)}
    (hu : 3 ≤ u) (hm : 1 ≤ S.m)
    (ht : 2 ^ p * ((max (height S t) k' + 1) * (2 ^ S.m + 2 ^ S.m)) < 2 ^ W.w)
    (size : Dictionary.arity S t ≤ u) (label : Dictionary.label S t ∈ L) :
    Kernel F u L ((J).pair E) (.wire .unit)
      (fun z _ => value S V t V' k' p w n z.1 z.2) (price W S V t V' k' p w n) := by
  let k := height S t
  have hc : 2 ^ p * ((max k k + 1) * (2 ^ S.m + 2 ^ S.m)) < 2 ^ W.w := by
    refine lt_of_le_of_lt ?_ ht
    rw [max_self]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.succ_le_succ (le_max_left ..)))
  have hd : 2 ^ 0 * ((max k k' + 1) * (2 ^ S.m + 2 ^ S.m)) < 2 ^ W.w :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.two_pow_pos _)) ht
  have left := checker_net (V := V) (V' := V) (w := w) (n := n) (L := L) W hu hm hc
  have right := checker_net (V := V) (V' := V') (w := w) (n := n) (L := L) W hu hm hd
  have station := Dictionary.realize (V := V) hu size label
  have h := Kernel.contract hu left right station
  unfold price
  dsimp only
  rw [Format.width_pair, Format.width_pair]
  exact h

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-! # Computing the complete dictionary header vector from the original control rows -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Header

open Coloring Dictionary
open scoped Classical
variable {F : Type} [Field F] (S : Scheme F) (V t : ℕ)

def arity := (key S).width + (header S).width
private def mapLabel (A B : Format) (f : A.obj → B.obj) :=
  lookup F A B (fun x y => if f x = y then 1 else 0)

def label := mapLabel (F:=F) (key S) (header S) (select S)

abbrev names := Format.vec S.m (.vec (n S) (key S))
abbrev lines := Format.vec S.m (line S)
def rowCost := 4 * (S.format.width + 34 * (names S).width) +
  2 ^ S.m * (2 ^ (n S) * (1 + (key S).width + (header S).width))

variable {S V t} {u v c : ℕ} {L : Set (Table F)}

theorem rows_net (hu : 3 ≤ u) (ha : arity S ≤ u) (hl : label S ∈ L) :
    Map F u L S.format (lines S) (row S) (rowCost S) := by
  have a : Circuit F S.format (names S) (labels S) (S.format.width + 34 * (names S).width) := by
    apply Window.Tile.project_const
    rintro ⟨i, j, k|k⟩
    · exact .inl ⟨(i, .inr ((Match.rowIndex S.h S.k j).1, k)), fun _ => rfl⟩
    · exact .inr ⟨(Format.addr S.k).code (Match.rowIndex S.h S.k j).2 k, fun _ => rfl⟩
  have b : Map F u L (key S) (header S) (select S) (1 + (key S).width + (header S).width) :=
    Kernel.lookup ha hl
  exact (Map.circuit hu a).comp (Map.vec _ fun _ : B S.m => Map.vec _ fun _ : B (n S) => b)

private theorem unary {A : Format} {δ : ℕ} (hw : A.width ≤ δ) (f : Bool → A.obj) :
    Cheap F 0 δ .bit A f 2 := by
  have dep : Install.Depends (A.code ∘ f ∘ Format.bit.code.symm) 1 := by
    intro i
    refine ⟨Finset.univ, le_rfl, fun x y he => ?_⟩
    rw [funext (fun j => he j (Finset.mem_univ _))]
  refine ⟨_, dep.bnet F, ?_⟩
  change 1 + A.width + (1 + 34 * A.width) ≤ _
  ring_nf
  omega

def scale (S : Scheme F) (t : ℕ) := wordSize S t + (header S).width

private theorem host :
    Cheap F (n S) (scale S t) (line S) (.pair (.addr (wordSize S t)) (line S))
      (fun x => (length S t x, pack S x)) 50 := by
  let δ := scale S t
  have hn : n S + 1 ≤ δ := by unfold δ scale wordSize; omega
  have he : S.e + t + 1 ≤ δ := by unfold δ scale wordSize; omega
  have hh : (header S).width ≤ δ := Nat.le_add_left _ _
  have hw : (header S).width ≤ 2 ^ 0 * (100 + δ) ^ 1 := by simp only [pow_zero, one_mul, pow_one]; omega
  have get := (Cheap.id F hw).fst
  have fl := get.comp (unary (F:=F) (A:=.addr 1) (δ:=δ) (by rw [Format.width_addr]; omega) flag)
  have sz := get.comp (unary (F:=F) (A:=.addr (S.e + t + 1)) (by rw [Format.width_addr]; exact he) (amount S t))
  have len := (Cheap.map _ fun _ : B (n S) => sz).comp ((cheap_total F (n S) (S.e + t + 1)).widen he)
  have σ := (Cheap.map _ fun _ : B (n S) => fl).comp ((cheap_order F (n S) 1).widen hn)
  have hd : (line S).width ≤ 2 ^ (n S) * (100 + δ) ^ 1 := by
    rw [Format.width_vec, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have sorted := ((Cheap.id F hd).pair σ).comp (Cheap.lookup F (n S) δ (header S) (by omega) hh)
  exact (len.pair sorted).mono (by decide)

def localCost (S : Scheme F) (t : ℕ) :=
  4 * (2 ^ S.m * (2 ^ (n S) * (100 + scale S t) ^ 50) + 3 * (source S t).width)

theorem paired_net (hu : 3 ≤ u) (ha : arity S ≤ u) (hl : label S ∈ L) :
    Map F u L S.format (source S t) (paired S t) (rowCost S + localCost S t) := by
  let D := Format.vec S.m (.pair (.addr (wordSize S t)) (line S))
  have hw : D.width = (source S t).width := by simp [D, source, Redistribute.input, mul_add]
  have unzip : Circuit F D (source S t) (fun x => (fun i => (x i).1, fun i => (x i).2))
      (D.width + 2 * (source S t).width) := by
    apply Circuit.project (Sum.elim (fun p => (p.1, .inl p.2)) (fun p => (p.1, .inr p.2)))
    rintro x (i|i) <;> rfl
  obtain ⟨s, hs, hb⟩ := host (S:=S) (t:=t)
  have hc := (Circuit.map _ (fun _ : B S.m => hs)).comp unzip
  have hle : s ≤ 2 ^ (n S) * (100 + scale S t) ^ 50 := by omega
  have hm := Nat.mul_le_mul_left (2 ^ S.m) hle
  exact (rows_net hu ha hl).comp ((Map.circuit hu hc).mono (n:=localCost S t) (by unfold localCost; omega))

def cost (S : Scheme F) (V t v c : ℕ) := rowCost S + localCost S t +
    Redistribute.cost S.m (height S t) (wordSize S t) v c +
    4 * ((dest S V t).width + 2 * (headers S V t).width)

theorem realize (hu : 3 ≤ u) (ha : arity S ≤ u) (hl : label S ∈ L)
    (ht : Radix.Tag F S.m v c) (hv : (line S).width ≤ v) :
    Map F u L S.format (headers S V t) (eval S V t) (cost S V t v c) := by
  have a := paired_net (t:=t) hu ha hl
  have b := Redistribute.realize (L:=L) (w:=wordSize S t) (k:=height S t) (V:=V)
    hu ht (line S) hv (fun _ => pad S)
  have d : Circuit F (dest S V t) (headers S V t) (cut S V t)
      ((dest S V t).width + 2 * (headers S V t).width) :=
    Circuit.project (fun i => ⟨i.1.1, pick S V t i.1, i.2⟩) (fun _ _ => rfl)
  exact (a.comp b).comp (Map.circuit hu d)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Header
end

/-! # Header work is charged to hosts and the data charge is linear in bank capacity -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Header
open Coloring Dictionary

private theorem majorant (R x y H z d W : ℕ) (hR : 1000 ≤ R)
    (hx : x ≤ R) (hy : y ≤ R) (hh : H ≤ R) (hz : z ≤ R)
    (hd : d ≤ R) (hw : W + 1 ≤ R) :
    137 * x + 1 + 13 * y + 12 * z + 52 * H * y + 4 * d ^ 50 + 10000 * H * (W + 1) * (y + 1) ≤ R ^ 80 := by
  have hr : 0 < R := by omega
  have h₀ : 1 ≤ R ^ 50 := Nat.one_le_pow _ _ hr
  have h₁ : R ≤ R ^ 50 := Nat.le_pow (by decide)
  have h₂ : R ^ 2 ≤ R ^ 50 := Nat.pow_le_pow_right hr (by decide)
  have h₃ : R ^ 3 ≤ R ^ 50 := Nat.pow_le_pow_right hr (by decide)
  calc
    _ ≤ 137 * R + 1 + 13 * R + 12 * R + 52 * R * R + 4 * R ^ 50 + 10000 * R * R * (R + 1) := by gcongr
    _ = 1 + 162 * R + 10052 * R ^ 2 + 10000 * R ^ 3 + 4 * R ^ 50 := by ring
    _ ≤ 1000000 * R ^ 50 := by omega
    _ ≤ R ^ 2 * R ^ 50 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hR 2)
    _ = R ^ 52 := (pow_add R 2 50).symm
    _ ≤ R ^ 80 := Nat.pow_le_pow_right hr (by decide)

private theorem account (A M N H x y z d W P B V v c D E Y : ℕ)
    (hn : 0 < N) (hv : v ≤ N * y + P) (hc : c ≤ W * (M * v))
    (hD : D ≤ H * (M * (N * y))) (hE : E ≤ D) (hY : Y ≤ H * (2 * V)) :
    4 * (A + 34 * (M * (N * x))) + M * (N * (1 + x + y)) +
      4 * (M * (N * d ^ 50) + 3 * (M * z + M * (N * y))) +
      10000 * H * (c + M * (v + B)) + 4 * (D + 2 * E) + 40 * (E + Y) ≤
    4 * A + (M * (P + B) + M * N) * (137 * x + 1 + 13 * y + 12 * z + 52 * H * y + 4 * d ^ 50 + 10000 * H * (W + 1) * (y + 1)) + 80 * H * V := by
  have hm := Nat.le_mul_of_pos_right M hn
  have hg : c ≤ W * (M * (N * y + P + B)) := hc.trans (by gcongr; omega)
  have he := hE.trans hD
  calc
    _ ≤ 4 * (A + 34 * (M * (N * x))) + M * (N * (1 + x + y)) +
      4 * (M * (N * d ^ 50) + 3 * (M * N * z + M * (N * y))) +
      10000 * H * (W * (M * (N * y + P + B)) + M * (N * y + P + B)) +
      4 * (H * (M * (N * y)) + 2 * (H * (M * (N * y)))) + 40 * (H * (M * (N * y)) + H * (2 * V)) := by gcongr
    _ ≤ _ := by ring_nf; omega

variable {F : Type} {S : Scheme F} {V t v c P W : ℕ}

theorem cost_bound (hv : v ≤ (line S).width + P) (hc : c ≤ W * (2 ^ S.m * v)) :
    cost S V t v c + Dictionary.price S V t ≤
      4 * S.format.width + (2 ^ S.m * (P + (101 + S.m + wordSize S t) ^ 60) + 2 ^ (S.m + S.h + S.k))*
        (1000 + W + scale S t) ^ 80 + 80 * (height S t + 1) * V := by
  have hu := account S.format.width (2 ^ S.m) (2 ^ (n S)) (height S t + 1)
    (key S).width (header S).width (wordSize S t) (100 + scale S t) W P
    ((101 + S.m + wordSize S t) ^ 60) V v c (dest S V t).width (headers S V t).width
    (Fmt.payload S.m V (height S t)).width (Nat.two_pow_pos _) (by simpa only [line, Format.width_vec] using hv) hc
    (by simpa only [line, Format.width_vec] using width_dest S V t)
    (width_headers S V t) (Fmt.width_payload ..)
  have hb := majorant (1000 + W + scale S t) (key S).width (header S).width (height S t + 1)
    (wordSize S t) (100 + scale S t) W (by omega)
    (by simp only [scale, key, header, Format.width_pair]; omega)
    (by unfold scale; omega) (by unfold scale wordSize height n; omega)
    (by unfold scale; omega) (by omega) (by omega)
  have hn : 2 ^ (S.m + S.h + S.k) = 2 ^ S.m * 2 ^ (n S) := by rw [add_assoc, pow_add]
  rw [hn]
  refine le_trans ?_ (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ hb) _) _)
  simpa only [cost, Dictionary.price, rowCost, localCost, names, source, Redistribute.input, Redistribute.cost,
    Redistribute.budget, line, Format.width_pair, Format.width_vec, Format.width_addr] using hu

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Header
end

/-! # Reading reciprocal contacts from a matrix of address comparisons -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring
open scoped Classical

variable {F : Type} (S : Scheme F)
abbrev LinkGrid := (Perm (S.m + (S.d + 1))).pair (Flags S)
def links (r : S.format.obj) : (LinkGrid S).obj := (perm S r, flags S r)

namespace Links
local notation "m" => S.m
local notation "d" => S.d
local notation "idx" => Match.rowIndex m (d + 1)

abbrev Rows := Neighborhood.Rows m (d + 1)
abbrev Mask := Neighborhood.Mask m (d + 1) (d + 1)
abbrev Query := Format.vec m (.vec (d + 1) (.vec d .bit))
abbrev Reply := Format.vec m (.vec (d + 1) (.addr (d + 1)))
abbrev Status := (Mask S).pair (Reply S)
abbrev Data := (Rows S).pair (Status S)

def query (x : (Mask S).obj) : (Query S).obj := fun v i j => x v i (hop (some j)) (hop none)
def reply (x : (Query S).obj) : (Reply S).obj := fun v i => reverseHop d (x v i)
def status (x : (Mask S).obj) : (Status S).obj := (x, reply S (query S x))
def data (x : (Rows S).obj) : (Data S).obj := (x, status S (Neighborhood.maskRows x x))
def self (x : (Data S).obj) (v : B m) (j : B (d + 1)) := x.2.1 v (hop none) j (hop none)

def finish (x : (Data S).obj) : (LinkGrid S).obj :=
  (fun i =>
    let j := idx i
    (idx).symm (x.1 j.1 j.2, if self S x j.1 j.2 then j.2 else x.2.2 j.1 j.2),
   fun i j => self S x i (hop (some j)))

theorem correct : finish S ∘ data S ∘ extended S = links S := by
  funext r
  have a (i : B m) (j : B (d + 1)) : self S (data S (extended S r)) i j = decide (extended S r i j = i) := by
    simp only [self, data, status, Neighborhood.maskRows, extended_self]
  have b (i : B m) (j : B (d + 1)) :
      (data S (extended S r)).2.2 i j = reverseHop d (fun k => decide ((r (extended S r i j)).1 k = i)) := by
    apply congrArg (reverseHop d)
    funext k
    simp only [query, Neighborhood.maskRows, extended_self, extended_peer]
  apply Prod.ext
  · funext i
    simp only [Function.comp_apply, finish, links, perm, a, b, decide_eq_true_eq]
    rfl
  · funext i j
    simp only [Function.comp_apply, finish, links, flags, a, extended_peer]

variable [Field F]

theorem extend_net : Circuit F S.format (Rows S) (extended S) (S.format.width + 34 * (Rows S).width) := by
  apply Window.Tile.project_const
  rintro ⟨v, i, k⟩
  by_cases h : (Match.rowIndex S.d 1 i).2 = 1
  · refine .inl ⟨(v, .inl ((Match.rowIndex S.d 1 i).1, k)), fun r => ?_⟩
    change (Format.addr m).code (extended S r v i) k = _
    rw [extended, ite_eq_left h]
    rfl
  · refine .inr ⟨(Format.addr m).code v k, fun r => ?_⟩
    change (Format.addr m).code (extended S r v i) k = _
    rw [extended, ite_eq_right h]

theorem query_net : Circuit F (Mask S) (Query S) (query S) ((Mask S).width + 2 * (Query S).width) :=
  Circuit.project (fun x => (x.1, x.2.1, hop (some x.2.2.1), hop none, x.2.2.2)) (fun _ _ => rfl)

theorem finish_net : Circuit F (Data S) (LinkGrid S) (finish S) ((Data S).width + 68 * (LinkGrid S).width) := by
  let A := Data S
  let C := LinkGrid S
  have he : Install.Depends (C.code ∘ finish S ∘ A.code.symm) 2 := by
    have pin (i : C.pins) (j : A.pins) (h : ∀ x, C.code (finish S x) i = A.code x j) :
        ∃ s : Finset A.pins, s.card ≤ 2 ∧ ∀ x y, (∀ l ∈ s, x l = y l) →
          (C.code ∘ finish S ∘ A.code.symm) x i = (C.code ∘ finish S ∘ A.code.symm) y i := by
      refine ⟨{j}, by simp, fun x y he => ?_⟩
      simp only [Function.comp_apply, h, Equiv.apply_symm_apply]
      exact he j (by simp)
    rintro (⟨i, t⟩|⟨j, k, ⟨⟩⟩)
    · let v := (idx i).1
      let w := (idx i).2
      obtain ⟨k, hk⟩ := Match.append_pin m (d + 1) t
      cases k with
      | inl k =>
        exact pin _ (.inl (v, w, k)) (fun x => hk _ _)
      | inr k =>
        let j : A.pins := .inr (.inl (v, hop none, w, hop none, ()))
        let l : A.pins := .inr (.inr (v, w, k))
        have eq (x : A.obj) : C.code (finish S x) (.inl (i, t)) =
            if A.code x j then (Format.addr (d + 1)).code w k else A.code x l := by
          change (Format.addr _).code ((idx).symm (x.1 v w, if self S x v w then w else x.2.2 v w)) t = _
          rw [hk]
          change (Format.addr (d + 1)).code (if self S x v w then w else x.2.2 v w) k =
            if self S x v w then _ else _
          split <;> rfl
        refine ⟨{j, l}, Finset.card_le_two, fun x y h => ?_⟩
        simp only [Function.comp_apply, eq, Equiv.apply_symm_apply, h j (by simp), h l (by simp)]
    · exact pin _ (.inr (.inl (j, hop none, hop (some k), hop none, ()))) (fun _ => rfl)
  exact he.bnet F

end Links
end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-!
# Cost of constructing the terminal contact permutation

A shared mask compares only addresses in the host's neighborhood.
Recover each reciprocal index from the unique successful comparison.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring Links
open scoped Classical

variable {F : Type} (S : Scheme F)

local notation "m" => S.m
local notation "d" => S.d
local notation "t" => (S.m + 2 ^ (S.d + 1))
local notation "W" => (2 ^ m * (100 + t) ^ 24)

def linkCost := S.format.width + 512 * W

private theorem product (x y z : ℕ) (hx : x ≤ 100 + t) (hy : y ≤ 100 + t) (hz : z ≤ 100 + t) :
    2 ^ m * (x * (y * z)) ≤ W := by
  apply Nat.mul_le_mul_left
  calc
    _ ≤ (100 + t) * ((100 + t) * (100 + t)) := Nat.mul_le_mul hx (Nat.mul_le_mul hy hz)
    _ = (100 + t) ^ 3 := by rw [pow_succ' (100 + t) 2, pow_two]
    _ ≤ _ := Nat.pow_le_pow_right (by positivity) (by decide)

private theorem bounds :
    (Query S).width ≤ W ∧ (Reply S).width ≤ W ∧ (LinkGrid S).width ≤ 2 * W ∧
      2 ^ m * (2 ^ (d + 1) * (100 * (2 ^ d) ^ 2)) ≤ 100 * W := by
  have hs : 2 ^ (d + 1) ≤ 100 + t := (Nat.le_add_left _ _).trans (Nat.le_add_left _ _)
  have hd : 2 ^ d ≤ 100 + t := (Nat.pow_le_pow_right (by decide) (Nat.le_succ d)).trans hs
  have h₁ : 1 ≤ 100 + t := (by decide : 1 ≤ 100).trans (Nat.le_add_right ..)
  have ha : m + (d + 1) ≤ 100 + t :=
    (Nat.add_le_add_left Nat.lt_two_pow_self.le m).trans (Nat.le_add_left ..)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Query, Format.width_vec, Format.width_vec, Format.width_vec, Format.width_bit]
    exact product S _ _ _ hs hd h₁
  · rw [Reply, Format.width_vec, Format.width_vec, Format.width_addr]
    simpa only [mul_one] using product S _ _ 1 hs ((Nat.le_add_left _ _).trans ha) h₁
  · rw [LinkGrid, Format.width_pair, Perm, Flags, Format.width_vec, Format.width_addr, Format.width_vec,
      Format.width_vec, Format.width_bit, pow_add, mul_assoc, two_mul]
    have hP := product S _ _ 1 hs ha h₁
    have hQ := product S _ _ 1 hd h₁ h₁
    simp only [mul_one] at hP hQ ⊢
    exact Nat.add_le_add hP hQ
  · rw [mul_left_comm (2 ^ (d + 1)) 100, mul_left_comm (2 ^ m) 100, pow_two]
    exact Nat.mul_le_mul_left 100 (product S _ _ _ hs hd hd)

private theorem assemble [Field F] {A B C : Format} {f : (A.pair A).obj → B.obj}
    {g : B.obj → C.obj} {k l w : ℕ}
    (first : Circuit F (A.pair A) B f k) (next : Circuit F B C g l)
    (hk : (A.pair A).width + B.width + k ≤ w) (hl : l ≤ 104 * w) :
    Circuit F A (A.pair (B.pair C)) (fun x => (x, f (x, x), g (f (x, x)))) (200 * w) := by
  have h := Circuit.id F A
  refine (h.pair (((h.pair h).comp first).comp ((Circuit.id F B).pair next))).mono ?_
  rw [Format.width_pair] at hk
  omega

private theorem mask_net [Field F] : ∃ a,
    Circuit F ((Rows S).pair (Rows S)) (Mask S) (fun x => Neighborhood.maskRows x.1 x.2) a ∧
    ((Rows S).pair (Rows S)).width + (Mask S).width + a ≤ W :=
  Neighborhood.cheap_maskRows F (Nat.le_add_right m (2 ^ (d + 1)))
    (Nat.le_add_left (2 ^ (d + 1)) m) (Nat.le_add_left (2 ^ (d + 1)) m)

private theorem twice [Field F] {A B : Format} {f : A.obj → B.obj} {c : ℕ}
    (h : Circuit F A B f c) (i j : ℕ) :
    Circuit F (.vec i (.vec j A)) (.vec i (.vec j B)) (fun x v y => f (x v y)) (2 ^ i * (2 ^ j * c)) :=
  Circuit.map _ fun _ => Circuit.map _ fun _ => h

private theorem r_net [Field F] : Circuit F (Query S) (Reply S) (Links.reply S) (2 ^ m * (2 ^ (d + 1) * (100 * (2 ^ d) ^ 2))) := by
  unfold Links.reply Query Reply
  exact twice (reverseNet F d) m (d + 1)

private theorem data_net [Field F] : Circuit F (Rows S) (Links.Data S) (Links.data S) (200 * W) := by
  obtain ⟨a, k, h⟩ := mask_net S
  have hl : (Mask S).width + 2 * (Query S).width + 2 ^ m * (2 ^ (d + 1) * (100 * (2 ^ d) ^ 2)) ≤ 104 * W := by
    obtain ⟨h₁, _, _, h₄⟩ := bounds S
    omega
  have h' := assemble k ((query_net S).comp (r_net S)) h hl
  simp only [Function.comp_apply] at h'
  unfold Links.data Links.status Links.Data Links.Status
  exact h'

theorem links_net [Field F] : Circuit F S.format (LinkGrid S) (links S) (linkCost S) := by
  rw [← correct]
  refine ((extend_net S).comp ((data_net S).comp (finish_net S))).mono ?_
  obtain ⟨_, _, h⟩ := mask_net S
  obtain ⟨_, h₂, h₃, _⟩ := bounds S
  rw [Format.width_pair] at h
  unfold linkCost
  rw [Links.Data, Format.width_pair, Links.Status, Format.width_pair]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-!
# Uniform cost scales of the terminal contraction

Host names, station labels and physical payloads have separate
coefficients. Each estimate is uniform over fields and schemes.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
open BatchDescent.Phase Rounds.Contraction

structure Size where
  F : Type
  [field : Field F]
  S : Scheme F
  W : Prices F
  V : ℕ
  t : ℕ
  V' : ℕ
  k' : ℕ

attribute [instance] Size.field

namespace Size
variable (i : Size)

abbrev k := height i.S i.t
abbrev w := max i.k i.k' + 1
abbrev p := i.S.d + 1
abbrev n := i.S.spanRows
abbrev B := 1000 + i.W.W + i.k + i.k'
abbrev T := i.B + 2 ^ i.S.d + i.S.ℓ
abbrev M := i.T + i.S.m + i.W.w + i.W.w ^ i.W.power
abbrev hosts := 2 ^ i.S.m
abbrev spans := i.hosts * 2 ^ i.n
abbrev volume := i.V + i.V'
abbrev bound (K : ℕ) := i.hosts * i.M ^ K + i.spans * i.T ^ K + i.volume * i.B ^ K

theorem b_two : 2 ≤ i.B := by unfold B; omega
theorem bt : i.B ≤ i.T := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
theorem tm : i.T ≤ i.M := by unfold M; omega
theorem t_two : 2 ≤ i.T := i.b_two.trans i.bt
theorem m_two : 2 ≤ i.M := i.t_two.trans i.tm
end Size

abbrev Outer := Poly Size.B
abbrev Short := Poly Size.T
abbrev Long := Poly Size.M
def Work (f : Size → ℕ) := ∃ K, ∀ i, f i ≤ i.bound K

variable {f g : Size → ℕ}
theorem Outer.short (h : Outer f) : Short f := h.grow Size.bt
theorem Short.long (h : Short f) : Long f := h.grow Size.tm
theorem Outer.long (h : Outer f) : Long f := h.short.long

theorem num (a : ℕ) : Outer (fun _ => a) := Poly.const Size.b_two a
theorem k : Outer Size.k := Poly.of_le Size.b_two fun i => by unfold Size.B; omega
theorem k' : Outer Size.k' := Poly.of_le Size.b_two fun i => by unfold Size.B; omega
theorem w : Outer Size.w := Poly.of_le Size.b_two fun i => by unfold Size.B Size.w; omega
theorem rate : Outer (fun i => i.W.W) := Poly.of_le Size.b_two fun i => by unfold Size.B; omega
theorem n : Outer Size.n := k.mono fun i => by unfold Size.k Size.n height Scheme.spanRows; omega
theorem neighbors : Short (fun i => 2 ^ i.S.d) := Poly.of_le Size.t_two fun i => by unfold Size.T; omega
theorem d : Short (fun i => i.S.d) := neighbors.of_exp
theorem labels : Short (fun i => i.S.ℓ) := Poly.of_le Size.t_two fun _ => Nat.le_add_left ..
theorem p : Short Size.p := d.add (num 1).short
theorem links : Short (fun i => 2 ^ i.p) := by simpa only [Size.p, pow_succ] using neighbors.mul (num 2).short
theorem m : Long (fun i => i.S.m) := Poly.of_le Size.m_two fun i => by unfold Size.M; omega
theorem limit : Long (fun i => i.W.w) := Poly.of_le Size.m_two fun i => by unfold Size.M; omega
theorem threshold : Long (fun i => i.W.w ^ i.W.power) :=
  Poly.of_le Size.m_two fun i => by unfold Size.M; omega

namespace Work
theorem mono (hf : Work f) (h : ∀ i, g i ≤ f i) : Work g :=
  let ⟨s, hs⟩ := hf
  ⟨s, fun i => (h i).trans (hs i)⟩

theorem add (hf : Work f) (hg : Work g) : Work (fun i => f i + g i) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  refine ⟨max s t + 1, fun i => (Nat.add_le_add (hs i) (ht i)).trans ?_⟩
  unfold Size.bound
  rw [add_add_add_comm, add_add_add_comm (i.hosts * _ ^ s), ← mul_add, ← mul_add, ← mul_add]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (Poly.pow_sum i.m_two ..))
    (Nat.mul_le_mul_left _ (Poly.pow_sum i.t_two ..)))
    (Nat.mul_le_mul_left _ (Poly.pow_sum i.b_two ..))

theorem mul (hf : Work f) (hg : Outer g) : Work (fun i => f i * g i) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg.bound
  refine ⟨s + t, fun i => (Nat.mul_le_mul (hs i) (ht i)).trans ?_⟩
  unfold Size.bound
  rw [add_mul, add_mul]
  simp only [mul_assoc, pow_add]
  gcongr
  · exact i.bt.trans i.tm
  · exact i.bt

theorem scale (hf : Work f) (hg : Outer g) : Work (fun i => g i * f i) :=
  (hf.mul hg).mono fun _ => (mul_comm ..).le

theorem hosts (hf : Long f) : Work (fun i => i.hosts * f i) :=
  let ⟨s, hs⟩ := hf.bound
  ⟨s, fun i => (Nat.mul_le_mul_left _ (hs i)).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))⟩

theorem spans (hf : Short f) : Work (fun i => i.spans * f i) :=
  let ⟨s, hs⟩ := hf.bound
  ⟨s, fun i => (Nat.mul_le_mul_left _ (hs i)).trans ((Nat.le_add_left ..).trans (Nat.le_add_right ..))⟩

theorem volume (hf : Outer f) : Work (fun i => i.volume * f i) :=
  let ⟨s, hs⟩ := hf.bound
  ⟨s, fun i => (Nat.mul_le_mul_left _ (hs i)).trans (Nat.le_add_left ..)⟩
end Work

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
end

/-! # Uniform bound for constructing and evaluating the terminal dictionary -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
open Coloring

namespace Size
variable (i : Size)
abbrev v := (Header.line i.S).width + i.W.w ^ i.W.power
abbrev c := i.W.W * (2 ^ i.S.m * i.v)
abbrev header := Header.cost i.S i.V i.t i.v i.c
abbrev dictionary := Dictionary.price i.S i.V i.t
abbrev inner := (Fmt.payload i.S.m i.V i.k).width
abbrev outer := (Fmt.payload i.S.m i.V' i.k').width

theorem stations : 2 ^ (i.S.m + i.S.h + i.S.k) ≤ i.spans := by
  rw [add_assoc, pow_add]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..))

end Size

theorem format : Work (fun i => i.S.format.width) := by
  refine ((Work.hosts (neighbors.long.mul m)).add (Work.spans labels)).mono fun i => ?_
  rw [Scheme.format, Fmt.width_rows, Format.width_addr, mul_add, ← mul_assoc (2 ^ i.S.m) (2 ^ i.S.h)]
  have he : 2 ^ i.S.h ≤ 2 ^ i.n := Nat.pow_le_pow_right (by decide) (by unfold Size.n Scheme.spanRows; omega)
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he)) _

theorem inner : Work Size.inner := by
  refine (Work.volume ((k.add (num 1)).mul (num 2))).mono fun i => ?_
  refine (Fmt.width_payload ..).trans ?_
  rw [← mul_assoc, mul_comm _ i.V]
  exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)

theorem outer : Work Size.outer := by
  refine (Work.volume ((k'.add (num 1)).mul (num 2))).mono fun i => ?_
  refine (Fmt.width_payload ..).trans ?_
  rw [← mul_assoc, mul_comm _ i.V']
  exact Nat.mul_le_mul_right _ (Nat.le_add_left ..)

private theorem word : Outer (fun i => Header.wordSize i.S i.t) :=
  (k.add (num 1)).mono fun i => by unfold Header.wordSize Header.n Size.k height; omega

private theorem scale : Short (fun i => Header.scale i.S i.t) := by
  have hk : Outer (fun i => i.S.k) := n.mono fun i => by unfold Size.n Scheme.spanRows; omega
  refine (word.short.add ((num 1).short.add (labels.add hk.short))).mono fun i => ?_
  simp only [Header.scale, Dictionary.header, Format.width_pair, Format.width_addr]
  rw [Format.width_bit]

theorem both : Work (fun i => i.header + i.dictionary) := by
  have factor := ((((num 1000).short.add rate.short).add scale).pow 80)
  have total := threshold.add ((((num 101).long.add m).add word.long).pow 60)
  have names := Work.hosts (total.mul (Short.long factor))
  have rows := Work.spans factor
  have bits := Work.volume ((num 80).mul (k.add (num 1)))
  refine (((format.scale (num 4)).add (names.add rows)).add bits).mono fun i => ?_
  refine (Header.cost_bound (S:=i.S) (V:=i.V) (t:=i.t) (v:=i.v) (c:=i.c)
    (P:=i.W.w ^ i.W.power) (W:=i.W.W) le_rfl le_rfl).trans ?_
  rw [add_mul, mul_assoc (2 ^ i.S.m), mul_comm _ i.V]
  exact Nat.add_le_add (Nat.add_le_add_left (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ i.stations) _) _) (Nat.mul_le_mul_right _ (Nat.le_add_right ..))

theorem header : Work Size.header := both.mono fun _ => Nat.le_add_right ..
theorem dictionary : Work Size.dictionary := both.mono fun _ => Nat.le_add_left ..
theorem headers : Work (fun i => (Dictionary.headers i.S i.V i.t).width) :=
  dictionary.mono fun i => by unfold Size.dictionary Dictionary.price; omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
end

/-! # Uniform terminal contraction cost -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
open Coloring Rounds.Contraction

abbrev Size.instruction (i : Size) := Terminal.instruction i.S i.V i.t i.p i.w i.n
abbrev Size.price (i : Size) := Terminal.price i.W i.S i.V i.t i.V' i.k' i.p i.w i.n

private theorem script (a : Size → ℕ) (ha : Short a) (he : Short (fun i => 2 ^ a i)) :
    Work (fun i => (Payload.Script i.S.m i.S.m (a i) i.w i.n).width) := by
  have row := Work.hosts (Short.long (w.short.add (he.mul w.short)))
  have span := Work.spans (ha.add ((num 3).short.mul w.short))
  have peer := Work.hosts (he.long.mul (m.add ha.long))
  refine (((row.add span).scale (num 2)).add peer).mono fun i => ?_
  simp only [Payload.Script, PeerLayout.input, PeerLayout.lengths, Fragments.Entry, Intervals.span,
    Format.width_pair, Format.width_vec, Format.width_addr, Size.spans, Size.hosts, pow_add]
  rw [Format.width_addr]
  exact le_of_eq (by ring)

theorem instruction : Work (fun i => i.instruction.width) := by
  have h := script Size.p p links
  have e := script (fun _ => 0) (num 0).short (num 1).short
  refine ((h.add e).add headers).mono fun i => ?_
  rw [Size.instruction, Terminal.instruction, Format.width_pair, Format.width_pair]

private theorem shipping (X J a : Size → ℕ) (hx : ∀ i, X i ≤ i.volume)
    (hj : Outer J) (ha : Short a) (he : Short (fun i => 2 ^ a i)) :
    Work (fun i => i.W.shipment i.inner i.S.m i.V i.k i.S.m (X i) (J i) (a i) i.w i.n) := by
  obtain ⟨K, hK⟩ := Prices.shipment_le
  have b := (((num 1000).add rate).add k).add hj
  have s := (((Outer.short b).add ha).add w.short).add n.short
  have l := ((((Short.long s).add m).add m).add limit).add threshold
  have posts := (num 2).short.mul he
  have names := Work.hosts ((Short.long posts).mul (l.pow K))
  have rows := Work.spans (posts.mul (s.pow K))
  have bits := Work.volume ((num 2).mul (b.pow K))
  refine (((inner.scale (num 4)).add (names.add rows)).add bits).mono fun i => ?_
  refine (hK i.F i.W i.inner i.S.m i.V i.k i.S.m (X i) (J i) (a i) i.w i.n).trans ?_
  apply Nat.add_le_add
  · apply Nat.add_le_add_left
    unfold Size.spans Size.hosts
    exact le_of_eq (by ring)
  · have hv := Nat.add_le_add (show i.V ≤ i.volume from Nat.le_add_right ..) (hx i)
    rw [← Nat.mul_two] at hv
    exact (Nat.mul_le_mul_right _ hv).trans_eq (mul_assoc ..)

theorem price : Work Size.price := by
  have a := shipping Size.V Size.k Size.p (fun _ => Nat.le_add_right ..) k p links
  have b := shipping Size.V' Size.k' (fun _ => 0) (fun _ => Nat.le_add_left ..) k' (num 0).short (num 1).short
  exact (((a.add b).add dictionary).add (((instruction.add outer).add inner).scale (num 64)))

theorem total : ∃ K, ∀ i : Size, i.header + i.price ≤
    2 ^ i.S.m * (i.M ^ K + 2 ^ i.n * i.T ^ K) + (i.V + i.V') * i.B ^ K := by
  obtain ⟨K, hK⟩ := header.add price
  exact ⟨K, fun i => (hK i).trans_eq (by unfold Size.bound Size.spans Size.hosts Size.volume; ring)⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
end
