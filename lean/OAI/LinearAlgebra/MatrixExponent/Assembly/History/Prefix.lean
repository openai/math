import OAI.LinearAlgebra.MatrixExponent.Spectral.Path
import OAI.LinearAlgebra.MatrixExponent.Spectral.Rule
import Mathlib.Data.Nat.Log
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Dense
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Entry
import OAI.LinearAlgebra.MatrixExponent.Transcript.Match.Reciprocal
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Checks

/-! # Eliminating the private join variables of a routed wire -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Packet.Rule

open Classical
variable {K S E X Y : Type} [Field K] [Fintype S] [Fintype E] [Fintype X] [Fintype Y]

/-- If nonzero contributions force a single setting of every local
joining bit, the serial sum is the product at that setting. -/
theorem series_eval {a b c : E → S} {W : X → S × S} {U : Y → S × S}
    (hf : Rule K (fun e => (a e, b e)) (fun _ : Unit => W))
    (hg : Rule K (fun e => (b e, c e)) (fun _ : Unit => U))
    (v : S) (x y : E → Bool) (u : X ⊕ Y → Bool) (k : E → Bool)
    (hp : ∀ t, hf.entry () v x t (u ∘ Sum.inl) ≠ 0 → hg.entry () v t y (u ∘ Sum.inr) ≠ 0 →
      ∀ e, b e = v → t e = k e) :
    (hf.series hg).entry () v x y u =
      hf.entry () v x k (u ∘ Sum.inl) * hg.entry () v k y (u ∘ Sum.inr) := by
  let T := {e // b e = v}
  let fill (t : T → Bool) (e : E) := if h : b e = v then t ⟨e, h⟩ else false
  let z (e : T) := k e.1
  change (∑ t, hf.entry () v x (fill t) (u ∘ Sum.inl) * hg.entry () v (fill t) y (u ∘ Sum.inr)) = _
  rw [Fintype.sum_eq_single z]
  · have he (e) (h : b e = v) : fill z e = k e := by simp [fill, h, z]
    apply congrArg₂ (· * ·)
    · exact hf.local' _ _ _ _ _ _ _ _ (fun _ _ => rfl) he (fun _ _ => rfl)
    · exact hg.local' _ _ _ _ _ _ _ _ he (fun _ _ => rfl) (fun _ _ => rfl)
  · intro t ht
    by_contra hn
    apply ht
    funext e
    have hh := hp (fill t) (left_ne_zero_of_mul hn) (right_ne_zero_of_mul hn) e.val e.property
    simpa only [fill, dite_eq_left e.property] using hh

theorem path_entry (D : ℕ → E → S) (n : ℕ) (v : S) (x y : E → Bool) (z : Fin n × E → Bool) :
    (Rule.path K D n).entry () v x y z =
      if ∀ (i : Fin (n + 1)) e, D i.val e = v →
        Fin.cons (α := fun _ => E → Bool) x (Function.curry z) i e =
          Fin.snoc (α := fun _ => E → Bool) (Function.curry z) y i e then 1 else 0 := rfl

theorem path_head (D : ℕ → E → S) {n : ℕ} (v : S) (x y : E → Bool) (z : Fin (n + 1) × E → Bool)
    (hn : (Rule.path K D (n + 1)).entry () v x y z ≠ 0) (e : E) (he : D 0 e = v) :
    x e = z (0, e) := by
  rw [path_entry] at hn
  split at hn
  · rename_i h
    simpa [Fin.snoc] using h 0 e he
  · contradiction

end OAI.LinearAlgebra.MatrixExponent.Spectral.Packet.Rule
end

/-!
# Products of trivalent tables on named bits

Collect all factors with the same ordered triple of inputs by
pointwise multiplication. Over a finite field the resulting table
of coefficients has a cubic description length.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Classical Finset
variable (F J : Type) [Field F] [Fintype J]

abbrev Triple := Fin 3 → Option J
abbrev Tables := Triple J → (Fin 3 → Bool) → F
def readBit (x : J → Bool) (s : Option J) : Bool := s.elim false x

def evaluate (c : Tables F J) (x : J → Bool) := ∏ j, c j (readBit J x ∘ j)

def simple : Submonoid ((J → Bool) → F) where
  carrier := Set.range (evaluate F J)
  one_mem' := ⟨1, by ext; simp [evaluate]⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, by ext; simp [evaluate, prod_mul_distrib]⟩

def tripleCost [Fintype F] := (Fintype.card J + 1) ^ 3 * 8 * Nat.clog 2 (Fintype.card F)

omit [Field F] in
theorem triple_bound [Fintype F] : Fintype.card (Tables F J) ≤ 2 ^ tripleCost F J := by
  simp only [Tables, Triple, Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_bool]
  unfold tripleCost
  rw [mul_comm _ (Nat.clog _ _), pow_mul (2 : ℕ), ← pow_mul]
  rw [mul_comm (2 ^ 3)]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _

variable {F J}

theorem one_table (j : Triple J) (g : (Fin 3 → Bool) → F) :
    (fun x => g (readBit J x ∘ j)) ∈ simple F J := by
  refine ⟨fun k z => if k = j then g z else 1, ?_⟩
  ext x
  simp [evaluate]

theorem local_table {I : Type} [Fintype I] (f : (J → Bool) → F) (a : I → Option J)
    (hb : Fintype.card I ≤ 3)
    (hf : ∀ x y, (∀ j, readBit J x (a j) = readBit J y (a j)) → f x = f y) :
    f ∈ simple F J := by
  obtain ⟨e⟩ : Nonempty (I ↪ Fin 3) := Function.Embedding.nonempty_of_card_le (by simpa using hb)
  let addr := Function.extend e a (fun _ => none)
  let pull (x : J → Bool) := readBit J x ∘ addr
  have he (x y : J → Bool) (h : pull x = pull y) : f x = f y := by
    apply hf
    intro i
    simpa only [pull, Function.comp_apply, addr, e.injective.extend_apply] using congrFun h (e i)
  let k (t : Fin 3 → Bool) := f (Function.invFun pull t)
  have h := one_table addr k
  convert h using 1
  funext x
  exact he _ _ (Function.invFun_eq ⟨x, rfl⟩).symm

theorem prod_simple {I : Type} (S : Finset I) (f : I → (J → Bool) → F)
    (hf : ∀ i ∈ S, f i ∈ simple F J) :
    (fun x => ∏ i ∈ S, f i x) ∈ simple F J := by
  convert (simple F J).prod_mem hf using 1
  ext
  exact (Finset.prod_apply ..).symm

theorem check_simple (a b : Option J) :
    (fun x => if readBit J x a = readBit J x b then (1 : F) else 0) ∈ simple F J :=
  one_table ![a, b, none] (fun t => if t 0 = t 1 then 1 else 0)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # A local description of a reset station -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Coloring
open scoped Classical
variable {F : Type} [Field F]

abbrev Addr (e : ℕ) := B e ⊕ B e
abbrev Control (S : Scheme F) (e : ℕ) := Bool × B S.k × (B S.e → Addr e)
abbrev Shape (S : Scheme F) (e : ℕ) := Fin (2 ^ e + 1) × (B e → Control S e) × Tables F (Addr e)
abbrev Recipe (S : Scheme F) (e : ℕ) := Shape S e × (B e → B S.ℓ)

variable {S : Scheme F} {e : ℕ}

def fetch {n u : ℕ} (x : B e → ℕ → Bool) (y : Fin n × Fin u → Bool) : Addr e → ℕ → Bool
  | .inl i, j => x i j
  | .inr i, j => if h : i.val < n ∧ j < u then y (⟨i, h.1⟩, ⟨j, h.2⟩) else false

def prior (o : B S.ℓ ≃ B S.ℓ) (c : Control S e) (t : B S.ℓ) (f : Addr e → ℕ → Bool) : F :=
  if c.1 then (S.decode (o.symm t)).value c.2.1 (fun i j => f (c.2.2 i) j.val) else 1

def run (o : B S.ℓ ≃ B S.ℓ) (u : ℕ) (r : Recipe S e) (x : B e → ℕ → Bool) : F :=
  ∑ y : Fin r.1.1.val × Fin u → Bool,
    (∏ i : B e, prior o (r.1.2.1 i) (r.2 i) (fetch x y)) *
      ∏ j : Fin u, evaluate F (Addr e) r.1.2.2 (fun i => fetch x y i j.val)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-!
# Canonical labels for reset tables

A recipe stores fixed-size controls and the old labels at their actual
bit lengths. Choosing the least label for a function makes the emitted
record independent of the recipe witnessing its length bound.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Coloring
open scoped Classical

variable {F : Type} [Fintype F] (S : Scheme F) (e : ℕ)

def shapeWidth := e + 1 + 2 ^ e * (1 + S.k + 2 ^ S.e * (e + 1)) + tripleCost F (Addr e)
def overhead := shapeWidth S e + 2 ^ e * Dense.used S.ℓ

private theorem card_addr : Fintype.card (Addr e) = 2 ^ (e + 1) := by
  simp only [Addr, B, Fintype.card_sum, Fintype.card_fin, pow_succ, mul_two]

omit [Fintype F] in
private theorem card_control : Fintype.card (Control S e) = 2 ^ (1 + S.k + 2 ^ S.e * (e + 1)) := by
  simp only [Control, Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, card_addr, B, Fintype.card_fin]
  rw [← pow_mul, mul_comm (e + 1), pow_add, pow_add, pow_one, mul_assoc]

omit [Fintype F] in
private theorem card_controls : Fintype.card (B e → Control S e) = 2 ^ (2 ^ e * (1 + S.k + 2 ^ S.e * (e + 1))) := by
  rw [Fintype.card_fun, card_control, ← pow_mul, mul_comm]
  simp only [B, Fintype.card_fin]

private theorem prod_bound (A B C : Type) [Fintype A] [Fintype B] [Fintype C] (a b c : ℕ)
    (ha : Fintype.card A ≤ 2 ^ a) (hb : Fintype.card B ≤ 2 ^ b) (hc : Fintype.card C ≤ 2 ^ c) :
    Fintype.card (A × B × C) ≤ 2 ^ (a + b + c) := by
  rw [Fintype.card_prod, Fintype.card_prod, pow_add, pow_add, mul_assoc]
  exact Nat.mul_le_mul ha (Nat.mul_le_mul hb hc)

private theorem tables_bound (J : Type) [Fintype J] (I : Fintype (Tables F J)) :
    @Fintype.card _ I ≤ 2 ^ tripleCost F J := by
  convert! triple_bound F J using 2

theorem shape_bound : Fintype.card (Shape S e) ≤ 2 ^ shapeWidth S e := by
  have hn : Fintype.card (Fin (2 ^ e + 1)) ≤ 2 ^ (e + 1) := by
    rw [Fintype.card_fin, pow_succ, mul_two]
    exact Nat.add_le_add_left (Nat.two_pow_pos _) _
  exact prod_bound _ _ _ _ _ _ hn (card_controls S e).le (tables_bound (Addr e) inferInstance)

private def shapeCode : Shape S e ↪ B (shapeWidth S e) :=
  (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (shape_bound S e))

variable {S e}

def recipeCode (r : Recipe S e) := Dense.pack (shapeCode S e r.1, r.2)

private theorem recipeCode_inj : Function.Injective (recipeCode (S := S) (e := e)) := by
  intro r s h
  obtain ⟨ha, hb⟩ := Prod.mk.inj (Dense.injective h)
  exact Prod.ext ((shapeCode S e).injective ha) hb

theorem recipe_length (r : Recipe S e) :
    Dense.used (recipeCode r) ≤ overhead S e + Dense.cost r.2 := by
  simpa only [recipeCode, overhead, Dense.header, B, Fintype.card_fin] using
    Dense.length (shapeCode S e r.1, r.2)

variable [Field F] (o : B S.ℓ ≃ B S.ℓ) (u cap : ℕ)

def decoder (c : B cap) : (B e → ℕ → Bool) → F :=
  run o u (Function.invFun (recipeCode (S := S) (e := e)) c.val)

variable (target : (B e → ℕ → Bool) → F)

private def candidates := Finset.univ.filter (fun c : B cap => decoder o u cap c = target)

def canonical : B cap :=
  if h : (candidates o u cap target).Nonempty then (candidates o u cap target).min' h else 0

variable {o u cap target}

theorem canonical_spec (r : Recipe S e) (hr : run o u r = target)
    (hc : overhead S e + Dense.cost r.2 ≤ cap) :
    decoder o u cap (canonical o u cap target) = target ∧
      Dense.used (canonical o u cap target).val ≤ overhead S e + Dense.cost r.2 := by
  let c : B cap := ⟨recipeCode r, Dense.used_le.mp ((recipe_length r).trans hc)⟩
  let t := candidates o u cap target
  have ht : c ∈ t := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    change run o u (Function.invFun recipeCode (recipeCode r)) = target
    rw [Function.leftInverse_invFun recipeCode_inj r]
    exact hr
  have hn : t.Nonempty := ⟨c, ht⟩
  have he : canonical o u cap target = t.min' hn := dite_eq_left hn
  rw [he]
  refine ⟨(Finset.mem_filter.mp (t.min'_mem hn)).2, Dense.used_le.mpr ?_⟩
  exact lt_of_le_of_lt (t.min'_le c ht) (Dense.used_le.mp (recipe_length r))

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-!
# Short tags for a contracted table

Keep the short pointer rows intact. Only the recursively generated
labels need variable-length packing. Unoccupied slots use the zero
tag and so consume no tag bits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History
open Coloring
open scoped Classical
variable {F A T : Type} {m e l s d : ℕ}

namespace Dense

def split (c : (code m e l s d).obj) : B (code m e 0 s d).width × (B m → B l) :=
  ((code m e 0 s d).serial (c.1, fun i => ((c.2 i).1, 0, (c.2 i).2.2)), fun i => (c.2 i).2.1)

private theorem split_inj : Function.Injective (split (m := m) (e := e) (l := l) (s := s) (d := d)) := by
  intro x y h
  obtain ⟨a, b⟩ := Prod.mk.inj h
  obtain ⟨u, v⟩ := Prod.mk.inj ((code m e 0 s d).serial.injective a)
  refine Prod.ext u (funext fun i => ?_)
  have he := congrFun v i
  exact Prod.ext (Prod.mk.inj he).1 (Prod.ext (congrFun b i) (Prod.mk.inj (Prod.mk.inj he).2).2)

def index (c : (code m e l s d).obj) := pack (split c)

theorem index_inj : Function.Injective (index (m := m) (e := e) (l := l) (s := s) (d := d)) :=
  injective.comp split_inj

def overhead (m e l s d : ℕ) := (code m e 0 s d).width + 2 ^ m * used l

theorem index_length (c : (code m e l s d).obj) :
    used (index c) ≤ overhead m e l s d + ∑ i, used ((c.2 i).2.1).val := by
  simpa only [index, overhead, header, cost, split, B, Fintype.card_fin] using length (split c)

/-- Only tags below the chosen limit are requested. On other inputs
the computation may return a dummy value. -/
def encode (q : ℕ) (c : (code m e l s d).obj) : B q :=
  if h : index c < 2 ^ q then ⟨index c, h⟩ else 0

def unpack (q : ℕ) (v : B q) : (code m e l s d).obj :=
  Function.invFun index v.val

theorem encode_val {q : ℕ} {c : (code m e l s d).obj} (h : used (index c) ≤ q) :
    (encode q c).val = index c := by simp [encode, used_le.mp h]

theorem unpack_encode {q : ℕ} {c : (code m e l s d).obj} (h : used (index c) ≤ q) :
    unpack q (encode q c) = c := by
  rw [unpack, encode_val h]
  exact Function.leftInverse_invFun index_inj c

end Dense

namespace Packed
variable [Fintype A] (p : Packed A T e l s d) (g : A ↪ B m) (f : T ↪ B e)

theorem index_length :
    Dense.used (Dense.index (p.encode g f)) ≤
      Dense.overhead m e l s d + ∑ i, Dense.used (p.tag i).val := by
  refine (Dense.index_length _).trans_eq (congrArg _ ?_)
  symm
  refine Fintype.sum_of_injective g g.injective _ _ ?_ ?_
  · intro j hj
    simp only [encode, Function.extend_apply' _ _ _ hj]
    exact Dense.used_zero
  · intro i
    rw [store]

theorem unpack_encode {q : ℕ} (h : Dense.overhead m e l s d + (∑ i, Dense.used (p.tag i).val) ≤ q) :
    Dense.unpack q (Dense.encode q (p.encode g f)) = p.encode g f :=
  Dense.unpack_encode ((p.index_length g f).trans h)

end Packed
end OAI.LinearAlgebra.MatrixExponent.Assembly.History
end

/-!
# Local records for a wire-saving step

The decoder reads only the block record. Global names appear in the
host's common neighbor array. The vacant record has no arguments
and weight one, including in positive characteristic.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Post
open Coloring

/-- Length index, direction, attached flag, neighbor slot, peer slot. -/
abbrev field (d e ℓ : ℕ) : Format :=
  .pair (.addr ℓ) (.pair .bit (.pair .bit (.pair (.addr d) (.addr e))))

abbrev record (d e ℓ : ℕ) (Y : Format) : Format :=
  .pair .bit (.pair (.vec e (field d e ℓ)) Y)

theorem width_record (d e ℓ : ℕ) (Y : Format) :
    (record d e ℓ Y).width = 1 + (2 ^ e * (ℓ + (1 + (1 + (d + e)))) + Y.width) := by
  simp [record, field]

variable {F : Type} [Field F] {m d h e l s ℓ a : ℕ} {Y : Format}

abbrev unused : (field d e ℓ).obj := (0, false, false, 0, 0)

def vacant : (record d e ℓ Y).obj := (false, fun _ => unused, Y.serial.symm 0)

def pattern (M : Menu F l s ℓ) (unpack : Y.obj → (code a e l s ℓ).obj)
    (r : (record d e ℓ Y).obj) : Pattern F d 0 e where
  width _ t := M.length (r.2.1 t).1
  direction _ t := (r.2.1 t).2.1
  peer _ t := if (r.2.1 t).2.2.1 then some ((r.2.1 t).2.2.2.1, 0, (r.2.1 t).2.2.2.2) else none
  value _ x := if r.1 then M.decode (fun t => M.length (r.2.1 t).1) (unpack r.2.2) (fun i => x i.1 i.2) else 1

abbrev scheme (m d h e : ℕ) (Y : Format) (M : Menu F l s ℓ)
    (unpack : Y.obj → (code a e l s ℓ).obj) : Scheme F :=
  ⟨m, d, h, 0, e, (record d e ℓ Y).width, pattern M unpack ∘ (record d e ℓ Y).serial.symm⟩

def write (M : Menu F l s ℓ) (unpack : Y.obj → (code a e l s ℓ).obj)
    (nav : B m → B d → B m) (R : B m → B h → (record d e ℓ Y).obj) :
    (scheme m d h e Y M unpack).format.obj :=
  fun v => (nav v, (record d e ℓ Y).serial ∘ R v)

theorem read_write (M : Menu F l s ℓ) (unpack : Y.obj → (code a e l s ℓ).obj)
    (nav : B m → B d → B m) (R : B m → B h → (record d e ℓ Y).obj)
    (v : (scheme m d h e Y M unpack).Vtx) :
    (scheme m d h e Y M unpack).pattern (write M unpack nav R) v = pattern M unpack (R v.1 v.2.1) :=
  congrArg (pattern M unpack) ((record d e ℓ Y).serial.symm_apply_apply (R v.1 v.2.1))

theorem table_eq (M : Menu F l s ℓ) (unpack : Y.obj → (code a e l s ℓ).obj)
    (out : (scheme m d h e Y M unpack).format.obj)
    (v : (scheme m d h e Y M unpack).Vtx) (r : (record d e ℓ Y).obj)
    (hr : (scheme m d h e Y M unpack).pattern out v = pattern M unpack r)
    (x : (scheme m d h e Y M unpack).LocalPin out v → Bool) :
    (scheme m d h e Y M unpack).table out v x = if r.1 then
      M.decode (fun t => (scheme m d h e Y M unpack).width out (v, t)) (unpack r.2.2) x else 1 := by
  have eq (P : Pattern F d 0 e) (he : P = pattern M unpack r) (j : B 0)
      (x : Positions (P.width j) → Bool) :
      P.value j (fun s i => x ⟨s, i⟩) =
        if r.1 then M.decode (P.width j) (unpack r.2.2) x else 1 := by
    subst P
    rfl
  exact eq _ hr _ x

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Post
end

/-!
# Putting the long part of an occurrence label at the high end

A fixed bijection translates between the physical serialization and
the ordering used to measure label lengths. The same ordering is
used when an old station becomes an atom at the next stage.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History
open Coloring
open scoped Classical

namespace Dense

def concat (h l : ℕ) : B h × B l ≃ B (h + l) :=
  finProdFinEquiv.trans (finCongr (pow_add 2 h l).symm)

theorem concat_length {h l : ℕ} (a : B h) (b : B l) :
    used (concat h l (a, b)).val ≤ used a.val + l := by
  rw [used_le, pow_add 2 (used a.val) l]
  change b.val + 2 ^ l * a.val < _
  calc
    _ < 2 ^ l + 2 ^ l * a.val := Nat.add_lt_add_right b.isLt _
    _ = (a.val + 1) * 2 ^ l := by rw [add_mul, one_mul, mul_comm a.val, add_comm]
    _ ≤ _ := Nat.mul_le_mul_right _ (used_le.mp le_rfl)

end Dense

namespace Post

abbrev headerFmt (d e n : ℕ) := Format.pair .bit (.vec e (field d e n))
abbrev width (d e n l : ℕ) := (record d e n (.addr l)).width

private theorem width_eq (d e n l : ℕ) : l + (headerFmt d e n).width = width d e n l := by
  simp only [width, headerFmt, record, Format.width_pair, Format.width_addr]
  omega

def order (d e n l : ℕ) : B (width d e n l) ≃ B (width d e n l) :=
  (record d e n (.addr l)).serial.symm |>.trans ((Equiv.prodAssoc _ _ _).symm.trans
    ((Equiv.prodComm _ _).trans (((Equiv.refl _).prodCongr (headerFmt d e n).serial).trans
      ((Dense.concat _ _).trans (finCongr (congrArg (2^·) (width_eq d e n l)))))))

theorem order_length {d e n l : ℕ} (c : (record d e n (.addr l)).obj) :
    Dense.used (order d e n l ((record d e n (.addr l)).serial c)).val ≤
      Dense.used c.2.2.val + (headerFmt d e n).width := by
  simp only [order, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact Dense.concat_length c.2.2 ((headerFmt d e n).serial (c.1, c.2.1))

end Post

namespace Kind
variable {F : Type} [Field F] (S : Scheme F) (P : Packing.Gadget F) (c : ℕ)

abbrev Small := B S.k ⊕ Role P ⊕ B c

def width := Dense.used (Fintype.card (Small S P c))

private def tags : Small S P c ↪ B (width S P c) :=
  (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (le_of_lt (Dense.used_le.mp le_rfl)))

variable (o : B S.ℓ ≃ B S.ℓ)

private def parts : Kind S P c → B S.ℓ × Small S P c
  | .inl x => (o x.1, .inl x.2)
  | .inr x => (0, .inr x)

private theorem parts_inj : Function.Injective (parts S P c o) := by
  rintro (⟨x, i⟩|x) (⟨y, j⟩|y) h <;> simp [parts] at h ⊢ <;> exact h

def names : Kind S P c ↪ B (S.ℓ + width S P c) :=
  (⟨parts S P c o, parts_inj S P c o⟩ : Kind S P c ↪ _).trans
    (((Function.Embedding.refl _).prodMap (tags S P c)).trans (Dense.concat _ _).toEmbedding)

def carried (j : Kind S P c) := Dense.used (parts S P c o j).1.val

theorem names_length (j : Kind S P c) :
    Dense.used (names S P c o j).val ≤ carried S P c o j + width S P c :=
  Dense.concat_length _ _

@[simp] theorem carried_old (x : B S.ℓ) (i : B S.k) :
    carried S P c o (.inl (x, i)) = Dense.used (o x).val := rfl

@[simp] theorem carried_new (i : Role P ⊕ B c) : carried S P c o (.inr i) = 0 :=
  Dense.used_zero

end Kind

namespace Post

variable {F A T : Type} [Field F] [Fintype A]
    {m e d s n c : ℕ} (S : Scheme F) (P : Packing.Gadget F) (o : B S.ℓ ≃ B S.ℓ)
    (p : Packed A T e (S.ℓ + Kind.width S P c) s n)
    (g : A ↪ B m) (f : T ↪ B e)

/-- Header cost includes role names, widths and pointers. It depends
on the previous label bound only through its logarithm. -/
def bookkeeping (m e s n old role : ℕ) :=
  Dense.overhead m e (old + role) s n + 2 ^ m * role

theorem packed_length (t : A → Kind S P c) (ht : p.tag = Kind.names S P c o ∘ t) :
    Dense.used (Dense.index (p.encode g f)) ≤
      bookkeeping m e s n S.ℓ (Kind.width S P c) + ∑ i, Kind.carried S P c o (t i) := by
  refine (p.index_length g f).trans ?_
  have ha : Fintype.card A ≤ 2 ^ m := by simpa using Fintype.card_le_of_injective g g.injective
  have h : (∑ i, Dense.used (p.tag i).val) ≤ ∑ i, (Kind.carried S P c o (t i) + Kind.width S P c) := by
    rw [ht]
    exact Finset.sum_le_sum fun i _ => Kind.names_length S P c o (t i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] at h
  have h' := Nat.mul_le_mul_right (Kind.width S P c) ha
  unfold bookkeeping
  omega

/-- The receipt need only retain the effective lengths of its
ancestors. In particular the maximum old length is not multiplied
by the number of candidate ports or atoms. -/
theorem stored_length {l bound : ℕ} (t : A → Kind S P c)
    (ht : p.tag = Kind.names S P c o ∘ t)
    (hb : (∑ i, Kind.carried S P c o (t i)) ≤ bound)
    (hl : bookkeeping m e s n S.ℓ (Kind.width S P c) + bound ≤ l)
    (v : (record d e n (.addr l)).obj) (hv : v.2.2 = Dense.encode l (p.encode g f)) :
    Dense.unpack l v.2.2 = p.encode g f ∧
    Dense.used (order d e n l ((record d e n (.addr l)).serial v)).val ≤
      (headerFmt d e n).width + bookkeeping m e s n S.ℓ (Kind.width S P c) + bound := by
  have h := (packed_length S P o p g f t ht).trans (Nat.add_le_add_left hb _)
  refine ⟨by rw [hv]; exact Dense.unpack_encode (h.trans hl), ?_⟩
  have he := order_length v
  rw [hv, Dense.encode_val (h.trans hl)] at he
  omega

end Post
end OAI.LinearAlgebra.MatrixExponent.Assembly.History
end

/-! # Decoding the emitted span records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.Allocation
open Coloring Packing
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h z a : ℕ}
  {P : Gadget F} {G : HostNet F L h (P.b * z)}
  {Δ D k : ℕ} {B' : ℝ} {g : Grouping G.N G.C Δ D k B' G.load}
  {m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix} {i : g.Choice m P}
  {S : Scheme F} {r : S.format.obj} {p : S.Presentation r G.diagram}
  {q : G.Projection Δ D a}
  {m' d h' e ℓ n l s : ℕ} {Y : Format} {M : Menu F l s ℓ}
  {u : Y.obj → (code n e l s ℓ).obj}

local notation "U" => Post.scheme m' d h' e Y M u
local notation "Face'" => Face g m P i p
local notation "Host" => endHost (p := p) (q := q)

variable (A : Allocation P G g m i p q (Post.scheme m' d h' e Y M u))

def header (A : Allocation P G g m i p q U) (size : Face' → B ℓ) : Face' → (Post.field d e ℓ).obj
  | .inl j => (size (.inl j), S.direction r (p.vertex j.val.1, j.val.2), false, 0, 0)
  | .inr (b, t) =>
    (size (.inr (b, t)), t, true, A.index (Host b t) (Host b (!t)), A.unitSeat b (!t))

variable {nav : B m' → B d → B m'} {R : B m' → B h' → (Post.record d e ℓ Y).obj}
  {size : Face g m P i p → B ℓ}

local notation "out" => Post.write M u nav R

/-- The active record fields are indexed only by the local seats.
Unused argument seats have zero length and no peer. -/
structure Emitted (A : Allocation P G g m i p q U) (size : Face' → B ℓ) (nav : B m' → B d → B m')
    (R : B m' → B h' → (Post.record d e ℓ Y).obj) : Prop where
  zero : M.length 0 = 0
  length : ∀ j, M.length (size j) = visibleWidth g m P i p z j
  active : ∀ v, (R (A.vertex v).1 (A.vertex v).2.1).1 = true
  vacant : ∀ v : (U).Vtx, v ∉ Set.range A.vertex → (R v.1 v.2.1).1 = false
  used : ∀ j : Face', let t : (U).Span := A.span j
    (R t.1.1 t.1.2.1).2.1 t.2 = A.header size j
  idle : ∀ t : (U).Span, t ∉ Set.range A.span → (R t.1.1 t.1.2.1).2.1 t.2 = Post.unused
  hop : ∀ (b : g.Survivors m P i) t, let v := Host b t
    let w := Host b (!t)
    nav (A.host v) (A.index v w) = A.host w

namespace Emitted
variable {A} (H : A.Emitted size nav R)

include H in
theorem lengths : A.Lengths out where
  used j := by
    rw [Scheme.width, Post.read_write]
    change M.length ((R _ _).2.1 _).1 = _
    rw [H.used j]
    rcases j with j|⟨b, t⟩ <;> exact H.length _
  idle t ht := by
    rw [Scheme.width, Post.read_write]
    change M.length ((R _ _).2.1 _).1 = _
    rw [H.idle t ht]
    exact H.zero

include H in
theorem exposed_direction (j : p.BorderSpan) :
    (U).direction out (A.span (.inl j)) = S.direction r (p.vertex j.val.1, j.val.2) := by
  rw [Scheme.direction, Post.read_write]
  change ((R _ _).2.1 _).2.1 = _
  rw [H.used]
  rfl

theorem agrees (hz : 0 < z)
    (hs : ∀ v t, M.decode (fun a => (U).width out (A.vertex v, a))
        (u (R (A.vertex v).1 (A.vertex v).2.1).2.2) t =
      Transcript.sample ((g.contract m P G.units hz i).table v) (t ∘ A.pin H.lengths hz v)) :
    A.Agrees H.lengths hz where
  sample v t := by
    rw [Post.table_eq M u out _ _ (Post.read_write _ _ _ _ _), H.active]
    exact hs v t
  vacant v hv t := by
    rw [Post.table_eq M u out _ _ (Post.read_write _ _ _ _ _), H.vacant v hv]
    rfl
  outside j := by
    rw [Scheme.peer, Post.read_write]
    simp only [Post.pattern, H.used, header, Bool.false_eq_true, ↓reduceIte, Option.map_none]
  idle t ht := by
    rw [Scheme.peer, Post.read_write]
    simp only [Post.pattern, H.idle t ht, Post.unused, Bool.false_eq_true, ↓reduceIte, Option.map_none]
  dir b t := by
    rw [Scheme.direction, Post.read_write]
    simp only [Post.pattern, H.used, header]
  link b t := by
    dsimp only
    rw [Post.read_write]
    simp only [Post.pattern, H.used, header, ↓reduceIte]
  nav b t := H.hop b t

/-- Every original exterior offset retains its span length and orientation. -/
theorem boundary (hz : 0 < z) (hA : A.Agrees H.lengths hz) (t : slots x ⊕ slots y) :
    let p' := A.presentation H.lengths hz hA
    let b := p.toSeating.ends (boundaryEnd _ t)
    let b' := p'.toSeating.ends (boundaryEnd _ t)
    (U).width out b'.1 = S.width r b.1 ∧ (U).direction out b'.1 = S.direction r b.1 ∧
      b'.2.val = b.2.val := by
  obtain ⟨j, rfl⟩ := p.exteriorBits.surjective t
  dsimp only [presentation]
  rw [p.border_pin, A.exposed_pin]
  exact ⟨H.lengths.used (.inl j.1), H.exposed_direction j.1, rfl⟩

theorem floor (hz : 0 < z) (hA : A.Agrees H.lengths hz) {w : ℕ}
    (hw : ∀ b, w ≤ p.borderWidth b) :
    ∀ b, w ≤ (A.presentation H.lengths hz hA).borderWidth b := by
  let p' := A.presentation H.lengths hz hA
  intro b
  let j : p'.BorderBit := ⟨b, ⟨0, b.property.1⟩⟩
  obtain ⟨t, ht⟩ := p.exteriorBits.surjective (p'.exteriorBits j)
  have h := (H.boundary hz hA (p'.exteriorBits j)).1
  rw [p'.border_pin, ← ht, p.border_pin] at h
  exact (hw _).trans_eq h.symm

end Emitted
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.Allocation
end

/-! # Constructing the visible span records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.Allocation
open Coloring Packing
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h z a : ℕ}
  {P : Gadget F} {G : HostNet F L h (P.b * z)}
  {Δ D k : ℕ} {B' : ℝ} {g : Grouping G.N G.C Δ D k B' G.load}
  {m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix} {i : g.Choice m P}
  {S : Scheme F} {r : S.format.obj} {p : S.Presentation r G.diagram}
  {q : G.Projection Δ D a}
  {m' d h' e ℓ n l s : ℕ} {Y : Format} {M : Menu F l s ℓ}
  {u : Y.obj → (code n e l s ℓ).obj}

local notation "U" => Post.scheme m' d h' e Y M u
local notation "Face'" => Face g m P i p
local notation "Host" => endHost (p := p) (q := q)

variable (A : Allocation P G g m i p q (Post.scheme m' d h' e Y M u))

variable (size : Face g m P i p → B ℓ) (data : Site G.V h → Y.obj)

def fields (v : Site G.V h) : B e → (Post.field d e ℓ).obj :=
  Function.extend (A.seat v) (fun j => A.header size j.val) (fun _ => Post.unused)

def localRecord (v : Site G.V h) : (Post.record d e ℓ Y).obj :=
  (true, A.fields size v, data v)

def records (x : B m') (y : B h') : (Post.record d e ℓ Y).obj :=
  Function.extend A.vertex (A.localRecord size data) (fun _ => Post.vacant) (x, y, 0)

theorem record_at (v : Site G.V h) :
    A.records size data (A.vertex v).1 (A.vertex v).2.1 = A.localRecord size data v :=
  A.vertex.injective.extend_apply _ _ v

theorem record_vacant (v : (U).Vtx) (hv : v ∉ Set.range A.vertex) :
    A.records size data v.1 v.2.1 = Post.vacant := by
  have he : (v.1, v.2.1, (0 : B 0)) = v := Prod.ext rfl (Prod.ext rfl (Fin.eq_zero _).symm)
  unfold records
  rw [he]
  exact Function.extend_apply' _ _ _ hv

variable (nav : B m' → B d → B m')

theorem emitted (h₀ : M.length 0 = 0) (hsize : ∀ j, M.length (size j) = visibleWidth g m P i p z j)
    (hop : ∀ (b : g.Survivors m P i) t, nav (A.host (Host b t))
      (A.index (Host b t) (Host b (!t))) = A.host (Host b (!t))) :
    A.Emitted size nav (A.records size data) where
  zero := h₀
  length := hsize
  active v := by rw [record_at]; rfl
  vacant v hv := by rw [record_vacant _ _ _ _ hv]; rfl
  used j := by
    let v := whereAt g m P G.units i p j
    change (A.records size data (A.vertex v).1 (A.vertex v).2.1).2.1 (A.slot j) = _
    rw [record_at]
    let e : Visible g m P G.units i p v := ⟨j, rfl⟩
    change A.fields size v (A.seat v e) = A.header size e.val
    rw [fields, (A.seat v).injective.extend_apply]
  idle t ht := by
    rcases t with ⟨v, j⟩
    by_cases hv : v ∈ Set.range A.vertex
    · obtain ⟨w, rfl⟩ := hv
      rw [record_at]
      have hn : j ∉ Set.range (A.seat w) := by
        rintro ⟨e, rfl⟩
        exact ht ⟨e.val, Prod.ext (congrArg A.vertex e.property) (A.slot_eq w e)⟩
      change A.fields size w j = _
      rw [fields, Function.extend_apply' _ _ _ hn]
    · rw [record_vacant _ _ _ _ hv]
      rfl
  hop := hop

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.Allocation
end
