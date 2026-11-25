import OAI.LinearAlgebra.MatrixExponent.Assembly.Group.Model
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reads

/-! # Local adjacency from slot equality masks and edge flags -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Group
open Coloring

abbrev Checks (q d : ℕ) := Format.pair (.vec q (.vec d (.vec q .bit))) (.vec q (Flags d))
abbrev Adjacency (q : ℕ) := Format.vec q (Flags q)

variable {q d t : ℕ}

def adjacency (x : (Checks q d).obj) (i k : B q) : Bool × Bool :=
  (decide (∃ j, x.1 i j k = true ∧ (x.2 i j).1 = true),
   decide (∃ j, x.1 i j k = true ∧ (x.2 i j).2 = true))

variable (F : Type) [Field F]

private theorem any_flags (hd : 2 ^ d ≤ t) :
    Cheap F 0 t (Flags d) .bit
      (fun a => decide (∃ j, (a j).1 = true ∧ (a j).2 = true)) 3 := by
  let f (z : Bool × Bool) := z.1 && z.2
  have both := Circuit.map (A := .pair .bit .bit) (D := .bit) (fun _ : B d => f)
    (fun _ => Coloring.small (F := F) (A := .pair .bit .bit) (by simp) f)
  have one : Circuit F (.vec d .bit) .bit (fun x => decide (∃ j, x j = true)) (5 * 2 ^ d + 1) := by
    have net := (Install.BNet.any F (B d)).pull (fun i => (i, ()))
    unfold Circuit
    convert net using 1 <;> try rfl
    · funext a i
      change decide (∃ j, a (j, ()) = true) = _
      simp [Function.comp_apply]
    · simp
      omega
  have net : Circuit F (Flags d) .bit
      (fun a => decide (∃ j, (a j).1 = true ∧ (a j).2 = true))
      (2 ^ d * 200 + (5 * 2 ^ d + 1)) := by
    convert both.comp one using 1
    funext x
    simp [f]
  refine ⟨_, net, ?_⟩
  simp only [Flags, Format.width_vec, Format.width_pair]
  rw [Format.width_bit]
  ring_nf
  omega

theorem cheap_adjacency (hq : 2 ^ q ≤ t) (hd : 2 ^ d ≤ t) :
    Cheap F 0 t (Checks q d) (Adjacency q) adjacency 16 := by
  have ha : (Checks q d).width ≤ 2 ^ 0 * (100 + t) ^ 3 := by
    simp only [Checks, Flags, Format.width_pair, Format.width_vec]
    rw [Format.width_bit]
    calc
      _ ≤ t * (t * (t * 1)) + t * (t * (1 + 1)) := by gcongr
      _ ≤ _ := by ring_nf; omega
  have hb : (Flags d).width ≤ 2 ^ 0 * (100 + t) ^ 3 := by
    simp only [Flags, Format.width_pair, Format.width_vec]
    rw [Format.width_bit]
    ring_nf
    omega
  have edge (i k : B q) : Cheap F 0 t (Checks q d) (.pair .bit .bit) (fun x => adjacency x i k) 6 := by
    have l : Cheap F 0 t (Checks q d) (Flags d) (fun x j => (x.1 i j k, (x.2 i j).1)) 4 :=
      Cheap.project F ha hb (fun p => p.2.elim (fun z => .inl (i, p.1, k, z))
        (fun z => .inr (i, p.1, .inl z))) (by rintro x ⟨j, z|z⟩ <;> rfl)
    have r : Cheap F 0 t (Checks q d) (Flags d) (fun x j => (x.1 i j k, (x.2 i j).2)) 4 :=
      Cheap.project F ha hb (fun p => p.2.elim (fun z => .inl (i, p.1, k, z))
        (fun z => .inr (i, p.1, .inr z))) (by rintro x ⟨j, z|z⟩ <;> rfl)
    exact (l.comp (any_flags F hd)).pair (r.comp (any_flags F hd))
  exact (Cheap.share _ (fun i => Cheap.share _ (edge i) hq) hq).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Group
end

/-! # Graph and core flags for child hosts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Child

open Coloring Install Packing
open scoped Classical

variable {m d a h b q t : ℕ} {V : Type}

/-- Select a graph mask and suppress every slot of an idle parent. -/
def fromGroup (X : (Group.Input m d a h b).obj) (core : Bool) : (Input m d).obj :=
  fun i j => ((X i).2.1 && (if core then ((X i).2.2.1 j).2 else ((X i).2.2.1 j).1), (X i).1 j)

theorem presents {X : (Group.Input m d a h b).obj} {g : V ↪ B m}
    {E C : V → Finset V} {l : V × Cell a → Cell h → ℝ} {f : B b → ℝ}
    (H : Group.Presents X g E C l f) (core : Bool) :
    Presents (if core then C else E) g (fromGroup X core) := by
  constructor
  · intro v u
    have live := (H.live (g v)).mpr ⟨v, rfl⟩
    have mask (y : V) : y ∈ (if core then C else E) v ↔
        ∃ j, (X (g v)).1 j = g y ∧ (fromGroup X core (g v) j).1 = true := by
      cases core
      · simpa [fromGroup, live] using H.edge v y
      · simpa [fromGroup, live] using H.core v y
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨y, hy⟩ := H.closed v j
      exact ⟨y, (mask y).mpr ⟨j, hy.symm, congrArg Prod.fst hj⟩, hy.trans (congrArg Prod.snd hj)⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨j, he, hj⟩ := (mask y).mp hy
      exact ⟨j, Prod.ext hj he⟩
  · intro v hv j
    have he : (X v).2.1 = false := Bool.eq_false_iff.mpr (fun h => hv ((H.live v).mp h))
    simp [fromGroup, he]

private theorem mask_depends (core : Bool) :
    Depends ((Input m d).code ∘ (fun x => fromGroup x core) ∘ (Group.Input m d a h b).code.symm) 2 := by
  let T := Group.Input m d a h b
  rintro ⟨i, j, k | k⟩
  · let live : T.pins := (i, .inr (.inl ()))
    let bit : T.pins := (i, .inr (.inr (.inl (j, if core then .inr () else .inl ()))))
    refine ⟨{live, bit}, Finset.card_le_two, fun x y he => ?_⟩
    have hl := he live (by simp)
    have hb := he bit (by simp)
    cases core <;> exact congrArg₂ (· && ·) hl hb
  · let pin : T.pins := (i, .inl (j, k))
    refine ⟨{pin}, by simp, fun x y he => ?_⟩
    exact (congrFun (T.code.apply_symm_apply x) pin).trans
      ((he pin (by simp)).trans (congrFun (T.code.apply_symm_apply y) pin).symm)

variable (F : Type) [Field F]

theorem fromGroup_circuit (core : Bool) :
    Circuit F (Group.Input m d a h b) (Input m d) (fun X => fromGroup X core)
      ((Group.Input m d a h b).width + 68 * (Input m d).width) :=
  (mask_depends core).bnet F

theorem cheap_fromGroup (core : Bool) (hm : m ≤ t) (hd : 2 ^ d ≤ t)
    (ha : 2 ^ a ≤ t) (hh : 2 ^ h ≤ t) (hb : b ≤ t) :
    Cheap F m t (Group.Input m d a h b) (Input m d) (fun X => fromGroup X core) 5 := by
  refine ⟨_, fromGroup_circuit F core, ?_⟩
  let A := Group.Input m d a h b
  let E := Input m d
  change A.width + E.width + (A.width + 68 * E.width) ≤ _
  have hi : A.width ≤ 2 ^ m * (100 + t) ^ 4 := by
    simp only [A, Group.Input, Fmt.bank, Group.Parcel, Group.Flags,
      Format.width_vec, Format.width_pair, Format.width_addr]
    rw [Format.width_bit]
    apply Nat.mul_le_mul_left
    calc
      _ ≤ t * t + (1 + (t * (1 + 1) + t * (t * t))) := by gcongr
      _ ≤ _ := by ring_nf; omega
  have ho : E.width ≤ 2 ^ m * (100 + t) ^ 4 := by
    simp only [E, Input, Format.width_vec, Format.width_pair, Format.width_addr]
    rw [Format.width_bit]
    apply Nat.mul_le_mul_left
    calc
      _ ≤ t * (1 + t) := by gcongr
      _ ≤ _ := by ring_nf; omega
  calc
    _ ≤ 100 * (2 ^ m * (100 + t) ^ 4) := by omega
    _ ≤ _ := by
      rw [mul_comm 100, pow_succ (100 + t) 4, ← mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.le_add_right 100 t)

/-- The short core list and the full list need not use the same slot indices. -/
def coreFlags (g : B m → B d → B m) (c : B m → B q → B m) (x : B m) (i : B d) :=
  decide (∃ k, c x k = g x i)

private theorem any_net (hq : 2 ^ q ≤ t) :
    Cheap F 0 t (.vec q .bit) .bit (fun x => decide (∃ i, x i = true)) 2 := by
  have net := (BNet.any F (B q)).rename (Equiv.prodUnique (B q) Unit).symm (.refl _)
  refine ⟨2 * Fintype.card (B q) + 1, ?_, ?_⟩
  · unfold Circuit
    convert net using 1
    funext x u
    change decide (∃ i, x (i, ()) = true) = _
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, decide_eq_true_eq]
    rfl
  · rw [Format.width_vec, Format.width_bit, Fintype.card_fin]
    ring_nf
    omega

theorem cheap_coreFlags (hm : m ≤ t) (hd : 2 ^ d ≤ t) (hq : 2 ^ q ≤ t) :
    Cheap F m t (.pair (Neighborhood.Rows m d) (Neighborhood.Rows m q))
      (.vec m (.vec d .bit)) (fun x => coreFlags x.1 x.2) 16 := by
  let A := Format.pair (.vec d (.addr m)) (.vec q (.addr m))
  have ha : A.width ≤ 2 ^ 0 * (100 + t) ^ 3 := by
    rw [Format.width_pair, Format.width_vec, Format.width_vec, Format.width_addr]
    calc
      _ ≤ t * t + t * t := by gcongr
      _ ≤ _ := by ring_nf; omega
  have hb : (Format.pair (.addr m) (.addr m)).width ≤ 2 ^ 0 * (100 + t) ^ 3 := by
    rw [Format.width_pair, Format.width_addr]
    ring_nf
    omega
  have cmp (i : B d) (j : B q) :
      Cheap F 0 t A .bit (fun x => decide (x.2 j = x.1 i)) 5 := by
    have h : Cheap F 0 t A (.pair (.addr m) (.addr m)) (fun x => (x.2 j, x.1 i)) 4 :=
      Cheap.project F ha hb (Sum.elim (fun k => .inr (j, k)) (fun k => .inl (i, k)))
        (by rintro x (k | k) <;> rfl)
    exact h.comp (cheap_eq F hm)
  have one (i : B d) : Cheap F 0 t A .bit (fun x => decide (∃ j, x.2 j = x.1 i)) 8 := by
    have h := (Cheap.share _ (cmp i) hq).comp (any_net F hq)
    convert h using 1 <;> try rfl
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, decide_eq_true_eq]
  have pairWidth : (Format.pair (Neighborhood.Rows m d) (Neighborhood.Rows m q)).width ≤
      2 ^ m * (100 + t) ^ 3 := by
    rw [Format.width_pair, Format.width_vec m, Format.width_vec m, ← mul_add, ← Format.width_pair]
    exact Nat.mul_le_mul_left _ (by simpa only [pow_zero, one_mul] using ha)
  have net := (Cheap.id F pairWidth).zip.comp
    (Cheap.map (h := m) _ (fun _ => Cheap.share _ one hd))
  exact net.mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Child
end

/-!
# Resolving short child contacts from an old window

Both endpoints are specified relative to a common old host by a
window index and an interval code. Only the mask preparation reads
long host names. The same mask works for every block of that host.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Child

open Coloring hiding Rows
open Install Neighborhood
open scoped Classical
variable {m e q k t : ℕ}

def extend (e : ℕ) (u : (Rows m q).obj) : (Rows (m + e) (q + e)).obj :=
  fun x i => (Match.rowIndex m e).symm
    (u (Match.rowIndex m e x).1 (Match.rowIndex q e i).1, (Match.rowIndex q e i).2)

def mask (u : (Rows m q).obj) (g : (Rows (m + e) k).obj) : (Mask m (q + e) k).obj :=
  fun x => maskRows (extend e u) g ((Match.rowIndex m e).symm (x, 0))

theorem index_eq (u : (Rows m q).obj) (g : (Rows (m + e) k).obj) (x : B m) (i j : B q) (v w : B e) :
    index g ((Match.rowIndex m e).symm (u x i, v)) ((Match.rowIndex m e).symm (u x j, w)) =
      select (fun s => mask u g x ((Match.rowIndex q e).symm (i, v)) s ((Match.rowIndex q e).symm (j, w))) := by
  simp only [index, mask, maskRows, extend, Equiv.apply_symm_apply]

private theorem extend_depends :
    Depends ((Rows (m + e) (q + e)).code ∘ extend e ∘ (Rows m q).code.symm) 1 := by
  rintro ⟨x, i, b⟩
  obtain ⟨z, hz⟩ := Match.append_pin m e b
  let p := (Match.rowIndex m e x).1
  let j := Match.rowIndex q e i
  have key (a : (Rows m q).pins → Bool) :
      ((Rows (m + e) (q + e)).code ∘ extend e ∘ (Rows m q).code.symm) a (x, i, b) =
        Sum.elim (fun l => a (p, j.1, l)) ((Format.addr e).code j.2) z := by
    refine (hz _ _).trans ?_
    cases z with
    | inl l => exact congrFun ((Rows m q).code.apply_symm_apply a) (p, j.1, l)
    | inr _ => rfl
  cases z with
  | inl l =>
    refine ⟨{(p, j.1, l)}, by simp, fun a b h => ?_⟩
    rw [key, key]
    exact h _ (by simp)
  | inr l => exact ⟨∅, by simp, fun a b _ => (key a).trans (key b).symm⟩

private theorem mask_width (hq : 2 ^ q ≤ t) (hk : 2 ^ k ≤ t) :
    (Mask m q k).width ≤ 2 ^ m * (100 + t) ^ 3 := by
  simp only [Mask, Format.width_vec]
  rw [Format.width_bit, mul_one]
  rw [pow_succ, pow_two, mul_assoc]
  gcongr <;> omega

/-- Cost is independent of the number of blocks per child site. -/
theorem cheap_mask (F : Type) [Field F] (hm : m + e ≤ t) (hq : 2 ^ (q + e) ≤ t) (hk : 2 ^ k ≤ t) :
    Cheap F (m + e) t (.pair (Rows m q) (Rows (m + e) k)) (Mask m (q + e) k)
      (fun x => mask x.1 x.2) 40 := by
  let M := m + e
  let Q := q + e
  have hQ : 2 ^ Q ≤ t := hq
  have hp : 2 ^ m ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  have hq' : 2 ^ q ≤ t := (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)).trans hq
  have h₁ : (Rows m q).width ≤ 2 ^ M * (100 + t) ^ 2 := by
    rw [Format.width_vec, Format.width_vec, Format.width_addr, pow_two]
    gcongr <;> omega
  have h₂ : (Rows M Q).width ≤ 2 ^ M * (100 + t) ^ 2 := by
    rw [Format.width_vec, Format.width_vec, Format.width_addr, pow_two]
    gcongr <;> omega
  have h₃ : (Rows M k).width ≤ 2 ^ M * (100 + t) ^ 2 := by
    rw [Format.width_vec, Format.width_vec, Format.width_addr, pow_two]
    gcongr <;> omega
  have ha : Cheap F M t (Rows m q) (Rows M Q) (extend e) 3 := by
    refine ⟨_, extend_depends.bnet F, ?_⟩
    change (Rows m q).width + (Rows M Q).width +
      ((Rows m q).width + 34 * (Rows M Q).width) ≤ _
    have hb : 100 * (2 ^ M * (100 + t) ^ 2) ≤ 2 ^ M * (100 + t) ^ 3 := by
      rw [pow_succ' (100 + t) 2, mul_left_comm 100]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    omega
  let A := Mask M Q k
  let D := Mask m Q k
  have hd : D.width ≤ 2 ^ M * (100 + t) ^ 3 := (mask_width hq hk).trans (Nat.mul_le_mul_right _ hp)
  have pr : Cheap F M t A D (fun a x => a ((Match.rowIndex m e).symm (x, 0))) 4 :=
    Cheap.project F (mask_width hq hk) hd (fun j => ((Match.rowIndex m e).symm (j.1, 0), j.2))
      (fun _ _ => rfl)
  have mid := cheap_maskRows F hm hq hk
  have hi : (Format.pair (Rows m q) (Rows M k)).width ≤ 2 ^ M * (100 + t) ^ 3 := by
    rw [Format.width_pair, pow_succ (100 + t) 2, ← mul_assoc]
    have hle := Nat.mul_le_mul_left (2 ^ M * (100 + t) ^ 2) (show 2 ≤ 100 + t by omega)
    omega
  let base := Cheap.id F hi
  exact ((((base.fst.comp ha).pair base.snd).comp mid).comp pr).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Child
end

/-! # Comparing child IDs along two short paths -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Child
open Coloring hiding Rows
open Neighborhood Window

variable {d r : ℕ}

private theorem walkOfList (p : List (B d)) (hp : p.length ≤ r) :
    ∃ u : Walk d r, ∀ m (g : (Rows m d).obj) x, run g r u x = visit g x p := by
  induction r generalizing p with
  | zero =>
    have : p = [] := List.length_eq_zero_iff.mp (by omega)
    subst p
    exact ⟨(), fun _ _ _ => rfl⟩
  | succ r ih =>
    induction p using List.reverseRecOn with
    | nil =>
      obtain ⟨u, hu⟩ := ih [] (by simp)
      exact ⟨(none, u), fun m g x => hu m g x⟩
    | append_singleton p i _ =>
      obtain ⟨u, hu⟩ := ih p (by simpa using hp)
      refine ⟨(some i, u), fun m g x => ?_⟩
      simpa [run, visit] using hu m g (g x i)

/-- The slot for each path is independent of the navigation table. -/
theorem visit_slot (p : List (B d)) (hp : p.length ≤ r) :
    ∃ j : B ((d + 1) * r), ∀ m (g : (Rows m d).obj) x, walks r g x j = visit g x p := by
  obtain ⟨u, hu⟩ := walkOfList p hp
  obtain ⟨j, hj⟩ := path_surjective d r u
  exact ⟨j, fun m g x => by rw [walks, hj, hu]⟩

variable {m m' e k : ℕ} {g : (Rows m d).obj} {g' : (Rows m' d).obj}
  {a : (Rows (m + e) k).obj} {a' : (Rows (m' + e) k).obj} {x : B m} {x' : B m'}
  (he : mask (walks r g) a x = mask (walks r g') a' x')
  {p q : List (B d)} (hp : p.length ≤ r) (hq : q.length ≤ r)
include he hp hq

theorem index_agree (v w : B e) :
    index a ((Match.rowIndex m e).symm (visit g x p, v)) ((Match.rowIndex m e).symm (visit g x q, w)) =
      index a' ((Match.rowIndex m' e).symm (visit g' x' p, v)) ((Match.rowIndex m' e).symm (visit g' x' q, w)) := by
  obtain ⟨i, hi⟩ := visit_slot p hp
  obtain ⟨j, hj⟩ := visit_slot q hq
  rw [← hi, ← hj, ← hi, ← hj, index_eq, index_eq, he]

/-- Slot zero names the host itself, so the mask also remembers
equality of parent names along arbitrary short walks. -/
theorem visit_agree (ha : ∀ i, a i 0 = i) (ha' : ∀ i, a' i 0 = i) :
    visit g x p = visit g x q ↔ visit g' x' p = visit g' x' q := by
  obtain ⟨i, hi⟩ := visit_slot p hp
  obtain ⟨j, hj⟩ := visit_slot q hq
  let u := (Match.rowIndex ((d + 1) * r) e).symm (i, 0)
  let v := (Match.rowIndex ((d + 1) * r) e).symm (j, 0)
  have hv := congrFun (congrFun (congrFun he u) 0) v
  simpa only [mask, maskRows, ha, ha', extend, u, v, Equiv.apply_symm_apply, Equiv.apply_eq_iff_eq,
    Prod.mk.injEq, and_true, decide_eq_decide, hi, hj] using hv

end OAI.LinearAlgebra.MatrixExponent.Assembly.Child
end

/-!
# Delivering patches

The expensive long-address masks are shared across groups. The load
records for all groups are sent together in a single tagged exchange.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Group
open Coloring

variable {F : Type} [Field F] {m d a h b : ℕ}
local notation "Q" => ((d + 1) * h)
local notation "X₀" => Input m d a h b
local notation "Y₀" => Patches m d a h b
local notation "P₀" => Parcel d a h b
local notation "Mask" => Neighborhood.Mask m Q d
local notation "Bank" => Fmt.bank m Q P₀
local notation "Views" => Format.vec m (Format.vec Q P₀)
local notation "Overhead" => (2 ^ m * (100 + (m + 2 ^ Q)) ^ 220)

private def preview (x : (X₀).obj) := Neighborhood.mask h (fun i => (x i).1)
private def rebank (x : (X₀).obj) : (Bank).obj := fun i => (hosts x i, (x i).2)

private theorem prepare (hh : 0 < h) :
    (Mask).width ≤ Overhead ∧ Circuit F X₀ (.pair Mask Bank)
      (fun x => (preview x, rebank x)) (40 * ((X₀).width + Overhead)) := by
  let U := Neighborhood.Rows m d
  let V := Neighborhood.Rows m Q
  let L := Format.vec m P₀
  have l : Circuit F X₀ U (fun x i => (x i).1) ((X₀).width + 2 * U.width) :=
    Circuit.project (fun z => (z.1, .inl z.2)) (fun _ _ => rfl)
  have r : Circuit F X₀ L (fun x i => (x i).2) ((X₀).width + 2 * L.width) :=
    Circuit.project (fun z => (z.1, .inr z.2)) (fun _ _ => rfl)
  have zip : Circuit F (.pair V L) Bank (fun x i => (x.1 i, x.2 i))
      ((V.pair L).width + 2 * (Bank).width) :=
    Circuit.project (Equiv.prodSumDistrib _ _ _) (by rintro x ⟨i, j|j⟩ <;> rfl)
  obtain ⟨s, hs, h₁⟩ := (Neighborhood.cheap F m d h hh).mono (d := 220) (by decide)
  obtain ⟨t, ht, h₂⟩ := Neighborhood.cheap_mask F m d h hh
  change U.width + V.width + s ≤ Overhead at h₁
  change U.width + (Mask).width + t ≤ Overhead at h₂
  have hX : (X₀).width = U.width + L.width := by
    simp only [Input, Fmt.bank, U, L, Neighborhood.Rows, Format.width_vec, Format.width_pair, mul_add]
  have hB : (Bank).width = V.width + L.width := by
    simp only [Fmt.bank, V, L, Neighborhood.Rows, Format.width_vec, Format.width_pair, mul_add]
  refine ⟨by omega, ((l.comp ht).pair (((l.comp hs).pair r).comp zip)).mono ?_⟩
  rw [Format.width_pair]
  omega

private abbrev Source (m d a h b : ℕ) :=
  Format.pair (Neighborhood.Mask m ((d + 1) * h) d) (.vec m (.vec ((d + 1) * h) (Parcel d a h b)))

local notation "Z₀" => Source m d a h b

private def inspect (x : (Z₀).obj) (i : B m) : (Checks Q d).obj :=
  (x.1 i, fun j => (x.2 i j).2.1)

private def arrange (x : (Format.pair (.vec m (Adjacency Q)) Views).obj) : (Y₀).obj := fun t =>
  let i := Match.rowIndex m a t
  ((x.2 i.1 0).1, x.1 i.1, fun j => (x.2 i.1 j).2.2 i.2)

private def finish (x : (Z₀).obj) : (Y₀).obj := arrange (fun i => adjacency (inspect x i), x.2)

private theorem finish_eq (x : (X₀).obj) :
    finish (preview x, Fmt.gather P₀ (rebank x)) = patches x := by
  funext t
  apply Prod.ext
  · change (x (hosts x (Match.rowIndex m a t).1 0)).2.1 = _
    rw [hosts, Neighborhood.origin]
    rfl
  apply Prod.ext
  · funext i k
    apply Prod.ext <;> apply Bool.eq_iff_iff.mpr <;>
      simp only [finish, arrange, inspect, adjacency, preview, Neighborhood.mask, Neighborhood.maskRows,
        Fmt.gather, rebank, patches, hosts, links, decide_eq_true_eq] <;>
      exact ⟨decide_eq_true, of_decide_eq_true⟩
  · rfl

private theorem post (hh : 0 < h) (hm : (Mask).width ≤ Overhead) :
    Circuit F Z₀ Y₀ finish (40 * ((Views).width + (Y₀).width + Overhead)) := by
  let C := Format.vec m (Checks Q d)
  let D := Format.vec m (Adjacency Q)
  have first : Circuit F Z₀ C inspect ((Z₀).width + 2 * C.width) :=
    Circuit.project (fun z => z.2.elim (fun p => .inl (z.1, p))
      (fun p => .inr (z.1, p.1, .inr (.inl p.2)))) (by rintro x ⟨i, j|j⟩ <;> rfl)
  have b' : Circuit F Z₀ Views Prod.snd ((Z₀).width + 2 * (Views).width) :=
    Circuit.project Sum.inr fun _ _ => rfl
  have c : Circuit F (.pair D Views) Y₀ arrange ((D.pair Views).width + 2 * (Y₀).width) := by
    let pin (p : (Y₀).pins) : (D.pair Views).pins :=
      let i := Match.rowIndex m a p.1
      p.2.elim (fun z => .inr (i.1, 0, .inl z))
        (Sum.elim (fun z => .inl (i.1, z))
          (fun z => .inr (i.1, z.1, .inr (.inr (i.2, z.2)))))
    exact Circuit.project pin (by rintro x ⟨i, j|(j|j)⟩ <;> rfl)
  have hq : 2 ^ Q ≤ m + 2 ^ Q := Nat.le_add_left _ _
  have hd : 2 ^ d ≤ m + 2 ^ Q := (Nat.pow_le_pow_right (by decide)
    ((Nat.le_succ d).trans (Nat.le_mul_of_pos_right _ hh))).trans hq
  obtain ⟨t, ht, he⟩ := (Cheap.map _ (fun _ : B m => cheap_adjacency F hq hd)).mono
    (d := 220) (by decide)
  change C.width + D.width + t ≤ Overhead at he
  refine (((first.comp ht).pair b').comp c).mono ?_
  rw [Format.width_pair D Views, show (Z₀).width = (Mask).width + (Views).width from Format.width_pair _ _]
  omega

def patchCost (m d a h b v n : ℕ) :=
  1000 * ((Input m d a h b).width + (Patches m d a h b).width +
    (Format.vec m (.vec ((d + 1) * h) (Parcel d a h b))).width + 2 ^ m * (100 + (m + 2 ^ ((d + 1) * h))) ^ 220) +
      gatherCost m ((d + 1) * h) v n

theorem compute_patches {u v n : ℕ} {L : Set (Table F)} {I : Type*} (hu : 3 ≤ u)
    (hh : 0 < h) (ht : Access F u L (m + Q) v n) (hv : (P₀).width ≤ v)
    (X : I → (X₀).obj) (hx : ∀ i, Fmt.Reciprocal P₀ (X i)) :
    Computes F u L X₀ Y₀ X (fun i => patches (X i)) (fun _ => 1) (patchCost m d a h b v n) := by
  obtain ⟨hm, hp⟩ := prepare (F := F) (m := m) (d := d) (a := a) (b := b) hh
  have h₁ := Computes.of_map (L := L) (x := X) (Map.circuit hu hp) (fun _ => rfl)
  have hg := gather_neighbors (L := L) P₀ hu ht hv (fun i => rebank (X i))
    (fun i => Neighborhood.reciprocal (hx i) h (fun j => (X i j).2))
  have hi := Computes.of_map (L := L) (x := fun i => preview (X i))
    (Map.circuit hu (Circuit.id F Mask)) (fun _ => rfl)
  have h₂ := h₁.comp (hi.par hg)
  have k := h₂.comp (Computes.of_map (Map.circuit hu (post hh hm)) (fun i => finish_eq (X i)))
  simp only [one_mul] at k
  refine k.mono ?_
  unfold patchCost
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Group
end

/-! # Grouping from the shared contact array and short loads -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Group

open Coloring Packing
variable {m d a h b : ℕ}

def labels (Δ D : ℕ) (f : B b → ℝ) (x : (Input m d a h b).obj) :=
  decideAll Δ D f (patches x)

theorem labels_net {F : Type} [Field F] {I : Type*} {Δ D v n u : ℕ}
    {L : Set (Table F)} {f : B b → ℝ} (hu : 3 ≤ u) (hh : 0 < h)
    (ht : Access F u L (m + (d + 1) * h) v n) (hv : (Parcel d a h b).width ≤ v)
    (X : I → (Input m d a h b).obj) (hx : ∀ i, Fmt.Reciprocal (Parcel d a h b) (X i))
    (hb : arity ((d + 1) * h) h b ≤ u) (hL : (keys F ((d + 1) * h) h b Δ D f : Set _) ⊆ L) :
    Computes F u L (Input m d a h b) (.vec (m + a) (Labels h)) X
      (fun i => labels Δ D f (X i)) (fun _ => 1)
      (patchCost m d a h b v n + cost (m + a) ((d + 1) * h) h b) := by
  have H := (compute_patches (L := L) hu hh ht hv X hx).comp
    (Computes.of_map (compute F (m + a) hu hb hL) (fun _ => rfl))
  simpa only [one_mul, labels] using H

theorem Presents.grouping {V : Type} [Fintype V] {E C : V → Finset V} {Δ D k : ℕ}
    {x : (Input m d a h b).obj} {host : V ↪ B m}
    {l : V × Cell a → Cell h → ℝ} {B' : ℝ} {f : B b → ℝ}
    (H : Presents x host E C (relative k B' l) f)
    (hΔ : 0 < Δ) (hD : 0 < D) (hk : 1 ≤ k) (hkh : k ≤ h) (hB : 0 < B')
    (eSym : ∀ v u, u ∈ E v → v ∈ E u) (cSym : ∀ v u, u ∈ C v → v ∈ C u)
    (sub : ∀ v, C v ⊆ E v) (eDeg : ∀ v, (E v).card ≤ D) (cDeg : ∀ v, (C v).card ≤ Δ)
    (hl : ∀ v i, 0 ≤ l v i ∧ l v i ≤ B') :
    ∃ g : Grouping (inGroup a E) (inGroup a C) Δ D k B' l, ∀ v i,
      labels Δ D f x (embed host a v) (cellIndex h i) = intervalCode h (g.here v i).2 := by
  have sym (N : V → Finset V) (hs : ∀ v u, u ∈ N v → v ∈ N u)
      (v u : V × Cell a) (hu : u ∈ inGroup a N v) : v ∈ inGroup a N u := by
    simp only [mem_inGroup] at hu ⊢
    exact ⟨hs _ _ hu.1, hu.2.symm⟩
  apply (H.represents hΔ hD).grouping hΔ hD hk hkh hB (sym E eSym) (sym C cSym) _ _ _ hl
  · intro v u hu
    simp only [mem_inGroup] at hu ⊢
    exact ⟨sub _ hu.1, hu.2⟩
  · intro v
    simpa [inGroup] using eDeg v.1
  · intro v
    simpa [inGroup] using cDeg v.1

end OAI.LinearAlgebra.MatrixExponent.Assembly.Group
end
