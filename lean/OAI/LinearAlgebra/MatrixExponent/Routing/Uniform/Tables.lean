import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Inverse
import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Colours
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Matching
import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Recipe

section
/-! # Constructing inverse and pairing programs at arbitrary height -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring Algorithm
open private inverse_sorted from OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Inverse

def invTable {h : ℕ} : Endo h := fun g => ⇑(Coloring.permutation g (fun _ => true))

theorem invTable_eq {h : ℕ} (g : Equiv.Perm (B h)) : invTable g = ⇑g.symm := by
  unfold invTable
  rw [inverse_sorted]

namespace Builder

def inverse {w h : ℕ} (hh : h ≤ w) : Builder w (invTable (h := h)) (2 ^ h * (100 + w) ^ 25) := by
  have on : Builder w (fun (_ : B h → B h) (_ : B h) => true) (2 ^ h * 2) :=
    .tab hh _ (fun _ => .bit true)
  refine (on.keep.comp (Builder.permutation hh hh)).mono ?_
  have := Nat.two_pow_pos h
  have := budget_base h w 20
  have := (budget_step h w 20).trans (budget_mono h w (by decide : 21 ≤ 25))
  omega

def partner {w h k : ℕ} (hh : h ≤ w) (hk : k ≤ w) :
    Builder w (fun x : (B h → B k) × (B h → Bool) => Coloring.partner x.1 x.2)
      (2 ^ h * (100 + w) ^ 30) := by
  have flip : Builder w (fun p : B h → B h => p ∘ Coloring.toggle h) (2 ^ h * 2) :=
    .tab hh _ (fun i => .at hh (Coloring.toggle h i))
  have nbr := (Builder.permutation hh hk).comp ((flip.pair (inverse hh)).comp (gather hh hh))
  have mask : Builder w (fun (x : (B h → Bool) × (B h → B h)) i =>
      if x.1 i then x.2 i else i) (2 ^ h * 9) :=
    .tab hh _ (fun i => ((Builder.fst.comp (.at hh i)).pair
      ((Builder.snd.comp (.at hh i)).pair (.lit hh i))).comp .select)
  have H := (Builder.snd.pair nbr).comp mask
  convert H.mono (n := 2 ^ h * (100 + w) ^ 30) ?_ using 1
  · funext x i
    simp only [Function.comp_apply, Coloring.partner, invTable_eq]
  · have := Nat.two_pow_pos h
    have := budget_base h w 25
    have := budget_mono h w (by decide : 20 ≤ 25)
    have := (budget_step h w 25).trans (budget_mono h w (by decide : 26 ≤ 30))
    omega

end Builder
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-!
# Alternating colours by pointer doubling

At round t the two arrays store a jump of length 2^t and the minimum
along that many consecutive edges. Each round costs linearly many loads
and comparisons. The arrays from the previous round are shared.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Builder
open Coloring Algorithm

private abbrev Table (h : ℕ) := B h → B h

variable {w h k : ℕ}

private def minimum (hh : h ≤ w) :
    Builder w (fun x : B h × B h => min x.1 x.2) 4 := by
  have H := ((Builder.lt hh).pair Builder.id).comp (Builder.select (A := B h))
  convert H using 1
  funext x
  simp only [Function.comp_apply, id_eq, decide_eq_true_eq]
  by_cases hs : x.1 < x.2
  · rw [ite_eq_left hs, min_eq_left hs.le]
  · rw [ite_eq_right hs, min_eq_right (le_of_not_gt hs)]

/-- Read a value at i and at the successor indexed by the first array. -/
private def two_values (hh : h ≤ w) (i : B h) :
    Builder w (fun x : Table h × Table h => (x.2 i, x.2 (x.1 i))) 8 :=
  (Builder.snd.comp (.at hh i)).pair ((Builder.snd.pair (Builder.fst.comp (.at hh i))).comp (.read hh))

private def double_step (hh : h ≤ w) :
    Builder w (fun x : Table h × Table h => (x.1 ∘ x.1, fun i => min (x.2 i) (x.2 (x.1 i))))
      (2 ^ h * 23) := by
  have J : Builder w (fun x : Table h × Table h => x.1 ∘ x.1) (3 + 2 ^ h * 6) :=
    (Builder.fst.pair Builder.fst).comp (gather hh hh)
  have M : Builder w (fun x : Table h × Table h => fun i => min (x.2 i) (x.2 (x.1 i)))
      (2 ^ h * 13) := .tab hh _ (fun i => (two_values hh i).comp (minimum hh))
  exact (J.pair M).mono (by have := Nat.two_pow_pos h; omega)

private def doubling (hh : h ≤ w) (t : ℕ) :
    Builder w (fun P : Table h => (jump P t, low P t)) (2 ^ h * (4 + 23 * t)) := by
  induction t with
  | zero =>
    have M : Builder w (fun _ : Table h => (_root_.id : Table h)) (2 ^ h * 2) :=
      .tab hh _ (fun i => .lit hh i)
    exact (Builder.id.pair M).mono (by have := Nat.two_pow_pos h; omega)
  | succ t ih =>
    exact (ih.comp (double_step hh)).mono (by ring_nf; rfl)

def colour (hh : h ≤ w) :
    Builder w (fun x : (B h → B h) × (B h → B h) => Coloring.colour h x.1 x.2) (2 ^ h * (100 + w) ^ 2) := by
  have J : Builder w (fun x : Table h × Table h => x.2 ∘ x.1) (3 + 2 ^ h * 6) :=
    (Builder.snd.pair Builder.fst).comp (gather hh hh)
  have M := (J.comp (doubling hh h)).comp Builder.snd
  have H : Builder w (fun x : Table h × Table h => fun i => decide (x.2 i < x.2 (x.1 i)))
      (2 ^ h * 10) := .tab hh _ (fun i => (two_values hh i).comp (.lt hh))
  apply ((Builder.fst.pair M).comp H).mono
  calc
    _ ≤ 2 ^ h * (26 + 23 * h) := by have := Nat.two_pow_pos h; ring_nf; omega
    _ ≤ _ := Nat.mul_le_mul_left _ (by nlinarith)

def split (hh : h ≤ w) (hk : k ≤ w) :
    Builder w (fun x : (B h → B k) × (B h → B k) × (B h → Bool) =>
      Coloring.split x.1 x.2.1 x.2.2) (2 ^ h * (100 + w) ^ 40) := by
  have part := Builder.partner hh hk
  let A := (B h → B k) × (B h → B k) × (B h → Bool)
  have L : Builder w (fun x : A => (x.1, x.2.2)) 4 := Builder.fst.pair (Builder.snd.comp Builder.snd)
  have R : Builder w (fun x : A => x.2) 1 := Builder.snd
  apply (((L.comp part).pair (R.comp part)).comp (colour hh)).mono
  have := Nat.two_pow_pos h
  have := budget_base h w 30
  have := budget_mono h w (by decide : 2 ≤ 30)
  have := (budget_step h w 30).trans (budget_mono h w (by decide : 31 ≤ 40))
  omega

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Builder
end

section
/-!
# Compiling the matching routine

The dummy labels and the initial multiplicities are input-independent.
The current counter at each edge fits in the same word throughout.
Materializing the chosen side and the cycle colors before updating the
counters avoids recomputing a global quantity for each edge.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring (B join dummy halves)
open Algorithm (Graph budget_mono budget_base budget_step)
open private State View odds update step steps out from OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Matching

namespace Reservation
variable {k t w : ℕ}

/-- A lookup that carries the number of setup steps used along the chain
of enlarged reservations. -/
structure Fetch (S : Reservation k) (t : ℕ) where
  get : ℕ → Work (B k)
  eq : ∀ i, (get i).value = S.assign i
  fee : ∀ i, (get i).steps ≤ 64 * (1 + t)

/-- The initial reservation must provide bounded-cost indexed access.
Construction of this initial table is charged by the caller. -/
def fetch (S : Reservation k) : S.Fetch 0 where
  get i := ⟨S.assign i, 64⟩
  eq _ := rfl
  fee _ := le_rfl

/-- Charge each enlarged lookup for its recursive call and a block
for the index shift, parity, doubling, and return. -/
def Fetch.enlarge {S : Reservation k} (F : S.Fetch t) : S.enlarge.Fetch (t + 1) where
  get i :=
    let prev := F.get (i / 2)
    ⟨Coloring.double prev.value (decide (i % 2 = 1)), prev.steps + 64⟩
  eq i := congrArg (fun v => Coloring.double v (decide (i % 2 = 1))) (F.eq (i / 2))
  fee i := by
    change (F.get (i / 2)).steps + 64 ≤ _
    have := F.fee (i / 2)
    omega

theorem Fetch.allowed {S : Reservation k} (F : S.Fetch t) (ht : t ≤ w) (i : ℕ) :
    (F.get i).steps ≤ allowance w := by
  calc
    _ ≤ 64 * (1 + t) := F.fee i
    _ ≤ (100 + w) ^ 2 := by nlinarith
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

end Reservation

namespace Builder
variable {w h k r m : ℕ}

def iterate {A : Type} {f : A → A} (hf : Builder w f m) (t : ℕ) :
    Builder w (f^[t]) (1 + t * m) := by
  induction t with
  | zero => simpa using (Builder.id : Builder w (_root_.id : A → A) 1)
  | succ t ih =>
    rw [Function.iterate_succ', Nat.succ_mul, ← Nat.add_assoc]
    exact ih.comp hf

private def update_code (hh : h ≤ w) (hr : r ≤ w) (i : B h) :
    Builder w (fun x : View h k r => update x i) 50 := by
  have v : Builder w (fun x : View h k r => x.1.2.2 i) 4 :=
    ((Builder.fst.comp .snd).comp .snd).comp (.at hh i)
  have col : Builder w (fun x : View h k r => x.2.1 i) 3 := (Builder.snd.comp .fst).comp (.at hh i)
  have pick := (col.pair (Builder.snd.comp Builder.snd)).comp (.gate (fun x => x.1 == x.2))
  have tag := ((v.comp (.odd hr)).pair pick).comp (.gate (fun x => x.1 && x.2))
  have down := v.comp (.halve hr)
  have plus := (down.pair (.lit hr 1)).comp (.add hr)
  exact ((tag.pair (plus.pair down)).comp .select).mono (by decide)

private def step_code (hh : h + 1 ≤ w) (hk : k ≤ w) (hr : r ≤ w) (δ : B h → Bool) :
    Builder w (step (k := k) (r := r) δ) (2 ^ h * (100 + w) ^ 42) := by
  have hv : h ≤ w := by omega
  have mask : Builder w (odds (h := h) (k := k) (r := r)) (2 ^ h * 5) :=
    .tab hv _ (fun i => ((Builder.snd.comp .snd).comp (.at hv i)).comp (.odd hr))
  have row := (Builder.fst.pair ((Builder.snd.comp Builder.fst).pair mask)).comp (Builder.split hv hk)
  have flags := (mask.pair row).comp (Builder.snd.pair (Builder.minority hh δ))
  have upd := flags.keep.comp (Builder.tab hv _ (update_code (k := k) hv hr))
  refine (Builder.fst.pair ((Builder.snd.comp Builder.fst).pair upd)).mono ?_
  have := budget_mono h w (by decide : 10 ≤ 40)
  have := budget_base h w 40
  have := Nat.two_pow_pos h
  have h₁ := budget_step h w 40
  have h₂ := budget_step h w 41
  simp only [Nat.reduceAdd] at h₁ h₂
  omega

private def init (S : Reservation k) (d : ℕ) (x : Graph h k) : State (h + 1) k (h + 2) :=
  (join x.1 (dummyLabel S), join x.2.1 (dummyLabel S),
    fun i => Fin.ofNat (2 ^ (h + 2)) (weights S d x.2.2 i))

private theorem init_eq (S : Reservation k) (d : ℕ) (x : Graph h k) :
    Fin.val ∘ (init S d x).2.2 = weights S d x.2.2 := by
  funext t
  apply Nat.mod_eq_of_lt
  have hp : 2 ^ (h + 1) < 2 ^ (h + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
  obtain ⟨i|i, rfl⟩ := (halves h).surjective t
  · simp only [weights, join, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
    split <;> first | exact (Nat.div_le_self ..).trans_lt hp | positivity
  · simp only [weights, join, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    split <;> first | exact (Nat.mod_le ..).trans_lt hp | positivity

private def init_code (hh : h + 2 ≤ w) (hk : k ≤ w) (S : Reservation k) (d : ℕ)
    {t : ℕ} (F : S.Fetch t) (bound : t ≤ w) :
    Builder w (init (h := h) S d) (2 ^ h * 100) := by
  have hv : h + 1 ≤ w := by omega
  have ht : h ≤ w := by omega
  have ext : Builder w (fun p : B h → B k => join p (dummyLabel S)) (2 ^ (h + 1) * 2) := by
    apply Builder.tab (m := 1) hv
    intro t
    obtain ⟨i|i, rfl⟩ : {i // halves h i = t} := ⟨(halves h).symm t, (halves h).apply_symm_apply t⟩
    · simpa [join] using (Builder.at (A := B k) ht i)
    · simpa only [join, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, dummyLabel, F.eq]
        using (Builder.litCost (A := B h → B k) hk (F.get i.val) (F.allowed bound i.val))
  have cnt : Builder w (fun x : B h → Bool => fun t => Fin.ofNat (2 ^ (h + 2)) (weights S d x t))
      (2 ^ (h + 1) * 7) := by
    apply Builder.tab (m := 6) hv
    intro t
    obtain ⟨i|i, rfl⟩ : {i // halves h i = t} := ⟨(halves h).symm t, (halves h).apply_symm_apply t⟩
    · have he := ((Builder.at (A := Bool) ht i).pair
        ((Builder.lit hh (Fin.ofNat (2 ^ (h + 2)) (2 ^ (h + 1) / d))).pair (Builder.lit hh 0))).comp .select
      simp only [weights, join, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
      convert he using 1
      funext x
      by_cases h : x i = true <;> simp [h]
    · simp only [weights, join, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
      exact (Builder.lit hh _).mono (by decide)
  refine ((Builder.fst.comp ext).pair (((Builder.snd.comp Builder.fst).comp ext).pair
    ((Builder.snd.comp Builder.snd).comp cnt))).mono ?_
  rw [pow_succ]
  have := Nat.two_pow_pos h
  omega

private def out_code (hh : h + 2 ≤ w) :
    Builder w (out (h := h) (k := k)) (2 ^ h * 7) := by
  apply Builder.tab (m := 6) (by omega)
  intro i
  exact ((((Builder.snd.comp .snd).comp (Builder.at (by omega) (halves h (.inl i)))).pair (.lit hh 1)).comp (.eq hh))

private theorem out_eq (S : Reservation k) (d : ℕ) (x : Graph h k) :
    out ((step (dummy h))^[h + 1] (init S d x)) = matching S d x.1 x.2.1 x.2.2 := by
  have he := (steps (dummy h) (init S d x) (h + 1)).2.2
  rw [init_eq] at he
  funext i
  have hv := congrFun he (halves h (.inl i))
  have hs : (1 : B (h + 2)).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_pow (by omega) (by decide))
  simp only [out, Fin.ext_iff, hs, Uniform.matching]
  exact congrArg (fun n => decide (n = 1)) hv

def matchingAt (hh : h + 2 ≤ w) (hk : k ≤ w) (S : Reservation k) (d : ℕ)
    {t : ℕ} (F : S.Fetch t) (bound : t ≤ w) :
    Builder w (fun x : Graph h k => Uniform.matching S d x.1 x.2.1 x.2.2) (2 ^ h * (100 + w) ^ 46) := by
  have run := ((init_code hh hk S d F bound).comp ((step_code (h := h + 1) hh hk hh (dummy h)).iterate (h + 1))).comp (out_code hh)
  have val : out ∘ (step (dummy h))^[h + 1] ∘ init S d =
      (fun x : Graph h k => Uniform.matching S d x.1 x.2.1 x.2.2) := funext (out_eq S d)
  rw [val] at run
  refine run.mono ?_
  have hi : (h + 1) * (2 ^ (h + 1) * (100 + w) ^ 42) ≤ 2 * (2 ^ h * (100 + w) ^ 43) := by
    calc
      _ ≤ (100 + w) * (2 ^ (h + 1) * (100 + w) ^ 42) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by
        have eqn (a b c : ℕ) : c * (a * 2 * b) = 2 * (a * (b * c)) := by ring
        rw [pow_succ 2 h, pow_succ (100 + w) 42]
        exact eqn ..
  have := Nat.two_pow_pos h
  have := budget_base h w 43
  have ha := budget_step h w 43
  have hb := budget_step h w 44
  have hc := budget_step h w 45
  simp only [Nat.reduceAdd] at ha hb hc
  omega

def matching (hh : h + 2 ≤ w) (hk : k ≤ w) (S : Reservation k) (d : ℕ) :
    Builder w (fun x : Graph h k => Uniform.matching S d x.1 x.2.1 x.2.2) (2 ^ h * (100 + w) ^ 46) :=
  matchingAt hh hk S d S.fetch (Nat.zero_le w)

end Builder
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-!
# Word programs for recursive edge colouring

At each level the two subgraphs share one array. The program stores
the retirement and split flags and invokes the next level once.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring (B nextEnd rest combine)
open Algorithm (Graph budget_mono budget_base budget_step)

namespace Builder
variable {w h k : ℕ}

private def double_code (hk : k + 1 ≤ w) :
    Builder w (fun x : B k × Bool => Coloring.double x.1 x.2) 14 := by
  have v : Builder w (fun x : B k × Bool => Fin.ofNat (2 ^ (k + 1)) x.1.val) 2 :=
    fst.comp (resize (by omega) hk)
  have b : Builder w (fun x : B k × Bool => if x.2 then (1 : B (k + 1)) else 0) 6 :=
    (snd.pair ((lit hk 1).pair (lit hk 0))).comp select
  have H := (((v.pair v).comp (add hk)).pair b).comp (add hk)
  convert H using 1
  funext ⟨x, b⟩
  apply Fin.ext
  have lt := (Coloring.double x b).isLt
  cases b <;> simp [Coloring.double, Fin.add_def, Fin.ofNat, two_mul] at lt ⊢ <;>
    rw [Nat.mod_eq_of_lt lt]

private def combine_code (hh : h + 1 ≤ w) (d : ℕ) :
    Builder w (fun x : Bool × B h × Bool => Coloring.combine d x.1 x.2.2 x.2.1) 21 := by
  have hp : h ≤ w := by omega
  have dc := (double_code hh).comp (resize hh hp)
  let z := Fin.ofNat (2 ^ h) (d - 1)
  have H := (fst.pair ((lit hp z).pair (snd.comp dc))).comp (select (A := B h))
  convert H.mono (n := 21) (by decide) using 1
  funext ⟨p, j, b⟩
  cases p <;> rfl

private abbrev Flags (h : ℕ) := (B h → Bool) × (B h → Bool)

private def collect (hh : h + 1 ≤ w) (d : ℕ) :
    Builder w (fun (x : Flags h × (B h → B h)) i =>
      combine d (x.1.1 i) (x.1.2 i) (x.2 i)) (2 ^ h * 32) := by
  have hp : h ≤ w := by omega
  refine .tab hp _ (fun i => ?_)
  have y : Builder w (fun x : Flags h × (B h → B h) => x.1.1 i) 3 :=
    (fst.comp fst).comp (.at hp i)
  have b : Builder w (fun x : Flags h × (B h → B h) => x.1.2 i) 3 :=
    (fst.comp snd).comp (.at hp i)
  exact (y.pair ((snd.comp (.at hp i)).pair b)).comp (combine_code hh d)

private def extendEnds (hh : h ≤ w) (hk : k + 1 ≤ w) :
    Builder w (fun x : (B h → B k) × (B h → Bool) => nextEnd x.1 x.2) (2 ^ h * 20) :=
  .tab hh _ (fun i => ((fst.comp (.at hh i)).pair (snd.comp (.at hh i))).comp (double_code hk))

private def prepare (S : Reservation k) (d : ℕ) (x : Graph h k) : Flags h × Graph h (k + 1) :=
  let y := retired S d x.1 x.2.1 x.2.2
  let a := rest x.2.2 y
  let b := Coloring.split x.1 x.2.1 a
  ((y, b), nextEnd x.1 b, nextEnd x.2.1 b, a)

private def prepare_code (hh : h + 2 ≤ w) (hk : k + 1 ≤ w)
    (S : Reservation k) (d : ℕ) {t : ℕ} (F : S.Fetch t) (ht : t ≤ k) :
    Builder w (prepare (h := h) S d) (2 ^ h * (100 + w) ^ 48) := by
  have hp : h ≤ w := by omega
  have kp : k ≤ w := by omega
  let G := Graph h k
  let M := B h → Bool
  have y : Builder w (fun x : G => retired S d x.1 x.2.1 x.2.2) (2 ^ h * (100 + w) ^ 46) := by
    by_cases he : d % 2 = 0
    · simp only [retired, he, ite_true]
      exact (tab hp _ (fun _ => bit false)).mono (by
        have := budget_base h w 45
        have := budget_step h w 45
        simp only [Nat.reduceAdd] at *
        omega)
    · simp only [retired, he, ite_false]
      exact matchingAt hh kp S d F (ht.trans kp)
  have a : Builder w (fun x : G × M => rest x.1.2.2 x.2) (2 ^ h * 9) :=
    .tab hp _ (fun i => ((((fst.comp snd).comp snd).comp (.at hp i)).pair
      (snd.comp (.at hp i))).comp (gate (fun p => p.1 && !p.2)))
  have live := snd.pair ((fst.comp fst).pair (((fst.comp snd).comp fst).pair a))
  have b : Builder w (fun x : M × G => Coloring.split x.2.1 x.2.2.1 x.2.2.2)
      (1 + 2 ^ h * (100 + w) ^ 40) := snd.comp (Builder.split hp kp)
  have ends : Builder w (fun x : (M × G) × M => x.1.2) 2 := fst.comp snd
  have left := ((ends.comp fst).pair snd).comp (extendEnds hp hk)
  have right := (((ends.comp snd).comp fst).pair snd).comp (extendEnds hp hk)
  have newGraph := left.pair (right.pair ((ends.comp snd).comp snd))
  have resume := ((fst.comp fst).pair snd).pair newGraph
  refine (((y.keep.comp live).comp b.keep).comp resume).mono ?_
  have := Nat.two_pow_pos h
  have := budget_base h w 46
  have := budget_mono h w (by decide : 40 ≤ 46)
  have := (budget_step h w 46).trans (budget_mono h w (by decide : 47 ≤ 48))
  omega

private def recurse_code (hh : h + 2 ≤ w) (n : ℕ) (hk : k + n ≤ w)
    (S : Reservation k) (d : ℕ) {t : ℕ} (F : S.Fetch t) (ht : t ≤ k) :
    Builder w (fun x : Graph h k => recurse n S d x.1 x.2.1 x.2.2)
      ((n + 1) * (2 ^ h * (100 + w) ^ 49)) := by
  induction n generalizing k d t with
  | zero =>
    have hp : h ≤ w := by omega
    exact (tab hp _ (fun _ => lit hp 0)).mono (by
      have := budget_base h w 48
      have := budget_step h w 48
      simp only [Nat.reduceAdd, one_mul] at *
      omega)
  | succ n ih =>
    have a := prepare_code hh (by omega : k + 1 ≤ w) S d F ht
    have b := ih (k := k + 1) (by omega) S.enlarge (d / 2) F.enlarge (by omega)
    have c := collect (by omega : h + 1 ≤ w) d
    refine ((a.comp (fst.pair (snd.comp b))).comp c).mono ?_
    have := Nat.two_pow_pos h
    have := budget_base h w 48
    have := budget_step h w 48
    rw [Nat.succ_mul (n + 1)]
    simp only [Nat.reduceAdd] at *
    omega

def colours (hh : h + 3 ≤ w) (hk : k + h + 1 ≤ w) (S : Reservation k) (d : ℕ) :
    Builder w (fun x : Graph h k => Uniform.colours S d x.1 x.2.1 x.2.2)
      (2 ^ h * (100 + w) ^ 100) := by
  refine (recurse_code (w := w) (h := h) (k := k) (by omega) (h + 1) (by omega) S d S.fetch (Nat.zero_le k)).mono ?_
  calc
    _ ≤ (100 + w) * (2 ^ h * (100 + w) ^ 49) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ h * (100 + w) ^ 50 := by rw [pow_succ' (100 + w) 49, mul_left_comm]
    _ ≤ _ := budget_mono h w (by decide)

end Builder
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-!
# Word programs for the three permutation factors

Each route uses a vector sum, an indexed read from the location table,
and a mask. The charge includes constructing every fixed table.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring Algorithm

namespace Builder
variable {w h : ℕ}

def tableLits {A : Type} (hh : h ≤ w) (a : B h → B h) :
    Builder w (fun _ : A => a) (2 ^ h * 2) :=
  .tab hh _ (fun i => .lit hh (a i))

def mask_table (hh : h ≤ w) (m : B h → Bool) :
    Builder w (fun (x : B h → B h) i => if m i then x i else i) (2 ^ h * 7) :=
  .tab hh _ (fun i => ((Builder.bit (m i)).pair ((Builder.at hh i).pair (.lit hh i))).comp .select)

private def chart_route (hh : h ≤ w) (p : Uniform.Chart h) :
    Builder w (fun x : (B h → B h) × (B h → B h) => p.route x.1 x.2) (2 ^ h * 23) := by
  have addrs : Builder w (fun (x : (B h → B h) × (B h → B h)) i => x.1 i + x.2 i)
      (2 ^ h * 7) := .tab hh _ (fun i => ((Builder.fst.comp (.at hh i)).pair
        (Builder.snd.comp (.at hh i))).comp (.add hh))
  have get := ((tableLits hh p.location).pair addrs).comp (gather hh hh)
  exact (get.comp (mask_table hh p.mask)).mono (by have := Nat.two_pow_pos h; omega)

def chart_run (hw : 3 * h + 10 ≤ w) (p : Uniform.Chart h) :
    Builder w (p.run invert) (2 ^ h * (100 + w) ^ 110) := by
  have hh : h ≤ w := by omega
  have hi : Builder w (invert (h := h)) (2 ^ h * (100 + w) ^ 25) := inverse hh
  have hl := Builder.colours (show h + 3 ≤ w by omega) (show h + h + 1 ≤ w by omega) p.support p.degree
  have mask : Builder w (fun _ : B h → B h => p.mask) (2 ^ h * 2) :=
    .tab hh _ (fun i => .bit (p.mask i))
  have a := tableLits (A := B h → B h) hh p.base
  have y : Builder w (_root_.id : Endo h) 1 := .id
  have b := (a.pair y).comp (gather hh hh)
  have label := (a.pair (b.pair mask)).comp hl
  have L := (a.pair label).comp (chart_route hh p)
  have R := (b.pair label).comp (chart_route hh p)
  have u := (y.pair (R.comp hi)).comp (gather hh hh)
  have v := (R.pair (L.comp hi)).comp (gather hh hh)
  refine (u.pair (v.pair L)).mono ?_
  have h₁ := budget_base h w 100
  have h₂ := budget_mono h w (show 25 ≤ 100 by decide)
  have h₃ := budget_step h w 100
  have h₄ := (budget_step h w 101).trans (budget_mono h w (show 102 ≤ 110 by decide))
  simp only [Nat.reduceAdd] at h₃ h₄
  have := Nat.two_pow_pos h
  omega

end Builder
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-! # A linear word-width bound for every arithmetic subexpression -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
variable {M : ℕ}

def Register.width : Register → ℕ
  | .lit n => n + 1
  | _ => 1

def Arith.width : Arith M → ℕ
  | .power q => q + 1
  | .table (n := n) _ => M + n + 1
  | _ => 1

private theorem grow {s t : ℕ} (h : s ≤ t) : 2 ^ s ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) h

theorem power_lt (q h j : ℕ) (hj : j ≤ h + 2) : q ^ j < 2 ^ ((q + 1) * (h + 3)) := calc
  _ ≤ (2 ^ q) ^ j := Nat.pow_le_pow_left Nat.lt_two_pow_self.le j
  _ ≤ (2 ^ q) ^ (h + 2) := Nat.pow_le_pow_right (Nat.two_pow_pos _) hj
  _ < _ := by rw [← pow_mul]; exact Nat.pow_lt_pow_right (by decide) (by nlinarith)

private theorem Arith.eval_lt (a : Arith M) (h x y s t : ℕ) (hx : x < 2 ^ s) (hy : y < 2 ^ t) :
    a.eval h x y < 2 ^ (s + t + a.width * (h + 3)) := by
  have hh : (x + 1) * (y + 1) ≤ 2 ^ (s + t) := by rw [pow_add]; exact Nat.mul_le_mul hx hy
  have hu : 2 ^ (s + t) ≤ 2 ^ (s + t + a.width * (h + 3)) := grow (by omega)
  have hv : 2 ^ (a.width * (h + 3)) ≤ 2 ^ (s + t + a.width * (h + 3)) := grow (by omega)
  have hw := Nat.lt_two_pow_self (n := h + 3)
  cases a with
  | power q => exact (power_lt q h _ (min_le_left ..)).trans_le hv
  | @table n data =>
    have hm : M < 2 ^ ((M + n + 1) * (h + 3)) := Nat.lt_two_pow_self.trans_le (grow (by nlinarith))
    refine lt_of_le_of_lt ?_ (hm.trans_le hv)
    simp only [eval]
    split
    · exact Nat.le_of_lt_succ (Fin.isLt _)
    · exact Nat.zero_le _
  | lt =>
    change (if x < y then 1 else 0) < _
    simp only [width, one_mul] at hv ⊢
    split <;> omega
  | add => exact lt_of_lt_of_le (by change x + y < _; nlinarith only [hh]) hu
  | mul => exact lt_of_lt_of_le (by change x * y < _; nlinarith only [hh]) hu
  | sub => exact (Nat.sub_le x y).trans_lt (hx.trans_le (grow (by omega)))
  | div => exact (Nat.div_le_self x y).trans_lt (hx.trans_le (grow (by omega)))
  | mod => exact (Nat.mod_le x y).trans_lt (hx.trans_le (grow (by omega)))

namespace Index

def width : Index M → ℕ
  | .arg r => r.width
  | .op f u v => u.width + v.width + f.width
  | .sum n u => n.width + u.width + 1

theorem width_pos (e : Index M) : 0 < e.width := by
  induction e with
  | arg r => cases r <;> simp [width, Register.width]
  | op f u v hu hv => simp only [width]; omega
  | sum n u hn hu => simp only [width]; omega

/-- The bound also applies to each intermediate partial sum. -/
private theorem sum_lt (h s n : ℕ) (hn : n ≤ h + 2) (f : ℕ → ℕ)
    (hf : ∀ i < n, f i < 2 ^ s) : (∑ i ∈ Finset.range n, f i) < 2 ^ (s + (h + 3)) := calc
  _ ≤ ∑ _i ∈ Finset.range n, 2 ^ s := Finset.sum_le_sum (fun i hi => (hf i (Finset.mem_range.mp hi)).le)
  _ = n * 2 ^ s := by simp
  _ < _ := by
    rw [pow_add, mul_comm n]
    exact Nat.mul_lt_mul_of_pos_left (lt_of_le_of_lt (by omega) Nat.lt_two_pow_self) (Nat.two_pow_pos _)

theorem eval_lt (e : Index M) (h b x i : ℕ) (hb : b ≤ h + 2) (hx : x < 2 ^ (h + 2)) (hi : i ≤ h + 2) :
    e.eval h b x i < 2 ^ (e.width * (h + 3)) := by
  have hw := Nat.lt_two_pow_self (n := h + 3)
  have hv : 2 ^ (h + 2) ≤ 2 ^ (h + 3) := grow (by omega)
  induction e generalizing i with
  | arg r =>
    cases r <;> simp only [eval, Register.eval, width, Register.width, one_mul] <;> try omega
    case lit n => exact Nat.lt_two_pow_self.trans_le (grow (by nlinarith))
  | op f u v hu hv =>
    change _ < 2 ^ ((u.width + v.width + f.width) * (h + 3))
    rw [add_mul, add_mul]
    exact f.eval_lt h _ _ _ _ (hu i hi) (hv i hi)
  | sum n u hn hu =>
    refine (sum_lt h (u.width * (h + 3)) _ (min_le_left ..) _ (fun j hj => hu j (by omega))).trans_le ?_
    exact grow (by simp only [width, add_mul, one_mul]; omega)

/-- Syntactic subexpressions, including the entire expression. -/
inductive Part (u : Index M) : Index M → Prop
  | self : Part u u
  | left {f x y} : Part u x → Part u (.op f x y)
  | right {f x y} : Part u y → Part u (.op f x y)
  | bound {x y} : Part u x → Part u (.sum x y)
  | body {x y} : Part u y → Part u (.sum x y)

theorem Part.width_le {e u : Index M} (hu : Part u e) : u.width ≤ e.width := by
  induction hu <;> first | exact le_rfl | simp only [width]; omega

theorem Part.eval_lt {e u : Index M} (hu : Part u e) (h b x i : ℕ) (hb : b ≤ h + 2)
    (hx : x < 2 ^ (h + 2)) (hi : i ≤ h + 2) : u.eval h b x i < 2 ^ (e.width * (h + 3)) :=
  (u.eval_lt h b x i hb hx hi).trans_le (grow (Nat.mul_le_mul_right _ hu.width_le))

end Index
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-! # Uniform arithmetic programs for the numeric routing data -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Index
open Coloring (B)
variable {M : ℕ}

def position (p : ProductChart M) :=
  cond site (total M) (op .add (op .mul (row p) (pow 2 (ceil (columns p)))) (col p))
    (op .add (total M) site)

def group (p : ProductChart M) := op .div (position p) (pow 2 block)

theorem eval_position (p : ProductChart M) (hM : 1 < M) (h b : ℕ) (x : B (h + 1)) (i : ℕ) :
    (position p).eval h b x.val i = p.position h x := by
  have hr : 0 < p.rows h := by
    have := (Nat.two_pow_pos h).trans_le (count_bounds hM h).1
    rw [← p.area h] at this
    exact Nat.pos_of_mul_pos_right this
  have hd : p.degree h ≤ 2 ^ (h + 1) :=
    (Nat.le_mul_of_pos_left _ hr).trans ((p.area h).le.trans (count_bounds hM h).2.le)
  have hl := Nat.clog_le_of_le_pow hd
  rw [position, eval_cond, ProductChart.position]
  simp only [site, eval, Register.eval, Arith.eval, eval_total _ _ _ _ hM]
  split
  · rename_i hx
    let y : Fin (count M h) := ⟨x, hx⟩
    have he := eval_ceil h b x.val i (columns p) _ (eval_columns hM h b p x.val) hd
    simp only [pow, eval, Arith.eval, he, min_eq_right (show Nat.clog 2 (p.degree h) ≤ h + 2 by omega)]
    exact congrArg₂ (fun a c : ℕ => a * 2 ^ (Nat.clog 2 (p.degree h)) + c)
      (eval_row hM h b y p i) (eval_col hM h b y p i)
  · rfl

theorem eval_group (p : ProductChart M) (hM : 1 < M) (h b : ℕ) (hb : b ≤ h + 2)
    (x : B (h + 1)) (i : ℕ) :
    (group p).eval h b x.val i = p.position h x / 2 ^ b := by
  simp only [group, pow, block, eval, Register.eval, Arith.eval, eval_position _ hM, min_eq_right hb]

noncomputable section
local instance : Fintype (ProductChart M) := Fintype.ofFinite _

/-- A finite set of queries. A query contains no height-dependent data. -/
inductive Query (M : ℕ)
  | digit (p : Equiv.Perm (Fin M))
  | position (p : ProductChart M)
  | group (p : ProductChart M)
  | base (p : ProductChart M)
  | location (p : ProductChart M)
  | assign (p : ProductChart M)
  | rows (p : ProductChart M)
  | columns (p : ProductChart M)
  | mask | total | len | rest
  deriving Fintype

end

def Query.code : Query M → Index M
  | .digit p => packDigit p
  | .position p => Index.position p
  | .group p => Index.group p
  | .base p => Index.base p
  | .location p => Index.location p
  | .assign p => Index.assign p
  | .rows p => Index.rows p
  | .columns p => Index.columns p
  | .mask => Index.mask M
  | .total => Index.total M
  | .len => Index.len M
  | .rest => Index.rest M

/-- The exponent bounds all chart and permutation choices, at every
height. Each intermediate fits in d*(h+3) bits by Part.eval_lt. -/
theorem Query.bounds (M : ℕ) :
    ∃ d, ∀ q : Query M, q.code.width ≤ d ∧ ∀ h, q.code.cost h ≤ (100 + h) ^ d := by
  let f := fun q : Query M => q.code.width + q.code.size + q.code.degree
  refine ⟨Finset.univ.sup f, fun q => ?_⟩
  have he := Finset.le_sup (f := f) (Finset.mem_univ q)
  change q.code.width + q.code.size + q.code.degree ≤ _ at he
  refine ⟨by omega, fun h => ?_⟩
  calc
    _ ≤ q.code.size * (h + 3) ^ q.code.degree := cost_le _ h
    _ ≤ (100 + h) ^ q.code.size * (100 + h) ^ q.code.degree :=
      Nat.mul_le_mul (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega) _))
        (Nat.pow_le_pow_left (by omega) _)
    _ ≤ _ := by rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Index
end

section
/-!
# Building chart data with the bounded arithmetic evaluator

All numerical fields come from the fixed query syntax. Proofs of
range and injectivity disappear from the executable data.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Index.Query
open Coloring (B)
variable {M : ℕ}

def digitMap (π : Equiv.Perm (Fin M)) (hM : 1 < M) (h : ℕ) : B (h + 1) → B (h + 1) :=
  let e := (digit π).code
  fun x => ⟨e.eval h 0 x.val 0, (eval_packDigit hM h 0 π x 0).trans_lt (Uniform.packDigit hM π h x).isLt⟩

theorem digitMap_eq (π : Equiv.Perm (Fin M)) (hM : 1 < M) (h : ℕ) :
    digitMap π hM h = Uniform.packDigit hM π h :=
  funext fun x => Fin.ext (eval_packDigit hM h 0 π x 0)

variable (p : ProductChart M) (hM : 1 < M) (h : ℕ)

def groupValue (b : ℕ) : B (h + 1) → ℕ :=
  let e := (group p).code
  fun x => e.eval h b x.val 0

include hM in
theorem groupValue_eq (b : ℕ) (hb : b ≤ h + 2) (x : B (h + 1)) :
    groupValue p h b x = p.position h x / 2 ^ b := eval_group p hM h b hb x 0

private def assignment : ℕ → B (h + 1) :=
  let e := (assign p).code
  fun x => if x < 2 ^ (h + 1) then
    ⟨e.eval h 0 x 0, (eval_assign p hM h 0 x 0).trans_lt ((reservation hM p h).assign x).isLt⟩
  else 0

private theorem assignment_eq : assignment p hM h = (reservation hM p h).assign := by
  funext x
  by_cases hx : x < 2 ^ (h + 1)
  · simp only [assignment, ite_eq_left hx]
    exact Fin.ext (eval_assign p hM h 0 x 0)
  · have hr : p.rows h ≤ 2 ^ (h + 1) := (Nat.le_mul_of_pos_right _ (p.degree_pos h hM)).trans
      ((p.area h).le.trans (count_bounds hM h).2.le)
    simp only [assignment, ite_eq_right hx, reservation, dite_eq_right (show ¬ x < p.rows h by omega)]

private def support : Reservation (h + 1) where
  size := (rows p).code.eval h 0 0 0
  assign := assignment p hM h
  unique := by
    change Set.InjOn _ (Set.Iio ((Index.rows p).eval h 0 0 0))
    rw [assignment_eq, eval_rows hM]
    exact (reservation hM p h).unique

private theorem support_eq : support p hM h = reservation hM p h := by
  have ext (x y : Reservation (h + 1)) (hs : x.size = y.size) (ha : x.assign = y.assign) : x = y := by
    cases x; cases y; cases hs; cases ha; rfl
  exact ext _ _ (eval_rows hM h 0 p 0 0) (assignment_eq p hM h)

def chart : Uniform.Chart (h + 1) where
  base :=
    let e := (base p).code
    fun x => ⟨e.eval h 0 x.val 0, (eval_base p hM h 0 x 0).trans_lt ((Uniform.chart hM p h).base x).isLt⟩
  location :=
    let e := (location p).code
    fun x => ⟨e.eval h 0 x.val 0, (eval_location p hM h 0 x 0).trans_lt ((Uniform.chart hM p h).location x).isLt⟩
  mask x := decide ((mask (M := M)).code.eval h 0 x.val 0 = 1)
  support := support p hM h
  degree := (columns p).code.eval h 0 0 0

theorem chart_eq : chart p hM h = Uniform.chart hM p h := by
  have ext (x y : Uniform.Chart (h + 1)) (a : x.base = y.base) (b : x.location = y.location)
      (c : x.mask = y.mask) (d : x.support = y.support) (e : x.degree = y.degree) : x = y := by
    cases x; cases y; cases a; cases b; cases c; cases d; cases e; rfl
  refine ext _ _ (funext fun x => Fin.ext (eval_base p hM h 0 x 0))
    (funext fun x => Fin.ext (eval_location p hM h 0 x 0)) ?_
    (support_eq p hM h) (eval_columns hM h 0 p 0 0)
  funext x
  change decide ((Index.mask M).eval h 0 x.val 0 = 1) = _
  rw [eval_mask p hM]
  cases (Uniform.chart hM p h).mask x <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Index.Query
end
