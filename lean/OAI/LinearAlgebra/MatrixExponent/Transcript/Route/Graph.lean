import OAI.LinearAlgebra.MatrixExponent.Tagged.SortBack
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Install.Weight
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Restore
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Choices
import OAI.LinearAlgebra.MatrixExponent.Transcript.RAM.Calls
import OAI.LinearAlgebra.MatrixExponent.Transcript.Cost
import OAI.LinearAlgebra.MatrixExponent.Shaving.Defs

/-! # Verifying a deterministic controller on two named tapes -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring

open Install
open scoped Classical
variable {F : Type} [Field F] {A D : Format} {f : A.obj → D.obj} {j k c : ℕ}

def graph (F : Type) [Field F] (A D : Format) (f : A.obj → D.obj)
    (z : A.pins ⊕ D.pins → Bool) : F :=
  if f (A.code.symm (z ∘ Sum.inl)) = D.code.symm (z ∘ Sum.inr) then 1 else 0

theorem Cheap.weight (h : Cheap F j k A D f c) :
    Weight F (graph F A D f) (2 ^ j * (100 + k) ^ c) := by
  obtain ⟨m, hf, hm⟩ := h
  let a := word A.width
  let b := word D.width
  let i : A.pins ≃ slots a := Fintype.equivOfCardEq (by simp [a, Format.width])
  let l : D.pins ≃ slots b := Fintype.equivOfCardEq (by simp [b, Format.width])
  obtain ⟨v, hv, hf⟩ := hf a b i l
  have hb : wd b = D.width := wd_word _
  apply Weight.of_layout (a := .pair a b) (i.sumCongr l)
  refine ⟨v + wd b, by omega, ?_⟩
  have hu (k : Val a → Val b → F) (hk : Net F a b k v) :
      Net F (.pair a b) .unit (fun x _ => k x.1 x.2) (v + wd b) := by
    have both := (hk.par (Tagged.cap b)).pre (.assoc a b b)
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using
      (both.post (.swap _ _)).trace
  convert hu _ hf using 1
  funext z _
  have he (u : D.obj) : u = D.code.symm (bits b z.2 ∘ l) ↔
      (bits b).symm (D.code u ∘ l.symm) = z.2 := by
    rw [Equiv.eq_symm_apply, Equiv.symm_apply_eq]
    simp only [funext_iff, Function.comp_apply]
    exact ⟨fun h t => by simpa using h (l.symm t), fun h t => by simpa using h (l t)⟩
  change (if f (A.code.symm (bits a z.1 ∘ i)) = D.code.symm (bits b z.2 ∘ l) then (1 : F) else 0) = _
  simp only [he, Function.comp_apply]

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

/-!
# Reading routed stations through a dictionary

Each station occupies exactly one installed seat. The other seats
are either dormant or encode withdrawn scalar factors.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript

open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {d U : ℕ} {T J : Type}

structure Dispatch (D : Dictionary F d) (U : ℕ) (G : Diagram F x y)
    (T : Type) (width : J → ℕ) extends Route G T where
  place : Selector G.V J
  label : G.V → Fin d → Bool
  correct : ∀ v, D.table (label v) = G.table v
  size : ∀ v, d + G.arity v ≤ U ∧ d + G.arity v ≤ 2 ^ (width (place.write v))
  extra : (s : J) → (RAM.token (width s)).obj

namespace Dispatch
variable {D : Dictionary F d} {G : Diagram F x y} {width : J → ℕ}
  (P : Dispatch D U G T width)

def request (a : Val x) (b : Val y) (q : T → Bool) (v : G.V) : List Bool :=
  query (P.label v) (G.table v) (Sum.elim (exterior a b) q ∘ P.tap v)

def emit (a : Val x) (b : Val y) (q : T → Bool) (s : J) : (RAM.token (width s)).obj :=
  (P.place.read s).elim (P.extra s) (fun v => RAM.encodeToken _ (P.request a b q v))

def factor (s : J) : F :=
  if P.place.read s = none then RAM.tokenValue U D.eval (width s) (P.extra s) else 1

variable [Fintype J]

def scalar : F := ∏ s, P.factor s

theorem product (a : Val x) (b : Val y) (q : T → Bool) :
    (∏ s, RAM.tokenValue U D.eval (width s) (P.emit a b q s)) =
      P.scalar * ∏ v, P.toRoute.vertex a b q v := by
  have he (s : J) : RAM.tokenValue U D.eval (width s) (P.emit a b q s) =
      P.factor s * ∏ v, if s = P.place.write v then P.toRoute.vertex a b q v else 1 := by
    simp_rw [← P.place.valid]
    unfold emit factor
    cases h : P.place.read s with
    | none => simp
    | some v =>
      have hl : (P.request a b q v).length = d + G.arity v := query_length _ _ _
      have hv := P.size v
      rw [← (P.place.valid _ _).mp h] at hv
      simp only [Option.elim_some, reduceCtorEq, ite_false, one_mul, Option.some.injEq,
        Finset.prod_ite_eq, Finset.mem_univ, ite_true]
      rw [RAM.tokenValue_encode _ _ _ (hl.le.trans hv.1) (hl.le.trans hv.2)]
      exact D.eval_query _ _ (P.correct v) _
  simp_rw [he]
  rw [Finset.prod_mul_distrib, Finset.prod_comm]
  simp only [scalar, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

end Dispatch
end OAI.LinearAlgebra.MatrixExponent.Transcript
end

/-!
# Contracting a selected family

Control bits include intermediate deterministic decisions. A valid
selector has only one encoding. Payload bits may include paths and
padding; each internal edge retains exactly one independent bit.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript

open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {d U : ℕ} {T J I C : Type}
  {width : J → ℕ} {D : Dictionary F d} {G : I → Diagram F x y}

namespace Dispatch

variable (S : Selector I C) (P : ∀ i, Dispatch D U (G i) T width)

def authorized (a : Val x) (b : Val y) (c : C) (t : T → Bool) : Prop :=
  ∃ i, S.read c = some i ∧ (P i).copies.Agrees (exterior a b) t

/-- Multiplicity is checked on both levels, first the internal wires
of a summand and then the index of the summand. -/
theorem sum [Fintype I] [Fintype C] [Fintype T] [Fintype J] (a : Val x) (b : Val y)
    (ok : C → (T → Bool) → Prop)
    (calls : C → (T → Bool) → (s : J) → (RAM.token (width s)).obj)
    (allowed : ∀ c t, ok c t ↔ authorized S P a b c t)
    (reads : ∀ i t, (P i).copies.Agrees (exterior a b) t →
      calls (S.write i) t = (P i).emit a b t) :
    (∑ c, ∑ t, if ok c t then ∏ s, RAM.tokenValue U D.eval (width s) (calls c t s) else 0) =
      ∑ i, (P i).scalar * (G i).eval a b := by
  rw [← S.sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  cases h : S.read c with
  | none =>
    have he (t) : ¬ok c t := by simp [allowed, authorized, h]
    simp [he]
  | some i =>
    have he (t) : ok c t ↔ (P i).copies.Agrees (exterior a b) t := by
      simp only [allowed, authorized, h, Option.some.injEq, exists_eq_left']
    simp only [Option.elim_some]
    rw [← (P i).toRoute.contract, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hx : ok c t
    · rw [ite_eq_left hx, (S.valid _ _).mp h, reads _ _ ((he _).mp hx), product]
      simp only [Route.value, ite_eq_left ((he _).mp hx)]
    · rw [ite_eq_right hx, Route.value, ite_eq_right (mt (he _).mpr hx), mul_zero]

end Dispatch
end OAI.LinearAlgebra.MatrixExponent.Transcript
end

/-!
# A charged sheet of bit-RAM processors

The fixed actors hold the static inputs. The other actors are
dyadic slots. Their programs read public or guessed bits, check
local consistency, and emit dictionary calls. The packet tape
uses the same bit sources.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.RAM

abbrev Actor (P V k : ℕ) := Fin P ⊕ Slot P V k

def quota {P V k : ℕ} : Actor P V k → ℕ := Sum.elim (fun _ => 1) capacity

/-- A variable-length transcript in dyadic slot form. -/
structure Layout (x y : Wire) (P V k j H w U : ℕ) where
  hidden : Wire
  port : Actor P V k → Wire
  processor : (i : Actor P V k) → Processor (port i) (quota i) U
  read : ∀ i, slots (port i) → slots (.pair (.pair x y) hidden)
  messages : slots (tree j (Messages.row H w)) → slots (.pair (.pair x y) hidden)

variable {x y : Wire} {P V k j H w U : ℕ} {F : Type} [Field F]

namespace Layout

variable (L : Layout x y P V k j H w U) (W : List Bool → F)

def sheet : Sheet F x y j H w where
  privateBits := L.hidden
  I := Actor P V k
  port := L.port
  data i z := (L.processor i).value W (bits (L.port i) z)
  read := L.read
  messages := L.messages

theorem localChecks (i : Actor P V k) :
    ∃ n ≤ (L.processor i).cost, Wide F (8 * (U + 1)) (labels U W)
      (L.port i) .unit (fun z _ => (L.sheet W).data i z) n :=
  (L.processor i).build W _ (Equiv.refl _)

/-- Resource bounds before verification. `B` absorbs polylogarithmic
factors, `C` the per-processor allowance, including partial packets. -/
structure Fits (B C : ℕ) : Prop where
  base : 100 ≤ B
  buckets : k + 1 ≤ B
  dictionary : ceiling U + 1 ≤ B
  perimeter : wd x + wd y + wd L.hidden + 2 ^ j * w ≤ B * (V + P * C)
  inputs : ∀ i, wd (L.port i) ≤ B * (quota i + C)
  time : ∀ i, 2 ^ (L.processor i).clock ≤ B * (quota i + C)
  widths : ∀ i, 100 + (L.processor i).clock + (L.processor i).addressBits ≤ B
  gates : ∀ i, 2 ^ ((L.processor i).fanIn + 3) ≤ B

private theorem actor_sum (C : ℕ) (hC : 1 ≤ C) :
    ∑ i : Actor P V k, (quota i + C) ≤ 3 * (k + 1) * (V + P * C) := by
  rw [Fintype.sum_sum_type]
  simp only [quota, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  have h₁ := sum_capacity P V k
  have h₂ := Nat.mul_le_mul_right C (Transcript.card_slots P V k)
  have h₃ : P ≤ P * C := Nat.le_mul_of_pos_right P hC
  have h₄ : P * C ≤ (k + 1) * (P * C) := Nat.le_mul_of_pos_left _ (by omega)
  linarith only [h₁, h₂, h₃, h₄, Nat.zero_le ((k + 1) * V)]

variable {B C : ℕ}

private theorem Fits.actor_bound (h : L.Fits B C) (hC : 1 ≤ C) (i : Actor P V k) :
    (L.processor i).cost ≤ 3000 * B ^ 101 * (quota i + C) := by
  let t := quota i + C
  have ht : 0 < t := by unfold t; omega
  have hB : 0 < B := lt_of_lt_of_le (by decide) h.base
  have hpow : B ≤ B ^ 100 := Nat.le_pow (by decide)
  have hp : 0 < B ^ 100 := pow_pos hB _
  have hg : 3 + 4 * (100 + (L.processor i).clock + (L.processor i).addressBits) ^ 100
      + 32 * 2 ^ ((L.processor i).fanIn + 3) ≤ 39 * B ^ 100 := by
    have h₁ := Nat.pow_le_pow_left (h.widths i) 100
    have h₂ := (h.gates i).trans hpow
    omega
  have he := Nat.mul_le_mul (h.time i) hg
  have hd : (ceiling U + 1) * quota i ≤ B * t := Nat.mul_le_mul h.dictionary (Nat.le_add_right _ _)
  have hi := h.inputs i
  change wd (L.port i) ≤ B * t at hi
  have hcost : (L.processor i).cost ≤ 9 * (B * t + B * t * (39 * B ^ 100) + 194 + 10 * (B * t)) := by
    unfold Processor.cost Program.expense
    change _ ≤ B * t * (39 * B ^ 100) at he
    rw [mul_assoc 10]
    omega
  refine hcost.trans ?_
  change _ ≤ 3000 * B ^ 101 * t
  rw [show B ^ 101 = B * B ^ 100 from pow_succ' _ _]
  generalize B ^ 100 = a at hp ⊢
  have hbt : 0 < B * t := mul_pos hB ht
  linarith only [hbt, Nat.le_mul_of_pos_right (B * t) hp]

theorem Fits.volume (h : L.Fits B C) (hC : 1 ≤ C) :
    (L.sheet W).volume (fun i => (L.processor i).cost) + 2 ^ j * w ≤ B ^ 104 * (V + P * C) := by
  have ha := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Fits.actor_bound L h hC i)
  rw [← Finset.mul_sum] at ha
  have hb : (∑ i : Actor P V k, (quota i + C)) ≤ 3 * B * (V + P * C) :=
    (actor_sum C hC).trans (by gcongr; exact h.buckets)
  have hc := ha.trans (Nat.mul_le_mul_left _ hb)
  have hd : (L.sheet W).volume (fun i => (L.processor i).cost) + 2 ^ j * w ≤
      B * (V + P * C) + 3000 * B ^ 101 * (3 * B * (V + P * C)) := by
    change wd x + wd y + wd L.hidden + (∑ i, (L.processor i).cost) + 2 ^ j * w ≤ _
    have := h.perimeter
    omega
  refine hd.trans ?_
  rw [show B ^ 104 = B ^ 102 * B ^ 2 from pow_add B 102 2,
    show B * (V + P * C) + 3000 * B ^ 101 * (3 * B * (V + P * C)) = (B + 9000 * B ^ 102) * (V + P * C) by ring]
  apply Nat.mul_le_mul_right
  have h₁ : B ≤ B ^ 102 := Nat.le_pow (by decide)
  have h₂ : 10000 ≤ B ^ 2 := by nlinarith only [h.base]
  have := Nat.mul_le_mul_left (B ^ 102) h₂
  omega

end Layout
end OAI.LinearAlgebra.MatrixExponent.Transcript.RAM
end

section
/-!
# Realization of a charged slot transcript

This is the slot normal form for the transcript estimate. A fixed
layout supplies the programs, their wiring and the packet format.
The bound has no network-cost or network-existence premise for any
local processor.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.RAM.Layout

open Filter

theorem realizes {F : Type} [Field F] (wide : Radix.WideTag F) {τ : ℝ} (hτ : 0 < τ) (c : ℕ) :
    ∃ A C₀ : ℕ, 1 < A ∧ ∀ q : ℕ, ∀ᶠ h : ℕ in atTop,
    ∀ (K : Type) [Field K] [Algebra F K] (x y : Wire) (P V k j H U B : ℕ)
      (L : Layout x y P V k j H (h ^ A) U) (W : List Bool → K),
      1 ≤ j → j ≤ h ^ 2 → H ≤ h ^ 2 → (B : ℝ) ≤ (Real.log h) ^ q → L.Fits B (h ^ (A + c)) →
      ∃ s, Wide K (8 * (U + 1)) (labels U W) x y (L.sheet W).eval s ∧
        (s : ℝ) ≤ (h : ℝ) ^ τ * V + P * (h : ℝ) ^ C₀ := by
  obtain ⟨A, C₀, hA, ht⟩ := Sheet.realizes wide hτ c
  refine ⟨A, C₀, hA, fun q => ?_⟩
  filter_upwards [ht (q * 104), eventually_ge_atTop 1] with h he hh
    K _ _ x y P V k j H U B L W hj hlen hH hB hf
  refine he K x y P V j H (8 * (U + 1)) (labels U W) (L.sheet W)
    (fun i => (L.processor i).cost) hj hlen hH (by omega) (L.localChecks W) ?_
  have hv := Fits.volume L W hf (one_le_pow₀ hh)
  calc
    _ ≤ (↑(B ^ 104 * (V + P * h ^ (A + c)) : ℕ) : ℝ) := Nat.cast_le.mpr hv
    _ = (B : ℝ) ^ 104 * ((V : ℝ) + P * (h : ℝ) ^ (A + c)) := by push_cast; rfl
    _ ≤ _ := by
      rw [pow_mul]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hB 104) (by positivity)

end OAI.LinearAlgebra.MatrixExponent.Transcript.RAM.Layout
end

/-!
# Recovering the sum over processor records

The three layout checks are the bucket order, the capacity claimed
by each active slot, and occurrence of each processor exactly once.
An accepted encoding can therefore be decoded without multiplicity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript

open scoped Classical
variable {P V k : ℕ} {R : Type} {c : Fin P → R → ℕ} {y : Records P V k R}

structure Canonical (c : Fin P → R → ℕ) (y : Records P V k R) : Prop where
  sorted : ∀ j : Fin (k + 1), Monotone (fun i => name (y ⟨j, i⟩))
  fits : ∀ s p r, y s = some (p, r) → Nat.clog 2 (c p r) = s.1.val
  occurs : ∀ p, ∃! s, ∃ r, y s = some (p, r)

theorem Canonical.records (h : Canonical c y) : ∃ x, Encodes c x y := by
  choose s hs hu using h.occurs
  choose x hx using hs
  have hh (i p r) (he : y i = some (p, r)) : i = s p ∧ r = x p := by
    have eq := hu p i ⟨r, he⟩
    rw [eq, hx] at he
    exact ⟨eq, (Prod.mk.inj (Option.some.inj he)).2.symm⟩
  have he (i p) (hi : name (y i) = p.castSucc) : i = s p := by
    cases hv : y i with
    | none => simp [hv, name, Ne.symm (Fin.castSucc_ne_last p)] at hi
    | some z =>
      obtain ⟨q, r⟩ := z
      have hpq : q = p := by simpa [hv, name] using hi
      exact hpq ▸ (hh _ _ _ hv).1
  refine ⟨x, fun j => ⟨h.sorted j, ?_, ?_⟩, ?_⟩
  · intro p
    simp only [bucket, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h.fits _ _ _ (hx p)]
    constructor
    · rintro ⟨i, hi⟩
      rw [← he _ _ hi]
    · intro eq
      have e : (s p).1 = j := Fin.ext eq
      subst j
      exact ⟨(s p).2, by simp [hx, name]⟩
  · intro i i' heq hlast
    obtain ⟨p, hp⟩ := Fin.exists_castSucc_eq.mpr hlast
    have hh := (he _ p hp.symm).trans (he _ p (heq.symm.trans hp.symm)).symm
    exact eq_of_heq (Sigma.mk.inj hh).2
  · intro i
    cases hv : y i with
    | none => simp [readRecord, name]
    | some z =>
      obtain ⟨p, r⟩ := z
      simp [readRecord, name, (hh i p r hv).2]

namespace RAM.Layout
variable {a b : Wire} {j H w U : ℕ} {F : Type} [Field F]
  (L : Layout a b P V k j H w U) (W : List Bool → F)

def entry (x : Val a) (y : Val b) (z : Val L.hidden) : F :=
  if Messages.valid j H w (Install.project L.messages ((x, y), z))
  then ∏ i, (L.sheet W).data i (Install.project (L.read i) ((x, y), z)) else 0

/-- Local decoding and inverse encoding on accepted records suffice.
Rejected private assignments may have noncanonical encodings. -/
theorem eval_records [Fintype R] (x : Val a) (y : Val b)
    (c : Fin P → R → ℕ) (good : (Fin P → R) → Prop) (value : (Fin P → R) → F)
    (read : Val L.hidden → Records P V k R) (write : Records P V k R → Val L.hidden)
    (bounds : ∀ z, good z → (∀ p, 0 < c p (z p) ∧ c p (z p) ≤ 2 ^ k) ∧ ∑ p, c p (z p) ≤ V)
    (live : ∀ b, L.entry W x y b ≠ 0 → Canonical c (read b) ∧ write (read b) = b ∧
      ∀ z, Encodes c z (read b) → good z)
    (accept : ∀ z s, good z → Encodes c z s → read (write s) = s ∧ L.entry W x y (write s) = value z) :
    (L.sheet W).eval x y = ∑ z, if good z then value z else 0 := by
  let f := L.entry W x y
  let g := fun s => ∑ b, if read b = s then f b else 0
  have hg : (L.sheet W).eval x y = ∑ s, g s := by
    change ∑ b, f b = _
    unfold g
    rw [Finset.sum_comm]
    simp
  rw [hg]
  apply encode_sum c good value g bounds
  · intro z s hz hs
    obtain ⟨h₁, h₂⟩ := accept z s hz hs
    unfold g
    rw [Finset.sum_eq_single (write s)]
    · simpa [h₁] using h₂
    · intro b _ hb
      split
      · rename_i he
        by_contra! hh
        exact hb ((live b hh).2.1.symm.trans (congrArg write he))
      · rfl
    · simp
  · intro s hs
    apply Finset.sum_eq_zero
    intro b _
    split
    · rename_i he
      by_contra! hb
      obtain ⟨hc, _, hv⟩ := live b hb
      obtain ⟨z, hz⟩ := hc.records
      exact hs ⟨z, hv z hz, he ▸ hz⟩
    · rfl

end RAM.Layout
end OAI.LinearAlgebra.MatrixExponent.Transcript
end

/-!
# From local controller observations to a weighted diagram family

The two observations are bit-level acceptance and the strings on
dictionary seats. Internal edges and exterior arguments are transported
by the declared equality links.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.RAM.Layout

open scoped Classical
variable {F : Type} [Field F] {x y : Wire} {P V k j H w U : ℕ}
  (L : Layout x y P V k j H w U)

abbrev Seat (P V k U : ℕ) := Σ i : Actor P V k, Calls (quota i) U

def depth (s : Seat P V k U) := s.2.1.val

def signals (a : Val x) (b : Val y) (z : Val L.hidden) (i : Actor P V k) :=
  (L.processor i).program.eval (bits (L.port i) (Install.project (L.read i) ((a, b), z)))

def ok (a : Val x) (b : Val y) (z : Val L.hidden) : Prop :=
  Messages.valid j H w (Install.project L.messages ((a, b), z)) ∧
    ∀ i, L.signals a b z i (L.processor i).accept = true

def calls (a : Val x) (b : Val y) (z : Val L.hidden) (s : Seat P V k U) :
    (token (depth s)).obj :=
  (token (depth s)).code.symm (L.signals a b z s.1 ∘ (L.processor s.1).call s.2)

theorem entry_eq (W : List Bool → F) (a : Val x) (b : Val y) (z : Val L.hidden) :
    L.entry W a b z =
      if L.ok a b z then ∏ s, tokenValue U W (depth s) (L.calls a b z s) else 0 := by
  unfold entry ok
  by_cases hm : Messages.valid j H w (Install.project L.messages ((a, b), z))
  swap
  · simp only [hm, false_and, ite_false]
  simp only [hm, true_and, ite_true]
  have hd (i : Actor P V k) :
      (L.sheet W).data i (Install.project (L.read i) ((a, b), z)) =
        if L.signals a b z i (L.processor i).accept then
          ∏ s, tokenValue U W (depth ⟨i, s⟩) (L.calls a b z ⟨i, s⟩) else 0 := rfl
  by_cases hp : ∀ i, L.signals a b z i (L.processor i).accept = true
  · rw [ite_eq_left hp, Fintype.prod_sigma]
    exact Finset.prod_congr rfl (fun i _ => (hd i).trans (ite_eq_left (hp i)))
  · rw [ite_eq_right hp]
    obtain ⟨i, hi⟩ := not_forall.mp hp
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((hd i).trans (ite_eq_right hi))

variable {d : ℕ} {I C T : Type} (D : Dictionary F d) (G : I → Diagram F x y)

/-- Selector snapshots are encoded separately from the routed bits.
The dictionary data are checked only on accepted snapshots. -/
structure Implements where
  choice : Selector I C
  store : C × (T → Bool) ≃ Val L.hidden
  dispatch : ∀ i, Dispatch D U (G i) T (depth (P := P) (V := V) (k := k) (U := U))
  allowed : ∀ a b c t, L.ok a b (store (c, t)) ↔ Dispatch.authorized choice dispatch a b c t
  emits : ∀ a b i t, (dispatch i).copies.Agrees (exterior a b) t →
    L.calls a b (store (choice.write i, t)) = (dispatch i).emit a b t

theorem Implements.eval [Fintype I] [Fintype C] [Fintype T] (H : L.Implements D G (C := C) (T := T))
    (a : Val x) (b : Val y) :
    (L.sheet D.eval).eval a b = ∑ i, (H.dispatch i).scalar * (G i).eval a b := by
  change (∑ z, L.entry D.eval a b z) = _
  rw [← Equiv.sum_comp H.store, Fintype.sum_prod_type]
  simp_rw [entry_eq]
  exact Dispatch.sum H.choice H.dispatch a b _ _ (H.allowed a b) (H.emits a b)

end OAI.LinearAlgebra.MatrixExponent.Transcript.RAM.Layout
end

/-! # Labeled networks for a selected family of routed diagrams -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.RAM

open Filter
open scoped Classical

theorem labeled {K : Type} [Field K] {a b : Wire} {f : Val a → Val b → K}
    {W : List Bool → K} {U s : ℕ} (h : Wide K (8 * (U + 1)) (labels U W) a b f s) :
    Labeled f (ceiling U + 1) s (8 * (U + 1)) := by
  let L := (Finset.range (ceiling U + 1)).image (label U W)
  have he : (↑L : Set (Table K)) = labels U W := by
    ext
    simp [L, labels]
  exact ⟨L, Finset.card_image_le.trans_eq (Finset.card_range _), he.symm ▸ h⟩

theorem Layout.realizes_routes {F : Type} [Field F] (wide : Radix.WideTag F)
    {τ : ℝ} (hτ : 0 < τ) (c : ℕ) :
    ∃ A C₀ : ℕ, 1 < A ∧ ∀ q : ℕ, ∀ᶠ h : ℕ in atTop,
    ∀ (K I C T : Type) [Field K] [Algebra F K] [Fintype I] [Fintype C] [Fintype T]
      (x y : Wire) (P V k j H U B d : ℕ) (L : Layout x y P V k j H (h ^ A) U)
      (D : Dictionary K d) (G : I → Diagram K x y) (E : L.Implements D G (C := C) (T := T)),
      1 ≤ j → j ≤ h ^ 2 → H ≤ h ^ 2 → (B : ℝ) ≤ (Real.log h) ^ q → L.Fits B (h ^ (A + c)) →
      ∃ s, Labeled (fun a b => ∑ i, (E.dispatch i).scalar * (G i).eval a b)
        (ceiling U + 1) s (8 * (U + 1)) ∧ (s : ℝ) ≤ (h : ℝ) ^ τ * V + P * (h : ℝ) ^ C₀ := by
  obtain ⟨A, C, hA, ht⟩ := Layout.realizes wide hτ c
  refine ⟨A, C, hA, fun q => ?_⟩
  filter_upwards [ht q] with h he K I C T _ _ _ _ _ x y P V k j H U B d L D G E hj hj' hH hB hfit
  obtain ⟨s, hs, hcost⟩ := he K x y P V k j H U B L D.eval hj hj' hH hB hfit
  refine ⟨s, ?_, hcost⟩
  have hv : (L.sheet D.eval).eval = fun a b => ∑ i, (E.dispatch i).scalar * (G i).eval a b :=
    funext fun a => funext fun b => Layout.Implements.eval L D G E a b
  exact hv ▸ labeled hs

end OAI.LinearAlgebra.MatrixExponent.Transcript.RAM
end
