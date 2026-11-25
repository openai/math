import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomCostSyntax
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomMatrix
import OAI.Computability.NearSquareRoot.ScheduleRegisterTableEffective
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomSyntax

/-! # A packed arithmetic command generated from a literal table file -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open CommonRegisters Space InterchangeROMTable GeneratorSyntax

private theorem rows_le_clock {x y : Tree} {tab : List (Tree × Tree)} (hm : (x,y) ∈ tab) :
    x.count + y.count + 1 ≤ RegisterTable.cost tab := by
  induction tab with
  | nil => contradiction
  | cons uv tab ih =>
    rcases uv with ⟨u,v⟩
    rw [RegisterTable.cost]
    rcases List.mem_cons.mp hm with h | h
    · cases h
      omega
    · have := ih h
      omega

/-- The literal command takes a numeric scaffold rank, output width, and an
ordered list of spelled input/output tuple pairs. -/
def romPayload (rank m : ℕ) (bytes : SpellingTable) : Cmd :=
  let dst := Series.natural m
  alignedCommand rank dst (alignedCommand rank dst (RegisterTable.build bytes))

theorem romPayload_within (rank m : ℕ) (bytes : SpellingTable) :
    Within 4 (romPayload rank m bytes) :=
  aligned_within _ _ (aligned_within _ _ (RegisterTable.within (by decide) bytes))

/-- Actual execution and absolute register ceiling for the literal, effective
table reader, including all copies, cleanup, and both restores of column order. -/
theorem romLayout_bounded {K L A : Type} [DecidableEq K] [DecidableEq L] {P : A → Type}
    (src : Series K) (dst : Series L) (k : K)
    (rows : Series A) (payload : (a : A) → Series (P a)) (width : ℕ) (hw : ∀ a, (payload a).count ≤ width)
    (v : (a : A) → P a → K → Tree) (w : (a : A) → P a → L → Tree) (tab : List (Tree × Tree))
    (ht : ∀ a j, RegisterLookup.read tab (stripe src (v a j)) = stripe dst (w a j) ∧
      (stripe src (v a j), stripe dst (w a j)) ∈ tab)
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let bytes := spelledTable tab
    let D := romPayloadFactor src.count dst.count bytes * (rows.count * (width + 1) + 1)
    BoundedFits env (romPayload (src.explore.idxOf k) dst.count bytes)
      (pile 0 (stripe src (fun z => stripe rows fun a => stripe (payload a) (fun j => v a j z))) r)
      (pile 0 (stripe dst (fun z => stripe rows fun a => stripe (payload a) (fun j => w a j z))) r)
      D (base + D) D := by
  have sz (a j) := rows_le_clock (ht a j).2
  have h (a j env r base) (hd : DeckCap base r) :
      BoundedFits env (RegisterTable.command tab) (pile 0 (stripe src (v a j)) r)
        (pile 0 (stripe dst (w a j)) r) (2 * RegisterTable.cost tab)
        (base + 2 * RegisterTable.cost tab) (2 * RegisterTable.cost tab) := by
    have one := RegisterTable.run_lookup tab _ _ (ht a j).2 (ht a j).1 env r
    have hsize := sz a j
    change (stripe src (v a j)).count + _ + 1 ≤ _ at hsize
    exact (BoundedFits.of_fits one (cap := base + 2 * RegisterTable.cost tab) (depth := 2 * RegisterTable.cost tab)
      (fun i => by have := hd.pile 0 (stripe src (v a j)) i; change (letters (pile 0 (stripe src (v a j)) r) i).length + _ ≤ _; omega)
      (by omega)).mono (by omega) le_rfl le_rfl
  have call := packed_bounded src dst rows payload width hw k v w (RegisterTable.command tab)
    (2 * RegisterTable.cost tab)
    (fun a j z => by
      have sf := count_le_forest (v a j) (src.complete z)
      rw [← stripe_simple] at sf
      have u := sz a j
      change (stripe src (v a j)).count + _ + 1 ≤ _ at u
      omega)
    (fun a j z => by
      have sf := count_le_forest (w a j) (dst.complete z)
      rw [← stripe_simple] at sf
      have u := sz a j
      change _ + (stripe dst (w a j)).count + 1 ≤ _ at u
      omega)
    h env r base hr
  dsimp only at call ⊢
  let rank := src.explore.idxOf k
  rw [aligned_eq_natural rank dst (RegisterTable.command tab),
    aligned_eq_natural rank dst (alignedCommand rank (Series.natural dst.count) (RegisterTable.command tab))] at call
  have eqleaf : RegisterTable.build (spelledTable tab) = RegisterTable.command tab := rfl
  rw [romPayloadFactor, wordClock_spelledTable]
  unfold romPayload
  rw [eqleaf]
  exact call

theorem romPayload_bounded {n m : ℕ} {A : Type} {P : A → Type} (k : Fin n)
    (rows : Series A) (payload : (a : A) → Series (P a)) (width : ℕ) (hw : ∀ a, (payload a).count ≤ width)
    (v : (a : A) → P a → Fin n → Tree) (w : (a : A) → P a → Fin m → Tree) (tab : List (Tree × Tree))
    (ht : ∀ a j, RegisterLookup.read tab (stripe (Series.natural n) (v a j)) = stripe (Series.natural m) (w a j) ∧
      (stripe (Series.natural n) (v a j), stripe (Series.natural m) (w a j)) ∈ tab)
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let bytes := spelledTable tab
    let D := romPayloadFactor n m bytes * (rows.count * (width + 1) + 1)
    BoundedFits env (romPayload k.val m bytes)
      (pile 0 (stripe (Series.natural n) (fun z => stripe rows fun a => stripe (payload a) (fun j => v a j z))) r)
      (pile 0 (stripe (Series.natural m) (fun z => stripe rows fun a => stripe (payload a) (fun j => w a j z))) r)
      D (base + D) D := by
  have h := romLayout_bounded (Series.natural n) (Series.natural m) k rows payload width hw v w tab ht env r base hr
  have idx : (Series.natural n).explore.idxOf k = k.val := List.idxOf_finRange k
  simpa only [Series.count_natural, idx] using h

open private numeral_stripe from OAI.Computability.NearSquareRoot.ScheduleRegisterLoomMatrix

/-- The effective numeric matrix file acts at every actual residue vector in the bank. -/
theorem romMatrix_bounded {p n m : ℕ} [NeZero p] (k : Fin n) (M : Matrix (Fin m) (Fin n) (ZMod p))
    {A : Type} {P : A → Type} (rows : Series A) (payload : (a : A) → Series (P a)) (width : ℕ)
    (hw : ∀ a, (payload a).count ≤ width) (x : (a : A) → P a → Fin n → ZMod p)
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let bytes := spelledTable (matrixTable p n (List.ofFn fun i => residues (M i)))
    let D := romPayloadFactor n m bytes * (rows.count * (width + 1) + 1)
    BoundedFits env (romPayload k.val m bytes)
      (pile 0 (stripe (Series.natural n) fun z => stripe rows fun a =>
        stripe (payload a) fun j => numeral (x a j z).val) r)
      (pile 0 (stripe (Series.natural m) fun z => stripe rows fun a =>
        stripe (payload a) fun j => numeral (M.mulVec (x a j) z).val) r) D (base + D) D := by
  apply romPayload_bounded k rows payload width hw _ _ _ _ env r base hr
  intro a j
  simpa only [numeral_stripe] using matrixTable_correct M (x a j)

/-- Computably given layout sizes and a spelled table generate the machine's actual
P192 syntax file. -/
theorem effective_romPayload {X : Type} [Primcodable X] {rank m : X → ℕ} {bytes : X → SpellingTable}
    (hr : Computable rank) (hm : Computable m) (hb : Computable bytes) :
    Effective ltr (fun x => romPayload (rank x) (m x) (bytes x)) := by
  have n : Computable (fun x => (Series.natural (m x)).count) := by simpa only [Series.count_natural] using hm
  have leaf : Effective ltr (fun x => RegisterTable.build (bytes x)) := RegisterTable.effective_build.comp hb
  exact effective_aligned hr _ n (effective_aligned hr _ n leaf)

/-- A finite ring modulus, both arities, and numeric coefficient lists suffice
to generate the full modular matrix program file, including the lookup ROM. -/
theorem effective_romMatrix {X : Type} [Primcodable X] {p n m k : X → ℕ}
    {coefficients : X → List (List ℕ)} (hp : Computable p) (hn : Computable n)
    (hm : Computable m) (hk : Computable k) (hc : Computable coefficients) :
    Effective ltr (fun x => romPayload (k x) (m x) (spelledTable (matrixTable (p x) (n x) (coefficients x)))) := by
  have ht : Primrec (fun v : ℕ × ℕ × List (List ℕ) => spelledTable (matrixTable v.1 v.2.1 v.2.2)) :=
    primrec_spelled_matrixTable Primrec.fst (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact effective_romPayload hk hm (ht.to_comp.comp (hp.pair (hn.pair hc)))

/-- The nullary operation uses one template lane. Its raw key is the one-field
forest containing a false leaf, spelled as node, false, false. -/
def romConstant (m : ℕ) (value : List ℕ) : Cmd :=
  romPayload 0 m [([2, 0, 0], value)]

theorem effective_romConstant {X : Type} [Primcodable X] {m : X → ℕ} {value : X → List ℕ}
    (hm : Computable m) (hv : Computable value) : Effective ltr (fun x => romConstant (m x) (value x)) :=
  effective_romPayload (Computable.const 0) hm
    (Computable.list_cons.comp ((Computable.const [2, 0, 0]).pair hv) (Computable.const []))

theorem romConstant_bounded {m : ℕ} {A : Type} {P : A → Type} (value : Fin m → Tree)
    (rows : Series A) (payload : (a : A) → Series (P a)) (width : ℕ)
    (hw : ∀ a, (payload a).count ≤ width) (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let word := spelling (stripe (Series.natural m) value)
    let D := romPayloadFactor 1 m [([2, 0, 0], word)] * (rows.count * (width + 1) + 1)
    BoundedFits env (romConstant m word)
      (pile 0 (stripe templateLane fun _ => stripe rows fun a => stripe (payload a) fun _ => .atom false) r)
      (pile 0 (stripe (Series.natural m) fun z => stripe rows fun a => stripe (payload a) fun _ => value z) r)
      D (base + D) D := by
  let input := stripe (Series.natural 1) (fun _ => Tree.atom false)
  let output := stripe (Series.natural m) value
  let tab := [(input,output)]
  have good : RegisterLookup.read tab input = output ∧ (input,output) ∈ tab := by
    simp [tab, RegisterLookup.read]
  have h := romPayload_bounded (0 : Fin 1) rows payload width hw (fun _ _ _ => .atom false)
    (fun _ _ => value) tab (fun _ _ => good) env r base hr
  exact h

/-- A modular matrix with no input vector lanes computes the zero vector on
each cell of the template. The uniform generator needs only its output width. -/
theorem romZeroMatrix_bounded {p m : ℕ} (M : Matrix (Fin m) (Fin 0) (ZMod p))
    {A : Type} {P : A → Type} (rows : Series A) (payload : (a : A) → Series (P a)) (width : ℕ)
    (hw : ∀ a, (payload a).count ≤ width) (x : (a : A) → P a → Fin 0 → ZMod p)
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let word := spelling (stripe (Series.natural m) (fun _ => numeral 0))
    let D := romPayloadFactor 1 m [([2, 0, 0], word)] * (rows.count * (width + 1) + 1)
    BoundedFits env (romConstant m word)
      (pile 0 (stripe templateLane fun _ => stripe rows fun a => stripe (payload a) fun _ => .atom false) r)
      (pile 0 (stripe (Series.natural m) fun z => stripe rows fun a =>
        stripe (payload a) fun j => numeral (M.mulVec (x a j) z).val) r) D (base + D) D := by
  simpa only [Matrix.mulVec, dotProduct, Fintype.sum_empty, ZMod.val_zero] using
    romConstant_bounded (fun _ : Fin m => numeral 0) rows payload width hw env r base hr

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
