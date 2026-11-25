import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomAlignedCost
import OAI.Computability.NearSquareRoot.InterchangeROMTable

/-!
# Literal P192 table programs for aligned records and their contiguous payloads

Both applications read the same serialized column bank as the interchange.
The inner application assembles the tuple at a payload address. The outer
one groups and restores corresponding record streams. The emitted program
and its integer resource factors are determined by its finite table, field
orders and the selected scaffold column.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open CommonRegisters Space RegisterLookup

/-- Maximum per-address clock and extra working space of a literal lookup. -/
def lookupFactor (tab : List (Tree × Tree)) : ℕ :=
  6 * (limit Prod.fst tab + limit Prod.snd tab + 1)

private theorem raw_bounded (tab : List (Tree × Tree)) (x y : Tree) (hrd : read tab x = y)
    (hm : (x, y) ∈ tab) (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    BoundedFits env (command tab) (pile 0 x r) (pile 0 y r)
      (lookupFactor tab) (base + lookupFactor tab) (lookupFactor tab) := by
  have input := le_limit Prod.fst hm
  change x.count ≤ limit Prod.fst tab at input
  have h := run tab x y hrd hm env r
  apply (BoundedFits.of_fits h (cap := base + lookupFactor tab) (depth := lookupFactor tab)
    (fun i => by have := hr.pile 0 x i; dsimp [lookupFactor]; omega)
    (by dsimp [lookupFactor]; omega)).mono _ le_rfl le_rfl
  dsimp [lookupFactor]
  omega

private theorem cell_le_stripe {K : Type} (f : K → Tree) (s : Series K) (k : K) :
    (f k).count ≤ (stripe s f).count := by
  rw [stripe_simple]
  exact count_le_forest f (s.complete k)

private theorem small_inputs {K L : Type} (tab : List (Tree × Tree)) (a : Series K) (b : Series L)
    (p : K → Tree) (q : L → Tree) (h : (stripe a p, stripe b q) ∈ tab) :
    (∀ k, (p k).count ≤ lookupFactor tab) ∧ ∀ l, (q l).count ≤ lookupFactor tab := by
  have hp := le_limit Prod.fst h
  have hq := le_limit Prod.snd h
  change (stripe a p).count ≤ _ at hp
  change (stripe b q).count ≤ _ at hq
  constructor
  · intro k
    have := cell_le_stripe p a k
    dsimp [lookupFactor]
    omega
  · intro l
    have := cell_le_stripe q b l
    dsimp [lookupFactor]
    omega

/-- The literal table acts at each common address across separately stored rows. -/
def tableCommand {L : Type} [DecidableEq L] (rank : ℕ) (out : Series L) (tab : List (Tree × Tree)) : Cmd :=
  alignedCommand rank out (command tab)

theorem table_within {L : Type} [DecidableEq L] (rank : ℕ) (out : Series L) (tab : List (Tree × Tree)) :
    Within 4 (tableCommand rank out tab) :=
  aligned_within rank out (within (by decide) tab)

/-- One concrete command works for every record count. Only the literal bank
and the fixed finite layouts occur in its time and space coefficient. -/
theorem table_bounded {K L A : Type} [DecidableEq K] [DecidableEq L]
    (cols : Series K) (dst : Series L) (rows : Series A) (k : K)
    (v : A → K → Tree) (w : A → L → Tree) (tab : List (Tree × Tree))
    (ht : ∀ a, read tab (stripe cols (v a)) = stripe dst (w a) ∧
      (stripe cols (v a), stripe dst (w a)) ∈ tab)
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let D := alignedFactor cols.count dst.count (lookupFactor tab) * (rows.count + 1)
    BoundedFits env (tableCommand (cols.explore.idxOf k) dst tab)
      (pile 0 (stripe cols (fun j => stripe rows (fun a => v a j))) r)
      (pile 0 (stripe dst (fun j => stripe rows (fun a => w a j))) r) D (base + D) D := by
  have small a := small_inputs tab cols dst (v a) (w a) (ht a).2
  simpa only [Nat.mul_one, tableCommand] using aligned_linear cols dst rows k v w (command tab) (lookupFactor tab)
    1 le_rfl (fun a j => by simpa using (small a).1 j) (fun a j => by simpa using (small a).2 j)
    (fun a env r b h => by simpa only [Nat.mul_one] using raw_bounded tab _ _ (ht a).1 (ht a).2 env r b h)
    env r base hr

/-- An outer record pass and an inner payload pass use the same four registers. -/
def payloadCommand {L : Type} [DecidableEq L] (rank : ℕ) (out : Series L) (tab : List (Tree × Tree)) : Cmd :=
  alignedCommand rank out (tableCommand rank out tab)

theorem payload_within {L : Type} [DecidableEq L] (rank : ℕ) (out : Series L) (tab : List (Tree × Tree)) :
    Within 4 (payloadCommand rank out tab) :=
  aligned_within rank out (table_within rank out tab)

def packedFactor (f o C : ℕ) : ℕ :=
  alignedFactor f o (alignedFactor f o C + C + 2)

def payloadFactor (f o : ℕ) (tab : List (Tree × Tree)) : ℕ :=
  packedFactor f o (lookupFactor tab)

/-- The physical clock and space match record count times payload width. In
particular a zero record count never incurs a charge for absent payloads. -/
theorem packed_bounded {K L A : Type} {P : A → Type} [DecidableEq K] [DecidableEq L]
    (cols : Series K) (dst : Series L) (rows : Series A) (payload : (a : A) → Series (P a))
    (width : ℕ) (hw : ∀ a, (payload a).count ≤ width) (k : K)
    (v : (a : A) → P a → K → Tree) (w : (a : A) → P a → L → Tree) (op : Cmd) (C : ℕ)
    (hv : ∀ a j z, (v a j z).count ≤ C) (hout : ∀ a j z, (w a j z).count ≤ C)
    (hc : ∀ a j env r base, DeckCap base r → BoundedFits env op
      (pile 0 (stripe cols (v a j)) r) (pile 0 (stripe dst (w a j)) r) C (base + C) C)
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let D := packedFactor cols.count dst.count C * (rows.count * (width + 1) + 1)
    BoundedFits env (alignedCommand (cols.explore.idxOf k) dst (alignedCommand (cols.explore.idxOf k) dst op))
      (pile 0 (stripe cols (fun z => stripe rows fun a => stripe (payload a) (fun j => v a j z))) r)
      (pile 0 (stripe dst (fun z => stripe rows fun a => stripe (payload a) (fun j => w a j z))) r)
      D (base + D) D := by
  let G := alignedFactor cols.count dst.count C
  let F := G + C + 2
  have size {a : A} (f : P a → Tree) (hf : ∀ j, (f j).count ≤ C) :
      (stripe (payload a) f).count ≤ F * (width + 1) := by
    apply (stripe_size (payload a) f C hf).trans
    have := Nat.mul_le_mul_right (C + 1) (hw a)
    dsimp only [F]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one] at *
    nlinarith
  apply aligned_linear cols dst rows k _ _ (alignedCommand (cols.explore.idxOf k) dst op)
    F (width + 1) (by omega)
  · exact fun a j => size _ (fun u => hv a u j)
  · exact fun a j => size _ (fun u => hout a u j)
  · intro a e d b hd
    have h := aligned_linear cols dst (payload a) k (v a) (w a) op C 1 le_rfl
      (fun j z => by simpa using hv a j z) (fun j z => by simpa using hout a j z)
      (fun j e' d' b' h' => by simpa only [Nat.mul_one] using hc a j e' d' b' h') e d b hd
    dsimp only at h
    simp only [Nat.mul_one] at h
    have le : G * ((payload a).count + 1) ≤ F * (width + 1) :=
      Nat.mul_le_mul (by dsimp only [F]; omega) (by have := hw a; omega)
    exact h.mono le (Nat.add_le_add_left le _) le
  · exact hr

theorem payload_bounded {K L A : Type} {P : A → Type} [DecidableEq K] [DecidableEq L]
    (cols : Series K) (dst : Series L) (rows : Series A) (payload : (a : A) → Series (P a))
    (width : ℕ) (hw : ∀ a, (payload a).count ≤ width) (k : K)
    (v : (a : A) → P a → K → Tree) (w : (a : A) → P a → L → Tree) (tab : List (Tree × Tree))
    (ht : ∀ a j, read tab (stripe cols (v a j)) = stripe dst (w a j) ∧
      (stripe cols (v a j), stripe dst (w a j)) ∈ tab)
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let D := payloadFactor cols.count dst.count tab * (rows.count * (width + 1) + 1)
    BoundedFits env (payloadCommand (cols.explore.idxOf k) dst tab)
      (pile 0 (stripe cols (fun z => stripe rows fun a => stripe (payload a) (fun j => v a j z))) r)
      (pile 0 (stripe dst (fun z => stripe rows fun a => stripe (payload a) (fun j => w a j z))) r)
      D (base + D) D := by
  have small a j := small_inputs tab cols dst (v a j) (w a j) (ht a j).2
  exact packed_bounded cols dst rows payload width hw k v w (command tab) (lookupFactor tab)
    (fun a j => (small a j).1) (fun a j => (small a j).2)
    (fun a j => raw_bounded tab _ _ (ht a j).1 (ht a j).2) env r base hr

/-- The bounded-register form of the packed spectral or linear table
operation, with a concrete table compiled from its finite alphabet. -/
theorem interchange_payload_table_checked {A B I K L : Type} [DecidableEq K] [DecidableEq L]
    {P : I → Type} {D : (i : I) → P i → Type}
    (records : (i : I) → Series (P i)) (payload : (i : I) → (j : P i) → Series (D i j))
    (width : I → ℕ) (hwidth : ∀ i j, (payload i j).count ≤ width i)
    (srcRows : Series K) (dstRows : Series L) (k : K)
    (v : (i : I) → K → (j : P i) → D i j → A)
    (src : A → Tree) (dst : B → Tree) (hs : Function.Injective src)
    (table : (K → A) → L → B) (alphabet : List A) (fallback : A) (all : ∀ a, a ∈ alphabet) :
    let volume i := (records i).count * (width i + 1)
    RegisterWitness.Bounded 4 volume volume
      (fun i => stripe srcRows fun z => stripe (records i) fun j => stripe (payload i j) fun a => src (v i z j a))
      (fun i => stripe dstRows fun z => stripe (records i) fun j => stripe (payload i j) fun a =>
        dst (table (fun k => v i k j a) z)) := by
  let tab := InterchangeROMTable.bank alphabet fallback srcRows dstRows src dst table
  refine ⟨payloadCommand (srcRows.explore.idxOf k) dstRows tab, payload_within ..,
    payloadFactor srcRows.count dstRows.count tab, fun i env r base hr => ?_⟩
  exact payload_bounded srcRows dstRows (records i) (payload i) (width i) (hwidth i) k _ _ tab
    (fun j a => InterchangeROMTable.bank_correct alphabet fallback srcRows dstRows src dst table
      (fun z => v i z j a) hs all) env r base hr

/-- A physical template lane stores the payload delimiters of a nullary gate. -/
abbrev templateLane : Series Unit := Series.one

def constantTable {L : Type} (out : Series L) (value : L → Tree) : List (Tree × Tree) :=
  [(stripe templateLane (fun _ => .atom false), stripe out value)]

/-- The shape lane permits constant instructions even with zero logical input
fields. Its delimiters determine both the record count and each payload length. -/
theorem constant_payload_bounded {L A : Type} {P : A → Type} [DecidableEq L]
    (out : Series L) (value : L → Tree) (rows : Series A) (payload : (a : A) → Series (P a))
    (width : ℕ) (hw : ∀ a, (payload a).count ≤ width) (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let tab := constantTable out value
    let D := payloadFactor 1 out.count tab * (rows.count * (width + 1) + 1)
    BoundedFits env (payloadCommand 0 out tab)
      (pile 0 (stripe templateLane (fun _ => stripe rows fun a => stripe (payload a) fun _ => .atom false)) r)
      (pile 0 (stripe out (fun o => stripe rows fun a => stripe (payload a) fun _ => value o)) r)
      D (base + D) D := by
  apply payload_bounded templateLane out rows payload width hw () (fun _ _ _ => .atom false)
    (fun _ _ => value) (constantTable out value) _ env r base hr
  intro a j
  simp [constantTable, RegisterLookup.read]

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
