import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic

/-!
# Consecutive private strings and public deliveries in Proposition 7.2

The public directory lists the initial sites of each bottom bundle in row-major order.
A string's offset is the sum of preceding string lengths. The consecutive processor tails
supply the storage, and the directory addresses every destination once, independently of the
strings' contents.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

/-- Every index in an interval of length at most one block lies in its first or second block. -/
theorem interval_two_blocks (start len block : ℕ) (hlen : len ≤ block) (i : Fin len) :
    (start + i) / block = start / block ∨ (start + i) / block = start / block + 1 := by
  have hlo := Nat.div_le_div_right (c := block) (Nat.le_add_right start i)
  have hhi : (start + i) / block ≤ start / block + 1 := by
    rw [← Nat.add_div_right start (Nat.zero_lt_of_lt (i.isLt.trans_le hlen))]
    exact Nat.div_le_div_right (Nat.add_le_add_left (i.isLt.le.trans hlen) start)
  omega

/-- If two variable-width fields meet a half-open site block, at most one boundary separates
them when each field is at least the width of that site block. -/
theorem intersected_fields_adjacent (boundary : ℕ → ℕ) (ordered : Monotone boundary)
    (start width i j : ℕ) (wide : ∀ k, boundary k + width ≤ boundary (k + 1))
    (leftHit : start < boundary (i + 1)) (rightHit : boundary j < start + width) :
    j ≤ i + 1 := by
  by_contra! h
  have := (wide (i + 1)).trans (ordered (show i + 1 + 1 ≤ j by omega))
  omega

/-- The processor and position within its reserved tail for every bit in the public directory.
The capacity inequality is exactly the one for concatenating all the site strings. -/
def tailAddress {entries processors tail : ℕ} (width : Fin entries → ℕ)
    (fits : ∑ j, width j ≤ processors * tail) :
    ((j : Fin entries) × Fin (width j)) ↪ Fin processors × Fin tail :=
  (finSigmaFinEquiv.toEmbedding.trans (Fin.castLEEmb fits)).trans finProdFinEquiv.symm.toEmbedding

/-- Concatenation places a bit at its string's prefix offset plus its local position. -/
theorem tailAddress_linear {entries processors tail : ℕ} (width : Fin entries → ℕ)
    (fits : ∑ j, width j ≤ processors * tail) (j : Fin entries) (bit : Fin (width j)) :
    (finProdFinEquiv (tailAddress width fits ⟨j, bit⟩) : ℕ) =
      (∑ i : Fin j, width (Fin.castLE j.isLt.le i)) + bit := by
  change (finProdFinEquiv (finProdFinEquiv.symm _) : ℕ) = _
  rw [Equiv.apply_symm_apply]
  exact finSigmaFinEquiv_apply _

/-- The nonempty pieces of each short string come from at most two adjacent processor tails. -/
theorem private_string_two_tails {entries processors tail : ℕ} (width : Fin entries → ℕ)
    (fits : ∑ j, width j ≤ processors * tail) (j : Fin entries) (short : width j ≤ tail) :
    ∃ first : ℕ, ∀ bit : Fin (width j), ((tailAddress width fits ⟨j, bit⟩).1 : ℕ) = first ∨
      ((tailAddress width fits ⟨j, bit⟩).1 : ℕ) = first + 1 := by
  let start := ∑ i : Fin j, width (Fin.castLE j.isLt.le i)
  refine ⟨start / tail, fun bit ↦ ?_⟩
  change (finSigmaFinEquiv ⟨j, bit⟩ : ℕ) / tail = _ ∨ (finSigmaFinEquiv ⟨j, bit⟩ : ℕ) / tail = _
  simp only [finSigmaFinEquiv_apply]
  exact interval_two_blocks start _ tail short bit

/-- Fill occupied positions from the public directory and unused positions with zero. -/
def storeTails {entries processors tail : ℕ} (width : Fin entries → ℕ)
    (strings : (j : Fin entries) → Fin (width j) → Bool)
    (address : Fin processors × Fin tail) : Bool :=
  let flat := finProdFinEquiv address
  if h : flat.val < ∑ j, width j then
    let bit := finSigmaFinEquiv.symm ⟨flat.val, h⟩
    strings bit.1 bit.2
  else false

/-- Reading the assigned tail position recovers the original private bit. -/
theorem read_stored_bit {entries processors tail : ℕ} (width : Fin entries → ℕ)
    (fits : ∑ j, width j ≤ processors * tail)
    (strings : (j : Fin entries) → Fin (width j) → Bool) (bit : (j : Fin entries) × Fin (width j)) :
    storeTails width strings (tailAddress width fits bit) = strings bit.1 bit.2 := by
  have hflat : finProdFinEquiv (tailAddress width fits bit) = Fin.castLE fits (finSigmaFinEquiv bit) :=
    Equiv.apply_symm_apply finProdFinEquiv _
  unfold storeTails
  rw [hflat]
  simp only [Fin.val_castLE, Fin.is_lt, dite_true]
  exact congrArg (fun b : (j : Fin entries) × Fin (width j) ↦ strings b.1 b.2)
    (finSigmaFinEquiv.symm_apply_apply bit)

/-- Record of one public demand. Each bundle/site pair is numbered once regardless of how many
copies share its private string at the destination cell. -/
def privateDemand {bundles sites : ℕ} {Cell : Type*}
    (cell : Fin bundles × Fin sites → Cell) (j : Fin (bundles * sites)) :
    (Fin bundles × Fin sites) × Cell :=
  let key := finProdFinEquiv.symm j
  (key, cell key)

/-- The public order has exactly one record delivering the full private string of each bundle
and site to its assigned cell. All reads in that record return the intended bits. -/
theorem private_delivery_once {bundles sites processors tail : ℕ} {Cell : Type*}
    (cell : Fin bundles × Fin sites → Cell) (width : Fin (bundles * sites) → ℕ)
    (fits : ∑ j, width j ≤ processors * tail) (strings : ∀ j, Fin (width j) → Bool)
    (key : Fin bundles × Fin sites) :
    ∃! j : Fin (bundles * sites), privateDemand cell j = (key, cell key) ∧
      ∀ bit : Fin (width j), storeTails width strings (tailAddress width fits ⟨j, bit⟩) = strings j bit := by
  refine ⟨finProdFinEquiv key, ⟨by simp [privateDemand], fun bit ↦ read_stored_bit ..⟩, ?_⟩
  intro j hj
  exact finProdFinEquiv.symm.injective ((congrArg Prod.fst hj.1).trans
    (finProdFinEquiv.symm_apply_apply key).symm)

/-- A team's private deliveries originate at distinct processor/bit addresses in its reserved
tails. This gives the required per-team bound even for uneven string lengths. -/
theorem private_origins_per_team {entries teams processors tail : ℕ} (width : Fin entries → ℕ)
    (fits : ∑ j, width j ≤ teams * processors * tail) (team : Fin teams) :
    Fintype.card {bit : (j : Fin entries) × Fin (width j) //
      (finProdFinEquiv.symm ((tailAddress width fits bit).1)).1 = team} ≤ processors * tail := by
  let addr := tailAddress width fits
  let decode : Fin (teams * processors) × Fin tail ≃ (Fin teams × Fin processors) × Fin tail :=
    finProdFinEquiv.symm.prodCongr (Equiv.refl _)
  let e := addr.trans decode.toEmbedding
  let localAddr (bit : {bit : (j : Fin entries) × Fin (width j) //
      (finProdFinEquiv.symm ((tailAddress width fits bit).1)).1 = team}) : Fin processors × Fin tail :=
    ((e bit.val).1.2, (e bit.val).2)
  have inj : Function.Injective localAddr := by
    intro x y heq
    apply Subtype.ext
    apply e.injective
    have hl := congrArg (fun p : Fin processors × Fin tail ↦ p.1) heq
    have hr := congrArg (fun p : Fin processors × Fin tail ↦ p.2) heq
    exact Prod.ext (Prod.ext (x.property.trans y.property.symm) hl) hr
  simpa using Fintype.card_le_of_injective localAddr inj

/-- Adding the actual literal of every processor to the private requests costs at most twice
the total literal width of a team, as in Proposition 7.2(iii). -/
theorem private_and_literal_source_bound {entries teams processors tail literal : ℕ}
    (width : Fin entries → ℕ) (fits : ∑ j, width j ≤ teams * processors * tail)
    (tail_le : tail ≤ literal) (team : Fin teams) :
    Fintype.card {bit : (j : Fin entries) × Fin (width j) //
      (finProdFinEquiv.symm ((tailAddress width fits bit).1)).1 = team} +
        processors * literal ≤ 2 * (processors * literal) := by
  have h := (private_origins_per_team width fits team).trans (Nat.mul_le_mul_left processors tail_le)
  omega

end Packing

end BorderVNP
end Computability
end OAI
