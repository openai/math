import OAI.Computability.VPVNP.PrimedCounterBits
import OAI.Computability.VPVNP.PairCoefficient

/-!
# The multiplicity of accepting binary preorder traces

For each assignment of the internal primed bits, each site supplies one binary
choice list for every node call. Marking repeated positions and comparing the
sum of the emitted histograms with the nomination gives the integer coefficient
of the primed pair polynomial.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter

open ParseGrammar
open scoped Classical

variable {n m s w : ℕ} {Site Internal : Type*}

private theorem marked_iff (x : Fin m → Bool) (d : Fin n) (h : Fin s)
    (ts : List (Token m (Fin s))) :
    (scan x [(d,h)] ts).isSome ∧ (positions ts).Nodup ↔ (checkedTree x d.val ts).isSome := by
  have he := congrArg Option.isSome (scan_marked x d h ts)
  by_cases hn : (positions ts).Nodup <;> simpa [hn] using Bool.eq_iff_iff.mp he

/-- Branch tapes accepted by one parse's stack and mark checks. -/
abbrev SitePaths (w : ℕ) (x : Fin m → Bool) (d : Fin n) (h : Fin s) :=
  {bs : List (List Bool) // ∃ ts, decodeVisits w x [(d,h)] bs = some ts ∧ (positions ts).Nodup}

/-- Recover the node selections from the consumed binary branches. -/
def chosenTokens (x : Fin m → Bool) (d : Fin n) (h : Fin s) (b : SitePaths w x d h) :
    List (Token m (Fin s)) :=
  (decodeVisits w x [(d,h)] b.val).get (by
    obtain ⟨ts, he, _⟩ := b.property
    simp [he])

theorem chosenTokens_spec (x : Fin m → Bool) (d : Fin n) (h : Fin s) (b : SitePaths w x d h) :
    decodeVisits w x [(d,h)] b.val = some (chosenTokens x d h b) ∧ (positions (chosenTokens x d h b)).Nodup := by
  have he : decodeVisits w x [(d,h)] b.val = some (chosenTokens x d h b) := (Option.some_get _).symm
  refine ⟨he, ?_⟩
  obtain ⟨ts, hr, hn⟩ := b.property
  rwa [Option.some.inj (he.symm.trans hr)]

/-- Fixed-width branching preserves the exact multiplicity of token streams. -/
def bitTraceEquiv (hm : m ≤ 2^w) (hs : s ≤ 2^w) (hn : n ≤ 2^w)
    (x : Fin m → Bool) (d : Fin n) (h : Fin s) :
    SitePaths w x d h ≃ {ts : List (Token m (Fin s)) // (checkedTree x d.val ts).isSome} where
  toFun b := ⟨chosenTokens x d h b, by
    obtain ⟨hd, hm'⟩ := chosenTokens_spec x d h b
    exact (marked_iff x d h _).1 ⟨(decodeVisits_sound hm hs hn _ _ _ _ hd).2, hm'⟩⟩
  invFun t := ⟨t.val.map (encodeToken w), by
    obtain ⟨hsc, hm'⟩ := (marked_iff x d h _).2 t.property
    exact ⟨t.val, decodeVisits_encode hm hs hn _ _ _ hsc, hm'⟩⟩
  left_inv b := Subtype.ext (decodeVisits_sound hm hs hn _ _ _ _ (chosenTokens_spec x d h b).1).1.symm
  right_inv t := by
    apply Subtype.ext
    have hh := decodeVisits_encode hm hs hn _ _ _ ((marked_iff x d h _).2 t.property).1
    exact Option.some.inj ((Option.some_get _).trans hh)

/-- Complete local parsimony, including malformed code rejection and the
unique leaf bijection recovered from the position marks. -/
noncomputable def siteEquiv (hm : m ≤ 2^w) (hs : s ≤ 2^w) (hn : n ≤ 2^w)
    (x : Fin m → Bool) (d : Fin n) (h : Fin s) (hsize : d.val + 1 = m) :
    SitePaths w x d h ≃ ParseChoice (Fin s) d x :=
  (bitTraceEquiv hm hs hn x d h).trans (choiceEquiv d hsize x)

/-- Counter values emitted by this path's actual sequence of stack updates. -/
noncomputable def siteHistogram (hm : m ≤ 2^w) (hs : s ≤ 2^w) (hn : n ≤ 2^w)
    (x : Fin m → Bool) (d : Fin n) (h : Fin s) (b : SitePaths w x d h) : Label n m (Fin s) →₀ ℕ :=
  tally ((scan x [(d,h)] (chosenTokens x d h b)).get
    (decodeVisits_sound hm hs hn _ _ _ _ (chosenTokens_spec x d h b).1).2)

theorem siteHistogram_eq (hm : m ≤ 2^w) (hs : s ≤ 2^w) (hn : n ≤ 2^w)
    (x : Fin m → Bool) (d : Fin n) (h : Fin s) (hsize : d.val + 1 = m) (b : SitePaths w x d h) :
    siteHistogram hm hs hn x d h b = histogram d h (siteEquiv hm hs hn x d h hsize b).1 := by
  let ts := chosenTokens x d h b
  have hm' : (positions ts).Nodup := (chosenTokens_spec x d h b).2
  have hsc : (scan x [(d,h)] ts).isSome := (decodeVisits_sound hm hs hn _ _ _ _ (chosenTokens_spec x d h b).1).2
  have ht := (marked_iff x d h ts).1 ⟨hsc, hm'⟩
  have he := scan_marked x d h ts
  simp only [hm', ↓reduceIte] at he
  rw [← Option.some_get hsc, ← Option.some_get ht] at he
  exact Option.some.inj he

/-- One shared internal assignment followed by one complete branch path per site. -/
abbrev PairPaths (w : ℕ) (d : Fin n) (h : Fin s) (input : Internal → Site → Fin m → Bool) :=
  (a : Internal) × ((v : Site) → SitePaths w (input a v) d h)

/-- Identify an internal assignment and one accepted binary preorder path at each site with the
parse choices defining the pair coefficient. -/
noncomputable def pairEquiv (hm : m ≤ 2^w) (hs : s ≤ 2^w) (hn : n ≤ 2^w)
    (d : Fin n) (h : Fin s) (hsize : d.val + 1 = m) (input : Internal → Site → Fin m → Bool) :
    PairPaths w d h input ≃ PairCoefficient.Choices (Fin s) d input :=
  Equiv.sigmaCongrRight fun a => Equiv.piCongrRight fun v => siteEquiv hm hs hn (input a v) d h hsize

/-- Counts accumulated in the shared histogram across both primed groups. -/
noncomputable def totalHistogram [Fintype Site] (hm : m ≤ 2^w) (hs : s ≤ 2^w) (hn : n ≤ 2^w)
    (d : Fin n) (h : Fin s) (input : Internal → Site → Fin m → Bool) (b : PairPaths w d h input) :
    Label n m (Fin s) →₀ ℕ := ∑ v, siteHistogram hm hs hn (input b.1 v) d h (b.2 v)

theorem totalHistogram_eq [Fintype Site] (hm : m ≤ 2^w) (hs : s ≤ 2^w) (hn : n ≤ 2^w)
    (d : Fin n) (h : Fin s) (hsize : d.val + 1 = m) (input : Internal → Site → Fin m → Bool)
    (b : PairPaths w d h input) :
    totalHistogram hm hs hn d h input b = PairCoefficient.jointHistogram d h input (pairEquiv hm hs hn d h hsize input b) := by
  apply Finset.sum_congr rfl
  intro v _
  exact siteHistogram_eq hm hs hn _ _ _ hsize _

/-- The number of branch tapes surviving the histogram comparison is precisely
the coefficient of (9.4), including when no tape is accepted. -/
theorem pairPath_count [Fintype Site] [Fintype Internal]
    (hm : m ≤ 2^w) (hs : s ≤ 2^w) (hn : n ≤ 2^w) (d : Fin n) (h : Fin s)
    (hsize : d.val + 1 = m) (input : Internal → Site → Fin m → Bool) (μ : Label n m (Fin s) →₀ ℕ) :
    (Nat.card {b : PairPaths w d h input // totalHistogram hm hs hn d h input b = μ} : ℤ) =
      (PairCoefficient.jointPolynomial d h input).coeff μ := by
  rw [PairCoefficient.coeff_eq_count, ← Nat.card_eq_fintype_card]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquiv (pairEquiv hm hs hn d h hsize input) fun b =>
    by rw [totalHistogram_eq hm hs hn d h hsize input b])

end PrimedCounter

end VPVNP
end Computability
end OAI
