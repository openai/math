import OAI.Computability.MultitapeWeakETH.WitnessPushCodes

/-! # Ordered coefficient labels of the factor expansion at a site -/

namespace OAI.Computability.MultitapeWeakETH.WitnessWalk

open IntegerMultiplication Code VPVNP NetworkKernel CompressorRecords PairSimulation LocalHistory
open scoped Classical
noncomputable section

variable {D L R : Type} [Fintype L] [CommRing R] {f : L → R} {N : Network} {hist : ℕ}
  (order : L ≃ Fin hist) (visit : Visit D) (ctx : D)

abbrev SiteJobs (N : Network) := ∀ u, N.Half u → Job

/-- The accepted private words are the canonical codes of the site factors,
with one ordered list of finite labels realizing each exponent vector. -/
def SiteSpec (P : SiteParsers f N) (job : SiteJobs N) : Prop :=
  ∀ u h, ∃ names : (P.witnesses u h).Choice → List (Fin hist),
    (∀ x l, (names x).count (order l) = (P.witnesses u h).exponents x l) ∧
    Reads visit ctx [job u h] (P.read u h).encode (fun x => (names x).map (tally ∘ Fin.val))

def NodeSpec {t : Term R N} (r : TermParsers f t) (before : SiteJobs N) (after : SiteJobs t.output) : Prop :=
  ∀ u new, ∃ names : ∀ old, (r.witness u old new).Choice → List (Fin hist),
    (∀ old x l, (names old x).count (order l) = (r.witness u old new).exponents x l) ∧
    ∀ bits jobs tail labels, visit ((ctx,after u new),bits) = some ((jobs,tail),labels) ↔
      ∃ old x, jobs = children r before u old ∧ bits = r.nodeBits u old new x ++ tail ∧
        labels = (names old x).map (tally ∘ Fin.val)

private theorem count_flatten {A : Type} [BEq A] [LawfulBEq A] (ls : List (List A)) (a : A) :
    ls.flatten.count a = (ls.map (fun s => s.count a)).sum := by
  induction ls with
  | nil => rfl
  | cons _ _ ih => simp only [List.flatten_cons,List.count_append,ih,List.map_cons,List.sum_cons]

/-- Pushing factors through one term preserves the actual code and sums all
multiplicities from the local maps and independently chosen child monomials. -/
theorem SiteSpec.push {t : Term R N} (r : TermParsers f t) (P : SiteParsers f N)
    {before : SiteJobs N} {after : SiteJobs t.output} (sites : SiteSpec order visit ctx P before)
    (step : NodeSpec order visit ctx r before after) : SiteSpec order visit ctx (r.push P) after := by
  choose child ccount crun using sites
  intro v z
  obtain ⟨emit,ecount,erun⟩ := step v z
  let e := t.pushChoice P.factors P.witnesses r.witness v z
  let o := r.order.children v
  let kids (x : ((r.push P).witnesses v z).Choice) := List.ofFn fun j => let u := o.entries j
    child u.val ((e x).1 u.val u.prop) ((e x).2.1 u)
  let labels (x : ((r.push P).witnesses v z).Choice) := emit (e x).1 (e x).2.2 ++ (kids x).flatten
  refine ⟨labels,?_,?_⟩
  · intro x l
    simp only [labels,List.count_append,ecount,count_flatten,kids,List.map_ofFn,Function.comp_def,ccount,List.sum_ofFn]
    change _ + _ = (∑ u : t.Preimage v, (P.witnesses u.val ((e x).1 u.val u.prop)).exponents ((e x).2.1 u) l) + _
    rw [Nat.add_comm]
    exact congrArg (· + _) (o.entries.sum_comp (fun u => (P.witnesses u.val ((e x).1 u.val u.prop)).exponents ((e x).2.1 u) l))
  · have joined := reads_push r P before after (fun u h x => (child u h x).map (tally ∘ Fin.val))
      crun v z (fun a x => (emit a x).map (tally ∘ Fin.val)) erun
    intro bits tail out
    exact (joined bits tail out).trans (exists_congr fun x => and_congr_right fun _ => by
      simp only [labels,kids,List.map_append,List.map_flatten,List.map_ofFn,Function.comp_def,e,o])

end
end OAI.Computability.MultitapeWeakETH.WitnessWalk
