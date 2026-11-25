import OAI.Computability.IntegerMultiplication.Strip.Rails
import OAI.Computability.IntegerMultiplication.Code.Static

/-!
# Pointwise finite tables on separately stored streams

The data algebra of the revised interchange may have odd characteristic. A
fixed table on its symbols can be compiled directly, including a dense
linear map on a fixed batch of independent rows. Stream length and contents
are inputs. The number of rows and the table determine the finite program.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication.Code IntegerMultiplication.Strip

private theorem forest_agree {X : Type} {f g : X → Tree} (l : List X)
    (h : Task.forest f l = Task.forest g l) : ∀ x ∈ l, f x = g x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [Task.forest_cons, Tree.fork.injEq] at h
    exact List.forall_mem_cons.mpr ⟨h.1, ih h.2⟩

private theorem stripe_symbols_injective {K A : Type} (rows : Series K)
    {symbol : A → Tree} (hs : Function.Injective symbol) :
    Function.Injective (fun x : K → A => stripe rows (symbol ∘ x)) := by
  intro a b h
  simp only [stripe_simple] at h
  exact funext fun k => hs (forest_agree rows.explore h k (rows.complete k))

/-- Scan one aligned record stream with a fixed finite table. -/
theorem interchange_record_table {F I : Type} [Finite F] {P : I → Type}
    (points : (i : I) → Series (P i)) (v : (i : I) → P i → F)
    (src dst : F → Tree) (hs : Function.Injective src) :
    Carries (fun i => ((points i).count : ℝ) + 1)
      (stackRun points fun i j => src (v i j)) (stackRun points fun i j => dst (v i j)) := by
  obtain ⟨U, hU⟩ := (Set.finite_range (fun x => (src x).count)).bddAbove
  obtain ⟨V, hV⟩ := (Set.finite_range (fun x => (dst x).count)).bddAbove
  have source (x : F) : (src x).count ≤ U := hU (Set.mem_range_self x)
  have target (x : F) : (dst x).count ≤ V := hV (Set.mem_range_self x)
  have h : Carries (fun _ : F => (1 : ℝ)) src dst := by
    refine Carries.cheap (fun _ => le_rfl) ⟨U, fun x => ?_⟩ _ ?_
    · simpa using (show ((src x).count : ℝ) ≤ U by exact_mod_cast source x)
    exact Task.restricted _ src dst U V source target (fun _ _ e => congrArg dst (hs e))
  have t := liftoff points (fun i j => src (v i j)) (fun i j => dst (v i j))
    (fun _ => 1) (h.slide (fun x : Sigma P => v x.1 x.2))
  simpa using t

/-- Apply any fixed table at each common address across arbitrary input rows.
The input and output layouts both consist of whole rows in series order.
Zipping, restoring row order, table evaluation and work-tape cleanup are
charged in the P192 command budget. -/
theorem interchange_aligned_table {A B I K L : Type} [Finite A] [Finite K] [Nonempty K]
    {P : I → Type} (points : (i : I) → Series (P i))
    (srcRows : Series K) (dstRows : Series L) (v : (i : I) → K → P i → A)
    (src : A → Tree) (dst : B → Tree) (hs : Function.Injective src)
    (table : (K → A) → L → B) :
    Carries (fun i => ((points i).count : ℝ) + 1)
      (fun i => stripe srcRows fun k => stripe (points i) fun j => src (v i k j))
      (fun i => stripe dstRows fun l => stripe (points i) fun j =>
        dst (table (fun k => v i k j) l)) := by
  let w (i : I) : ℝ := (points i).count + 1
  let p i := stripe srcRows fun k => stripe (points i) fun j => src (v i k j)
  have hp : Volume w p := by
    obtain ⟨U, hU⟩ := (Set.finite_range (fun x => (src x).count)).bddAbove
    refine ⟨(srcRows.count + 1) * (U + 2) + 1, fun i => ?_⟩
    have hrow k := stripe_size (points i) (fun j => src (v i k j)) U
      (fun _ => hU (Set.mem_range_self _))
    have hbatch := stripe_size srcRows _ _ hrow
    dsimp [p, w]
    exact_mod_cast (show (stripe srcRows (fun k => stripe (points i) (fun j => src (v i k j)))).count ≤
      ((srcRows.count + 1) * (U + 2) + 1) * ((points i).count + 1) by nlinarith)
  have base := Carries.idles (fun i => (by dsimp [w]; linarith [Nat.cast_nonneg (α := ℝ) (points i).count] : 1 ≤ w i)) hp
  let k := Classical.choice (inferInstance : Nonempty K)
  have blank := (finite_cell srcRows _ base k).chain
    (interchange_record_table points (fun i => v i k) src (fun _ => .atom false) hs)
  let x (i : I) (j : P i) (k : K) := v i k j
  have z := lay srcRows points (fun i k j => src (v i k j)) base blank
  have mapped := interchange_record_table points x
    (fun a : K → A => stripe srcRows (src ∘ a))
    (fun a : K → A => stripe dstRows (dst ∘ table a)) (stripe_symbols_injective srcRows hs)
  exact unlay dstRows points _ (z.chain mapped)

end NearSquareRoot
end Computability
end OAI
