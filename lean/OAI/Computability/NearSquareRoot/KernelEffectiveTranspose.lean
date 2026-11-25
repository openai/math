import OAI.Computability.NearSquareRoot.ScheduleRegisterSelectBank
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyIterate

/-! # Repeated fixed commands for gathering and scattering a row bank

The input arity determines how often to prepend a row to the per-address
tuples. The output arity determines how often to split off one row. Both
iterations use a fixed state type, including at arity zero.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEffectiveTranspose

open IntegerMultiplication IntegerMultiplication.Code MixBankLayout

variable {X : Type} [Codec X] (d : X)

private abbrev Bank (α : Type) := List (List α)

open private tail_easy from OAI.Computability.NearSquareRoot.KernelPassMixBankLayout

def prepend (row : List X) (columns : Bank X) : Bank X :=
  (zipFair d [] (row,columns)).map fun p => p.1 :: p.2

def gatherInit (p : Tally × Bank X) : Bank X × Bank X :=
  (p.2.reverse,p.1.map fun _ => [])

def gatherStep (p : Bank X × Bank X) : Bank X × Bank X :=
  (p.1.tail,prepend d (p.1.headD []) p.2)

def collect (n : ℕ) (p : Tally × Bank X) : Bank X := ((gatherStep d)^[n] (gatherInit p)).2

theorem easy_gatherInit : Code.Easy (gatherInit (X := X)) :=
  (Easy.snd.compose Easy.reverse).pair (Easy.fst.compose (Easy.const ([] : List X)).mapping)

theorem easy_gatherStep : Code.Easy (gatherStep d) := by
  have add : Code.Easy (fun p : List X × Bank X => prepend d p.1 p.2) :=
    (easy_zip d []).compose Easy.cons.mapping
  exact (Easy.fst.compose tail_easy).pair
    (((Easy.fst.compose (Iter.leader [])).pair Easy.snd).compose add)

omit [Codec X] in
private theorem gather_iter (rows acc : Bank X) :
    (gatherStep d)^[rows.length] (rows, acc) = ([], rows.foldl (fun a r => prepend d r a) acc) := by
  induction rows generalizing acc with
  | nil => rfl
  | cons r rs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    exact ih (prepend d r acc)

omit [Codec X] in
private theorem align_fold (r : Tally) (s : Bank X) :
    align s.length d (r,s) = s.foldr (prepend d) (r.map fun _ => []) := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    change prepend d a (align s.length d (r,s)) = prepend d a _
    rw [ih]

omit [Codec X] in
theorem collect_exact (r : Tally) (rows : Bank X) :
    collect d rows.length (r,rows) = align rows.length d (r,rows) := by
  rw [collect,gatherInit]
  have e := gather_iter d rows.reverse (r.map fun _ => [])
  rw [List.length_reverse,List.foldl_reverse] at e
  change ((gatherStep d)^[rows.length] (rows.reverse,_)).2 = _
  rw [e,align_fold]

def scatterInit (columns : Bank X) : Bank X × Bank X := (columns,[])

def scatterStep (p : Bank X × Bank X) : Bank X × Bank X :=
  (p.1.map List.tail, (p.1.map (fun e => e.headD d)) :: p.2)

def scatterDone (p : Bank X × Bank X) : Bank X := p.2.reverse

def distribute (n : ℕ) (p : Bank X) : Bank X := scatterDone ((scatterStep d)^[n] (scatterInit p))

theorem easy_scatterInit : Code.Easy (scatterInit (X := X)) := Easy.identity.pair (Easy.const [])

theorem easy_scatterStep : Code.Easy (scatterStep d) :=
  (Easy.fst.compose tail_easy.mapping).pair
    (((Easy.fst.compose (Iter.leader d).mapping).pair Easy.snd).compose Easy.cons)

theorem easy_scatterDone : Code.Easy (scatterDone (X := X)) := Easy.snd.compose Easy.reverse

omit [Codec X] in
private theorem scatter_iter (n : ℕ) (columns acc : Bank X) :
    ((scatterStep d)^[n] (columns,acc)).2 = (scatter n d columns).reverse ++ acc := by
  induction n generalizing columns acc with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change ((scatterStep d)^[n] (columns.map List.tail,_)).2 = _
    rw [ih]
    simp [MixBankLayout.scatter]

omit [Codec X] in
theorem distribute_exact (n : ℕ) (columns : Bank X) : distribute d n columns = scatter n d columns := by
  simp [distribute,scatterInit,scatterDone,scatter_iter]

open KernelEffectiveFamily RegisterSelect Filter

theorem collect_family : ∀ᶠ R in atTop, Family R (collect d) := by
  filter_upwards [easy_eventually (easy_gatherInit (X := X)), easy_eventually (easy_gatherStep d),
    easy_eventually (Easy.snd : Code.Easy (@Prod.snd (Bank X) (Bank X)))] with R init step done
  exact ((Family.fixed init).comp (Family.iterate_fixed step)).comp (Family.fixed done)

theorem scatter_family : ∀ᶠ R in atTop, Family R (MixBankLayout.scatter · d ·) := by
  filter_upwards [easy_eventually (easy_scatterInit (X := X)), easy_eventually (easy_scatterStep d),
    easy_eventually (easy_scatterDone (X := X))] with R init step done
  have h : Family R (distribute d) :=
    ((Family.fixed init).comp (Family.iterate_fixed step)).comp (Family.fixed done)
  exact h.congr (distribute_exact d)

end KernelEffectiveTranspose

end NearSquareRoot
end Computability
end OAI
