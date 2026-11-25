import OAI.Computability.NearSquareRoot.CommonRegisters
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPack

/-! # Packed transition rows on a fixed register bank

The old tape order can omit unused register names. Compressing the fixed read
tuple into that order and expanding the command tuple in the opposite direction
retains every original transition. Each omitted head preserves its symbol.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Padding

open IntegerMultiplication CommonAlphabet

def extract (b : ℕ) (positions : List ℕ) (reads : ℕ) : ℕ :=
  Numbering.encodeBase b (positions.map (Numbering.digit b reads))

def one (b : ℕ) (positions : List ℕ) (reads acts j : ℕ) : ℕ :=
  let k := positions.idxOf j
  if k < positions.length then Numbering.digit (b*3) acts k
  else 1 + 3 * Numbering.digit b reads j

def expand (b total : ℕ) (positions : List ℕ) (reads acts : ℕ) : ℕ :=
  Numbering.encodeBase (b*3) ((List.range total).map (one b positions reads acts))

def row (b total : ℕ) (positions : List ℕ) (orig : ℕ × ℕ → Option (ℕ × ℕ))
    (p : ℕ × ℕ) : Option (ℕ × ℕ) :=
  (orig (p.1, extract b positions p.2)).map (fun z => (z.1, expand b total positions p.2 z.2))

def positions (sites : List Site) : List ℕ := 0 :: (Pack.stackNames sites).map Nat.succ

def fixed (R : ℕ) : Numbering (Option (Option (Fin R))) := (Numbering.fin R).option.option

@[simp] theorem fixed_size (R : ℕ) : (fixed R).size = R+2 := rfl

variable {X Q I J : Type}
variable (x : Numbering X) (q : Numbering Q) (i : Numbering I) (j : Numbering J) (e : I ↪ J)

private def coordinates : List ℕ := i.all.map fun u => (j.equiv (e u)).val

private theorem coordinates_mem (v : J) :
    (j.equiv v).val ∈ coordinates i j e ↔ ∃ u, e u = v := by
  simp [coordinates, Fin.val_injective.eq_iff, (j.equiv.injective).eq_iff, i.mem_all]

private theorem coordinates_idx (u : I) :
    (coordinates i j e).idxOf (j.equiv (e u)).val = (i.equiv u).val := by
  let f (k : Fin i.size) := (j.equiv (e (i.equiv.symm k))).val
  have hf : Function.Injective f :=
    Fin.val_injective.comp (j.equiv.injective.comp (e.injective.comp i.equiv.symm.injective))
  have c : coordinates i j e = (List.finRange i.size).map f := by
    simp only [coordinates, Numbering.all, List.map_map]; rfl
  rw [c]
  have eqn : (j.equiv (e u)).val = f (i.equiv u) := by simp [f]
  rw [eqn]
  have hd := (List.nodup_finRange i.size).map hf
  have hlt : (i.equiv u).val < ((List.finRange i.size).map f).length := by simp
  have h := hd.idxOf_getElem (i.equiv u).val hlt
  simpa using h

private theorem extract_eq (r : J → X) :
    extract x.size (coordinates i j e) ((j.arrow x).equiv r).val =
      ((i.arrow x).equiv (r ∘ e)).val := by
  rw [← Numbering.encodeBase_arrow i x (r ∘ e)]
  unfold extract coordinates
  rw [List.map_map]
  apply congrArg (Numbering.encodeBase _)
  apply List.map_congr_left
  intro u _
  exact Numbering.digit_arrow j x r (e u)

private theorem one_eq (r : J → X) (op : I → X × TM.Move) (v : J) :
    one x.size (coordinates i j e) ((j.arrow x).equiv r).val
      ((i.arrow (x.prod Numbering.move)).equiv op).val (j.equiv v).val =
        ((x.prod Numbering.move).equiv (CommonTapes.extend e op (fun v => (r v,.stay)) v)).val := by
  by_cases h : ∃ u, e u = v
  · obtain ⟨u,rfl⟩ := h
    have hm := (coordinates_mem i j e (e u)).2 ⟨u,rfl⟩
    unfold one
    rw [ite_eq_left (List.idxOf_lt_length_of_mem hm), coordinates_idx, CommonTapes.extend_apply]
    exact Numbering.digit_arrow i (x.prod Numbering.move) op u
  · have hm := mt (coordinates_mem i j e v).1 h
    unfold one
    rw [ite_eq_right (mt List.idxOf_lt_length_iff.mp hm), Numbering.digit_arrow, CommonTapes.extend_off _ _ _ _ h]
    rfl

private theorem expand_eq (r : J → X) (op : I → X × TM.Move) :
    expand x.size j.size (coordinates i j e) ((j.arrow x).equiv r).val
      ((i.arrow (x.prod Numbering.move)).equiv op).val =
      ((j.arrow (x.prod Numbering.move)).equiv
        (CommonTapes.extend e op (fun v => (r v, .stay)))).val := by
  rw [← Numbering.encodeBase_arrow j (x.prod Numbering.move) (CommonTapes.extend e op (fun v => (r v,.stay)))]
  unfold expand
  rw [← List.map_coe_finRange_eq_range (n := j.size), Numbering.all, List.map_map, List.map_map]
  apply congrArg (Numbering.encodeBase _)
  apply List.map_congr_left
  intro k _
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using one_eq x i j e r op (j.equiv.symm k)

/-- A numerical row on an arbitrary larger tape bank with given tape numberings. -/
theorem row_eq (m : TM.Rule X Q I) (orig : ℕ × ℕ → Option (ℕ × ℕ))
    (source : ∀ s r, orig ((q.equiv s).val, ((i.arrow x).equiv r).val) =
      (m s r).map fun z => ((q.equiv z.1).val, ((i.arrow (x.prod Numbering.move)).equiv z.2).val))
    (s : Q) (r : J → X) :
    row x.size j.size (i.all.map fun u => (j.equiv (e u)).val) orig
      ((q.equiv s).val, ((j.arrow x).equiv r).val) =
      (CommonTapes.rule e m s r).map fun z =>
        ((q.equiv z.1).val, ((j.arrow (x.prod Numbering.move)).equiv z.2).val) := by
  change row _ _ (coordinates i j e) _ _ = _
  simp only [row, extract_eq, source, CommonTapes.rule, Option.map_map]
  cases m s (r ∘ e) with
  | none => rfl
  | some z =>
    exact congrArg some (congrArg (Prod.mk (q.equiv z.1).val) (expand_eq x i j e r z.2))

private theorem all_option {I : Type} (i : Numbering I) :
    i.option.all = none :: i.all.map some := by
  change (List.finRange (i.size+1)).map (fun k => ((finSuccEquiv i.size) k).map i.equiv.symm) = _
  rw [List.finRange_succ, List.map_cons, List.map_map]
  simp only [finSuccEquiv_zero, Option.map_none, List.cons.injEq, true_and]
  unfold Numbering.all
  rw [List.map_map]
  apply List.map_congr_left
  intro k _
  simp

open private stackNames_eq from OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPackOutput

variable {A : Type} [Fintype A] (a : Numbering A) {R : ℕ} (hR : 0 < R)
    {p : Prog A} (hp : CommonRegisters.Within R p)

theorem positions_eq :
    positions (Prog.sites [] p |>.map (site (Pack.letter a))) =
      (Pack.stacks (Prog.sites [] p)).option.all.map
        (fun u => ((fixed R).equiv (CommonRegisters.indexEmbedding hR hp u)).val) := by
  unfold positions
  rw [stackNames_eq, all_option, List.map_cons, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro u _
  cases u with
  | none =>
    exact (Generator.StackRows.option_some (Numbering.fin R).option none).trans
        (congrArg Nat.succ (Generator.StackRows.option_none (Numbering.fin R))) |>.symm
  | some v =>
    let z : Fin R := ⟨v.val,CommonRegisters.used_lt hR hp v.property⟩
    exact ((Generator.StackRows.option_some (Numbering.fin R).option (some z)).trans
        (congrArg Nat.succ (Generator.StackRows.option_some (Numbering.fin R) z))).symm

/-- The actual bounded-register embedding uses one fixed bank of `R+2` tapes
for every compiled program satisfying the same register bound. -/
theorem padded (x : Numbering X) (q : Numbering Q)
    (m : TM.Rule X Q (Option (Prog.Ix (Prog.sites [] p))))
    (orig : ℕ × ℕ → Option (ℕ × ℕ))
    (source : ∀ s r, orig ((q.equiv s).val, (((Pack.stacks (Prog.sites [] p)).option.arrow x).equiv r).val) =
      (m s r).map fun z => ((q.equiv z.1).val,
        (((Pack.stacks (Prog.sites [] p)).option.arrow (x.prod Numbering.move)).equiv z.2).val))
    (s : Q) (r : Option (Option (Fin R)) → X) :
    row x.size (R+2) (positions ((Prog.sites [] p).map (site (Pack.letter a)))) orig
      ((q.equiv s).val, (((fixed R).arrow x).equiv r).val) =
      (CommonTapes.rule (CommonRegisters.indexEmbedding hR hp) m s r).map fun z =>
        ((q.equiv z.1).val, (((fixed R).arrow (x.prod Numbering.move)).equiv z.2).val) := by
  rw [positions_eq a hR hp]
  exact row_eq x q _ (fixed R) _ m orig source s r

end GeneratorSyntax.Padding

end NearSquareRoot
end Computability
end OAI
