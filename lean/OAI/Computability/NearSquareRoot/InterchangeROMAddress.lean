import OAI.Computability.NearSquareRoot.InterchangePivotBatch
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect
import OAI.Computability.IntegerMultiplication.Code.Pace

/-!
# Compiling pivot descriptors from finite positional data

All radices, field positions and parent dimensions are inputs of the same
polynomial header program. A finite sequence of pivots changes only the
literal installed ahead of this program.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeBatch

abbrev Header := Tally × List Tally × List Tally × List Tally
abbrev Cuts := Tally × Tally × Tally × Tally
abbrev Spec := Tally × List Cuts

def metadata (b : ℕ) {J : Type} {n : ℕ} (ord : J ≃ Fin n) (pairs : List (J × J)) : Spec :=
  (tally b,pairs.map fun xy => (tally (ord xy.1).val, tally (n-(ord xy.1).val-1),
    tally (ord xy.2).val,tally (n-(ord xy.2).val-1)))

def header (f : ℕ) (p g s : Tape) : Header := (tally f,shape p,shape g,shape s)

def copies (t : Tally × List Tally) : List Tally := (t.1.map fun _ => t.2).flatten

theorem copies_poly : Poly copies := Packed.chamber.compose Easy.flatten.poly

def one (spec : (Tally × Header) × Cuts) : Header :=
  let radix := spec.1.1
  let h := spec.1.2
  let word := h.1.map (fun _ => radix)
  let c := spec.2
  (h.1, h.2.1 ++ copies (c.1,word),
    copies (c.2.1,word) ++ (h.2.2.1 ++ copies (c.2.2.1,word)),
    copies (c.2.2.2,word) ++ h.2.2.2)

theorem one_poly : Poly one := by
  let w (s : (Tally × Header) × Cuts) := s.1.2.1.map (fun _ => s.1.1)
  have word : Poly w :=
    (show Poly (fun s : (Tally × Header) × Cuts => (s.1.2.1,s.1.1)) from by fun_prop).compose
      Packed.chamber
  have cat := (Easy.append (X:=Tally)).poly
  change Poly (fun s : (Tally × Header) × Cuts =>
    (s.1.2.1,s.1.2.2.1 ++ copies (s.2.1,w s),
      copies (s.2.2.1,w s) ++ (s.1.2.2.2.1 ++ copies (s.2.2.2.1,w s)),
      copies (s.2.2.2.2,w s) ++ s.1.2.2.2.2))
  apply Poly.pair (by fun_prop)
  apply Poly.pair (((by fun_prop : Poly (fun s : (Tally × Header) × Cuts => s.1.2.2.1)).pair
      (((by fun_prop : Poly (fun s : (Tally × Header) × Cuts => s.2.1)).pair word).compose copies_poly)).compose cat)
  apply Poly.pair
  · exact ((((by fun_prop : Poly (fun s : (Tally × Header) × Cuts => s.2.2.1)).pair word).compose
      copies_poly).pair (((by fun_prop : Poly (fun s : (Tally × Header) × Cuts => s.1.2.2.2.1)).pair
      (((by fun_prop : Poly (fun s : (Tally × Header) × Cuts => s.2.2.2.1)).pair word).compose copies_poly)).compose cat)).compose cat
  · exact ((((by fun_prop : Poly (fun s : (Tally × Header) × Cuts => s.2.2.2.2)).pair word).compose copies_poly).pair
      (by fun_prop : Poly (fun s : (Tally × Header) × Cuts => s.1.2.2.2.2))).compose cat

def plan (p : Spec × Header) : List Header :=
  p.1.2.map (fun cuts => one ((p.1.1,p.2),cuts))

theorem plan_poly : Poly plan :=
  (show Poly (fun p : Spec × Header => ((p.1.1,p.2),p.1.2)) from by fun_prop).compose
    (Poly.push default default one_poly)

theorem shape_field (b f : ℕ) :
    (tally f).map (fun _ => tally b) = shape (field b f) := by
  induction f with
  | zero => rfl
  | succ f ih => simpa only [field,shape_cons,tally,List.replicate_succ,List.map_cons,List.cons.injEq,
      true_and] using ih

theorem copy_shape (k : ℕ) (s : Tape) : copies (tally k,shape s) = shape (Rack s k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((tally (k+1)).map (fun _ => shape s)).flatten = _
    rw [show tally (k+1) = () :: tally k by simp [tally,List.replicate_succ]]
    simp only [List.map_cons,List.flatten_cons]
    rw [show ((tally k).map (fun _ => shape s)).flatten = _ from ih]
    simp [Loom.Rack,shape]

theorem one_header {J : Type} {n : ℕ} (ord : J ≃ Fin n) (p g s : Tape) (b f : ℕ) (x y : J) :
    one ((tally b,header f p g s),tally (ord x).val,tally (n-(ord x).val-1),
      tally (ord y).val,tally (n-(ord y).val-1)) =
    header f (preamble ord p g (field b f) (false,x))
      (silence ord g (field b f) (false,x) (true,y)) (appendix ord g s (field b f) (true,y)) := by
  simp only [one, header, shape_field, copy_shape, preamble_false, silence_false_true, appendix_true,
    leftF, rightF, ranking]
  simp [shape]

variable {I J : Type} [DecidableEq J] {b n : ℕ} [NeZero b]
  (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f l : I → ℕ)

/-- For a fixed finite pivot program, the actual header generator, the exact
list of calls, and the stream equalities used by the physical batch command.
Each record in every call is one of the original records. -/
theorem pivot_schedule (good : I → Tree → Prop) (pairs : List (J × J))
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree)
    (hgood : ∀ i k, good i (v i k)) :
    ∃ uses : I → List (Request b),
      (∀ i, (uses i).length = pairs.length) ∧
      (∀ i a, a ∈ uses i → (allowed f (countRows (b:=b) ord P G B f) l i a ∧
        ∀ k, good i (a.contents k)) ∧ inherited b (P i) (G i) (B i) a) ∧
      (∀ i, send (plan (metadata b ord pairs,header (f i) (P i) (G i) (B i))) =
        headers Request.header (uses i)) ∧
      ∀ i, Chain Request.payload (Request.job b).reply (stripe (layoutRows ord P G B f i) (v i))
        (uses i) (stripe (layoutRows ord P G B f i) (v i ∘
          (recreation ord (P i) (G i) (B i) (f i) (pivotOps b pairs)
            (pivotOps_legal ord b pairs)).symm)) := by
  induction pairs generalizing v with
  | nil =>
    refine ⟨fun _ => [], fun _ => rfl, by simp, fun _ => rfl, fun i => .nil _⟩
  | cons pair pairs ih =>
    obtain ⟨x,y⟩ := pair
    let D i := field b (f i)
    let L i := preamble ord (P i) (G i) (D i) (false,x)
    let M i := silence ord (G i) (D i) (false,x) (true,y)
    let S i := appendix ord (G i) (B i) (D i) (true,y)
    let ax (i : I) := twoStops ord (false,x) (true,y) (Or.inl ⟨rfl,rfl⟩)
      (p:=b) (j:=f i) (P:=P i) (G:=G i) (B:=B i)
    let child (i : I) : Request b := ⟨L i, M i, S i, f i, l i, v i ∘ (ax i).view.cast.symm⟩
    let after (i : I) := v i ∘ (reflect ord (.pivot x y) trivial (P i) (G i) (B i) (f i)).symm
    obtain ⟨rest,card,valid,tags,linked⟩ := ih after (fun i _ => hgood i _)
    refine ⟨fun i => child i :: rest i, fun i => congrArg Nat.succ (card i), ?_,
      ?_, ?_⟩
    · intro i a ha
      rcases List.mem_cons.mp ha with rfl | later
      · refine ⟨⟨⟨rfl, (ax i).view.cost.symm, rfl⟩, fun k => hgood i _⟩, ?_⟩
        intro k hk
        change k ∈ (L i ++ M i) ++ S i at hk
        simp only [L,M,S,preamble_false,silence_false_true,appendix_true,List.mem_append] at hk
        simp only [List.mem_append]
        rcases hk with (((hp | h₁) | h₂ | hg | h₃) | h₄ | hs)
        · exact .inr (.inl (.inl hp))
        · exact .inl (source_radix k _ b _ h₁)
        · exact .inl (source_radix k _ b _ h₂)
        · exact .inr (.inl (.inr hg))
        · exact .inl (source_radix k _ b _ h₃)
        · exact .inl (source_radix k _ b _ h₄)
        · exact .inr (.inr hs)
      · exact valid i a later
    · intro i
      change Tree.fork _ (send (plan (metadata b ord pairs,header (f i) (P i) (G i) (B i)))) =
        Tree.fork (child i).header (headers Request.header (rest i))
      rw [tags i]
      exact congrArg (fun h => Tree.fork (send h) (headers Request.header (rest i)))
        (one_header ord (P i) (G i) (B i) b (f i) x y)
    · intro i
      have pre : Request.payload (child i) = stripe (layoutRows ord P G B f i) (v i) := by
        unfold Request.payload
        rw [(ax i).view.packet]
        exact congrArg (stripe _) (funext fun k => congrArg (v i) ((ax i).view.cast.symm_apply_apply k))
      have post : (Request.job b).reply (child i) = stripe (layoutRows ord P G B f i) (after i) := by
        unfold Request.job
        dsimp only
        rw [(ax i).view.packet]
        rfl
      rw [← pre]
      apply Chain.cons
      rw [post]
      exact linked i

end InterchangeROMAddress

end NearSquareRoot
end Computability
end OAI
