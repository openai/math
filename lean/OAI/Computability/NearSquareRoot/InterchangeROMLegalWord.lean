import OAI.Computability.NearSquareRoot.InterchangeROMWordLedger
import OAI.Computability.NearSquareRoot.CRTControlledFlatSwaps
import OAI.Computability.NearSquareRoot.InterchangeCalls
import OAI.Computability.NearSquareRoot.InterchangeOpcodeTypes

/-! # Native interpretation and pivot price of a literal address word -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMSequence

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims IntegerMultiplication.Loom
  NearSquareRoot.InterchangeBatch NearSquareRoot.InterchangeSpace NearSquareRoot.InterchangeAddress

variable {b n : ℕ} [NeZero b] (ord : Fin n ≃ Fin n) (P G B : Tape) (f : ℕ)

abbrev Legal := {m : Lag (Fin n) b // m.legal (ranking ord)}
abbrev Key := Keys P G B (Fin n) (Block b f)

private noncomputable def advance (o : Legal (b:=b) ord) (e : Equiv.Perm (Key (b:=b) (n:=n) P G B f)) :=
  e.trans (reflect ord o.val o.property P G B f)

private theorem folded (l : List (Legal (b:=b) ord))
    (ok : ∀ m∈l.map Subtype.val, m.legal (ranking ord)) (e : Equiv.Perm (Key (b:=b) (n:=n) P G B f)) :
    l.foldl (fun s o => advance ord P G B f o s) e =
      e.trans (recreation ord P G B f (l.map Subtype.val) ok) := by
  induction l generalizing e with
  | nil => rfl
  | cons o os ih =>
    change List.foldl _ (advance ord P G B f o e) os = _
    rw [ih (fun _ h => ok _ (List.mem_cons_of_mem _ h))]
    rfl

private theorem length_flat {X Q : Type} (xs : List X) (q : X → List Q) (cost : X → ℕ)
    (h : ∀ z∈xs, (q z).length=cost z) :
    (xs.flatMap q).length=(xs.map cost).sum := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,h _ List.mem_cons_self,
      ih (fun t ht => h t (List.mem_cons_of_mem _ ht))]

private theorem map_events {U V Z : Type} (a : U → V → V) (v : V) (l : List U) (g : U → Z) :
    (trace a v l).map (fun z => g z.1) = l.map g := by
  simpa only [List.map_map,Function.comp_def] using congrArg (List.map g) (trace_code a v l)

private theorem peak_events {U Z : Type} (l : List U) (g : U → Z) (h : Z → ℕ) :
    childPeak (fun z => h (g z)) l = childPeak h (l.map g) := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    change max _ (childPeak _ l) = max _ (childPeak _ (l.map g))
    rw [ih]

/-- Each legal P192 instruction contributes its actual child list on the
intermediate permuted row. Concatenation pays each pivot exactly once and
produces the semantic pullback by the full native address permutation. -/
theorem run_legal (cmd : Opcode.Op → Cmd) (header : Tree)
    (ops : List (Lag (Fin n) b)) (leg : ∀ m∈ops, m.legal (ranking ord))
    (v : Key (b:=b) (n:=n) P G B f → Tree) (valid : Request b → Prop)
    (time space depth : Lag (Fin n) b → ℕ)
    (one : ∀ (m : Lag (Fin n) b) (hm : m.legal (ranking ord))
      (e : Equiv.Perm (Key (b:=b) (n:=n) P G B f)),
      ∃ qs : List (Request b), qs.length = m.prices ∧ (∀ q∈qs, valid q) ∧
      Step (Request.job b) (cmd (Opcode.encode m)) header
        (stripe (arrays ord (line b f) P G B) (v ∘ e.symm))
        (stripe (arrays ord (line b f) P G B) (v ∘ (e.trans (reflect ord m hm P G B f)).symm))
        qs (time m) (space m) (depth m)) :
    let rows := arrays ord (line b f) P G B
    let H := header.count
    ∃ qs : List (Request b), qs.length = (ops.map Lag.prices).sum ∧ (∀ q∈qs, valid q) ∧
      Step (Request.job b) (command cmd (ops.map Opcode.encode)) header
        (stripe rows v) (stripe rows (v ∘ (recreation ord P G B f ops leg).symm)) qs
        ((ops.map time).sum+(ops.length+1)*(110*(H+1)))
        (dataSpace (stripe rows v).count H (childPeak space ops)) (returnSpace H (childPeak depth ops)) := by
  intro rows H
  let l := ops.attachWith (fun m => m.legal (ranking ord)) leg
  have erase : l.map Subtype.val=ops := by simp [l]
  let act := advance (b:=b) ord P G B f
  let E := Equiv.Perm (Key (b:=b) (n:=n) P G B f)
  let start : E := Equiv.refl _
  let events := trace act start l
  let pos (z : Legal (b:=b) ord × E) := z.1.val
  let row (s : E) := stripe rows (v ∘ s.symm)
  have wire := trace_chain act row start l
  have ok : ∀ m∈l.map Subtype.val, m.legal (ranking ord) := by simpa only [erase] using leg
  have endEq : List.foldl (fun s o => act o s) start l = recreation ord P G B f ops leg := by
    have h := folded ord P G B f l ok start
    simpa only [erase, start,Equiv.refl_trans] using h
  have ordered (g : Lag (Fin n) b → ℕ) : events.map (fun z => g (pos z)) = ops.map g := by
    have u := map_events act start l (fun z => g z.val)
    rw [←erase,List.map_map]
    exact u
  have order : events.map (fun z => Opcode.encode (pos z))=ops.map Opcode.encode := by
    rw [←erase,List.map_map]
    exact map_events act start l (fun z => Opcode.encode z.val)
  have ids : events.map pos=ops := (map_events act start l Subtype.val).trans erase
  have atoms (z : Legal (b:=b) ord × E) := one z.1.val z.1.property z.2
  choose docket counts trusted runs using atoms
  refine ⟨events.flatMap docket,?_,?_,?_⟩
  · rw [length_flat events docket (fun z => (pos z).prices) (fun z _ => counts z),ordered]
  · intro q hq
    obtain ⟨z,_,hz⟩ := List.mem_flatMap.mp hq
    exact trusted z q hz
  · let input (z : Legal (b:=b) ord × E) := row z.2
    let output (z : Legal (b:=b) ord × E) := row (act z.1 z.2)
    have same (e : E) : (row e).count=(stripe rows v).count :=
      Controlled.stripe_count_perm rows e.symm v
    have result := summarize (Request.job b) cmd (fun z => Opcode.encode (pos z)) input output docket
      (fun z => time (pos z)) (fun z => space (pos z)) (fun z => depth (pos z)) header
      (stripe rows v).count wire (fun z _ => runs z) (fun z _ => (same z.2).le) (same _).le
    have ln := congrArg List.length ids
    simp only [List.length_map] at ln
    rw [show trace act start l=events from rfl,order,ordered,ln,peak_events events pos space,
      peak_events events pos depth,ids,endEq] at result
    exact result

end InterchangeROMSequence

end NearSquareRoot
end Computability
end OAI
