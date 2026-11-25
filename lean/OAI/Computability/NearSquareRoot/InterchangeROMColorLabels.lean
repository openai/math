import OAI.Computability.NearSquareRoot.InterchangeROMColorBatch

/-! # Typed color masks for the fixed routing command

The mask producer may traverse an annotated list of digit carries. Relabeling
the carries by natural numbers affects only the proof of stable filtering.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMColors

open IntegerMultiplication.Code Space

structure Labeled (A : Type*) [DecidableEq A] where
  source : List (A × Tree)
  target : List (A × Tree)
  lengths : source.length = target.length
  lanes : ∀ k, Ribbon.read k source = Ribbon.read k target
  colors : List A
  distinct : colors.Nodup
  covers : ∀ z ∈ target, z.1 ∈ colors

namespace Labeled

variable {A : Type*} [DecidableEq A]

def masks (r : Labeled A) (a : A) :=
  (r.source.map (fun z => decide (z.1 = a)), r.target.map (fun z => decide (z.1 = a)))

def query (r : Labeled A) :=
  Tree.fork (send (r.colors.map r.masks)) (send (r.source.map Prod.snd))

def answer (r : Labeled A) := send (r.target.map Prod.snd)

def work (r : Labeled A) := (r.colors.length + 1) * (size (r.source.map Prod.snd) +
  size (r.target.map Prod.snd) + 1)

private def relabel (e : A ↪ ℕ) (s : List (A × Tree)) :=
  s.map fun z => (e z.1,z.2)

private theorem rekey (e : A ↪ ℕ) (a : A) (s : List (A × Tree)) :
    Ribbon.read (e a) (relabel e s) = Ribbon.read a s := by
  unfold Ribbon.read relabel
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro z _
  by_cases h : z.1 = a <;> simp [Ribbon.keep, e.injective.eq_iff, h]

omit [DecidableEq A] in
private theorem missing (e : A ↪ ℕ) (n : ℕ) (h : ∀ a, e a ≠ n) (s : List (A × Tree)) :
    Ribbon.read n (relabel e s) = [] := by
  induction s with
  | nil => rfl
  | cons z s ih =>
    unfold Ribbon.read relabel at ih ⊢
    simp only [List.map_cons, List.flatten_cons, Ribbon.keep, decide_eq_false (h z.1), Bool.cond_false,
      ih, List.nil_append]

/-- An injective coding is sufficient even when some natural color numbers never
occur. The physical masks use the original annotations directly. -/
def encode (e : A ↪ ℕ) (r : Labeled A) : Batch where
  source := relabel e r.source
  target := relabel e r.target
  lengths := by simpa only [relabel, List.length_map] using r.lengths
  lanes k := by
    by_cases hx : ∃ a, e a = k
    · obtain ⟨a,rfl⟩ := hx
      simpa only [rekey] using r.lanes a
    · have hn (a : A) : e a ≠ k := fun h => hx ⟨a,h⟩
      simp only [missing e k hn]
  colors := r.colors.map e
  distinct := r.distinct.map e.injective
  covers z hz := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact List.mem_map.mpr ⟨x.1, r.covers _ hx, rfl⟩

@[simp] theorem encode_query (e : A ↪ ℕ) (r : Labeled A) : (encode e r).query = r.query := by
  simp only [Batch.query, query, Rows.masks, Rows.values, encode, taggedMask, relabel,
    List.map_map, Function.comp_def, e.injective.eq_iff]
  rfl

@[simp] theorem encode_answer (e : A ↪ ℕ) (r : Labeled A) :
    send ((encode e r).answer) = r.answer := by
  simp only [Rows.answer, encode, answer, relabel, List.map_map, Function.comp_def]

@[simp] theorem encode_work (e : A ↪ ℕ) (r : Labeled A) : (encode e r).work = r.work := by
  simp only [Batch.work, Rows.volume, Rows.values, Rows.answer, encode, work, relabel,
    List.map_map, List.length_map, Function.comp_def]

/-- The same literal command and the same numerical constant serve all
injectively labeled classes, including pairs of high carries. -/
theorem uniform_command : ∃ C : ℕ, ∀ {A : Type} [DecidableEq A] (_e : A ↪ ℕ) (r : Labeled A)
    env d base, (∀ j, (letters d j).length ≤ base) →
    BoundedFits env command (pile 0 r.query d) (pile 0 r.answer d)
      (C * (r.work + 1)) (base + C * (r.work + 1)) (C * (r.work + 1)) := by
  obtain ⟨C, fit⟩ := command_fits
  refine ⟨C, ?_⟩
  intro A _ e r env d base hd
  simpa only [encode_query, encode_answer, encode_work] using fit (r.encode e) env d base hd

end Labeled
end InterchangeROMColors

end NearSquareRoot
end Computability
end OAI
