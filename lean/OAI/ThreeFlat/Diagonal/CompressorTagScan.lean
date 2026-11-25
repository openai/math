import OAI.ThreeFlat.Diagonal.CompressorOrderedScan
import OAI.ThreeFlat.Diagonal.CompressorTags

namespace OAI
/-! # The ordered scans that compute compressor colors and tag offsets -/

namespace ThreeFlat.Diagonal.CompressorPacking.Ordered
open Computability.VPVNP.Compression
variable {V Tag : Type*} {d m n : ℕ}

/-- Public slot order visits all outgoing slots followed by all incoming ones. -/
def directions (d : ℕ) : List (Fin d ⊕ Fin d) :=
  List.ofFn (fun i : Fin d => Sum.inl i) ++ List.ofFn (fun i : Fin d => Sum.inr i)

@[simp] theorem directions_length (d : ℕ) : (directions d).length = 2*d := by
  simp [directions,two_mul]

private theorem in_directions (i : Fin d ⊕ Fin d) : i ∈ directions d := by
  cases i <;> simp [directions,List.mem_ofFn]

def colorBan (G : SlotGraph V d) (x : V) (f : V → Fin (2*d+1)) : List (Fin (2*d+1)) :=
  (directions d).map fun i => f (adjacent G x i)

def colors [DecidableEq V] (G : SlotGraph V d) (visit : Fin m ≃ V) : V → Fin (2*d+1) :=
  scan (List.ofFn visit) (List.ofFn (Equiv.refl (Fin (2*d+1)))) 0 (colorBan G) (fun _ => 0)

theorem colors_proper [DecidableEq V] (G : SlotGraph V d) (visit : Fin m ≃ V) :
    ∀ e, colors G visit e.1 ≠ colors G visit (G.target e).1 := by
  have full (x : V) : x ∈ List.ofFn visit := List.mem_ofFn.mpr (visit.surjective x)
  have small x f : (colorBan G x f).length < 2*d+1 := by simp [colorBan]
  exact (scan_valid G (fun _ _ => True) (fun _ a b => a ≠ b) (List.ofFn visit) full
    (Equiv.refl _) 0 (colorBan G) small (by
      intro x f a hf
      have away (i : Fin d ⊕ Fin d) : a ≠ f (adjacent G x i) := fun h =>
        hf (List.mem_map.mpr ⟨i,in_directions i,h.symm⟩)
      exact ⟨trivial,fun i => away (.inl i),fun i => (away (.inr i)).symm⟩) (fun _ => 0)).2

variable [AddCommGroup Tag]

def stepsList (shift : V × Fin d → Tag) (x : V) : List Tag :=
  0 :: List.ofFn (fun i => shift (x,i))

@[simp] theorem steps_length (shift : V × Fin d → Tag) (x : V) :
    (stepsList shift x).length = d+1 := by simp [stepsList]

private theorem step_mem (shift : V × Fin d → Tag) (x : V) (a : Tag) :
    a ∈ stepsList shift x ↔ a ∈ tagSteps shift x := by
  classical
  simp [tagSteps,stepsList,List.mem_ofFn]

/-- The list contains the source single forbidden values and the candidate
values completing the pair constraint at this incidence. Duplicate values
are harmless and keep all lengths predetermined. -/
def tagPart (G : SlotGraph V d) (shift : V × Fin d → Tag) (x : V) (f : V → Tag)
    (i : Fin d ⊕ Fin d) : List Tag :=
  let e := incident G x i
  (stepsList shift x).map (fun a => shift e + a) ++
    (stepsList shift e.1).flatMap (fun a =>
      (stepsList shift (G.target e).1).map (fun b => shift e + a + b - f (adjacent G x i)))

def tagBan (G : SlotGraph V d) (shift : V × Fin d → Tag) (x : V) (f : V → Tag) : List Tag :=
  (directions d).flatMap (tagPart G shift x f)

private theorem length_flat {α β : Type*} (xs : List α) (f : α → List β) (k : ℕ)
    (hk : ∀ x, (f x).length = k) : (xs.flatMap f).length = xs.length*k := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih,hk,Nat.succ_mul,Nat.add_comm]

theorem tagPart_length (G : SlotGraph V d) (shift : V × Fin d → Tag) (x f i) :
    (tagPart G shift x f i).length = (d+1)+(d+1)^2 := by
  simp only [tagPart,List.length_append,List.length_map,steps_length]
  rw [length_flat _ _ (d+1) (by intro a; simp), steps_length, pow_two]

theorem tagBan_length (G : SlotGraph V d) (shift : V × Fin d → Tag) (x f) :
    (tagBan G shift x f).length = 2*d*((d+1)+(d+1)^2) := by
  rw [tagBan,length_flat _ _ _ (tagPart_length G shift x f),directions_length]

variable [DecidableEq V] [DecidableEq Tag]

/-- Deterministic offset table for the supplied vertex order and tag
enumeration. The initial table and fallback are both constant zero. -/
def offsets (G : SlotGraph V d) (shift : V × Fin d → Tag) (visit : Fin m ≃ V)
    (rank : Fin n ≃ Tag) : V → Tag :=
  scan (List.ofFn visit) (List.ofFn rank) 0 (tagBan G shift) (fun _ => 0)

theorem offsets_valid [Fintype Tag] (G : SlotGraph V d) (shift : V × Fin d → Tag)
    (visit : Fin m ≃ V) (rank : Fin n ≃ Tag) (size : 2*d*((d+1)+(d+1)^2) < n) :
    TagConditions G shift (offsets G shift visit rank) := by
  let unary (x : V) (u : Tag) := ∀ i a, a ∈ tagSteps shift x → u ≠ shift (incident G x i) + a
  let ok (e : V × Fin d) (u v : Tag) := ∀ a b,
    a ∈ tagSteps shift e.1 → b ∈ tagSteps shift (G.target e).1 → u+v ≠ shift e + a + b
  have full (x : V) : x ∈ List.ofFn visit := List.mem_ofFn.mpr (visit.surjective x)
  have valid := scan_valid G unary ok (List.ofFn visit) full rank 0 (tagBan G shift)
    (fun x f => (tagBan_length G shift x f).trans_lt size) (by
      intro x f u hu
      have avoid (i) : u ∉ tagPart G shift x f i := fun hh =>
        hu (List.mem_flatMap.mpr ⟨i,in_directions i,hh⟩)
      have one (i a) (ha : a ∈ tagSteps shift x) : u ≠ shift (incident G x i)+a := fun eq =>
        avoid i (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨a,(step_mem ..).mpr ha,eq.symm⟩)))
      have two (i) (a b : Tag) (ha : a ∈ tagSteps shift (incident G x i).1)
          (hb : b ∈ tagSteps shift (G.target (incident G x i)).1) :
          u + f (adjacent G x i) ≠ shift (incident G x i)+a+b := by
        intro eq
        exact avoid i (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
          ⟨a,(step_mem ..).mpr ha,List.mem_map.mpr ⟨b,(step_mem ..).mpr hb,
            (eq_sub_of_add_eq eq).symm⟩⟩)))
      refine ⟨one,fun i => two (.inl i),?_⟩
      intro i a b ha hb
      rw [add_comm (f (G.target.symm (x,i)).1) u]
      exact two (.inr i) a b ha hb) (fun _ => 0)
  exact ⟨valid.1,valid.2⟩

end ThreeFlat.Diagonal.CompressorPacking.Ordered

end OAI
