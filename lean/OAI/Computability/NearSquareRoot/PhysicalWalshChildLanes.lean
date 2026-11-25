import OAI.Computability.NearSquareRoot.KernelPassMixBanks
import OAI.Computability.NearSquareRoot.BoundedProgram
import OAI.Computability.IntegerMultiplication.Code.Dup
import OAI.Computability.IntegerMultiplication.Toom.Evaluate

/-! # Packing complete spectator blocks into recursive Walsh lanes

For a fixed number `W` of lanes the parent stream visits group `g`, then lane
`j`, then the consecutive records of its block. The child bank stores one
entire row per `j`. The two programs convert these layouts with bounded
linear scans, using a shared unary block-length header.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.ChildLanes

open IntegerMultiplication Code MixBankLayout

variable {A G I : Type} {W : ℕ}

/-- Consecutive blocks with the lane index varying fastest among spectators. -/
def stream (l : List G) (block : G → Fin W → List A) : List A :=
  ((l.map (fun g => List.ofFn (block g))).flatten).flatten

/-- One complete physical row per child lane, in the same group order. -/
def rows (l : List G) (block : G → Fin W → List A) : List (List A) :=
  (bank l block).map List.flatten

def split (W : ℕ) (p : List Tally × List A) : List (List A) :=
  let blocks := (Piecework.segment ((p.1.map (List.replicate W)).flatten) p.2).1
  let groups := (Piecework.segment (p.1.map (fun _ => tally W)) blocks).1
  (scatter W [] groups).map List.flatten

private def cutRows (W : ℕ) (p : List Tally × List (List A)) : List (List (List A)) :=
  List.ofFn fun j : Fin W => (Piecework.segment p.1 (Iter.pick [] (p.2, tally j.val))).1

def merge (W : ℕ) (p : List Tally × List (List A)) : List A :=
  ((align W [] (ruler p.1, cutRows W p)).flatten).flatten

theorem split_easy [Codec A] (W : ℕ) : Easy (split (A := A) W) := by
  have rep : Easy (fun r : Tally => List.replicate W r) := by
    have h := Toom.easy_ofFn (fun _ : Fin W => id (α := Tally)) (fun _ => Easy.identity)
    simpa only [id_eq, List.ofFn_const] using h
  have widths : Easy (fun p : List Tally × List A => (p.1.map (List.replicate W)).flatten) :=
    (Easy.fst.compose rep.mapping).compose Easy.flatten
  have phases : Easy (fun p : List Tally × List A => p.1.map (fun _ => tally W)) :=
    Easy.fst.compose (Easy.const (tally W)).mapping
  exact ((Piecework.easySegment phases (Piecework.easySegment widths Easy.snd).fstCompose).fstCompose.compose
    (easy_scatter W ([] : List A))).compose Easy.flatten.mapping

theorem merge_easy [Codec A] (W : ℕ) : Easy (merge (A := A) W) := by
  have cuts : Easy (cutRows (A := A) W) := by
    apply Toom.easy_ofFn
    intro j
    have row : Easy (fun p : List Tally × List (List A) => Iter.pick [] (p.2,tally j.val)) :=
      (Easy.snd.pair (Easy.const (tally j.val))).compose (Iter.facile [])
    exact (Piecework.easySegment Easy.fst row).fstCompose
  exact ((((Easy.ruler (Easy.fst : Easy (Prod.fst (α := List Tally) (β := List (List A))))).pair cuts).compose
    (easy_align W ([] : List A))).compose Easy.flatten).compose Easy.flatten

private theorem replicate_map_length (l : List G) (block : G → List A) (R : ℕ)
    (h : ∀ g ∈ l, (block g).length = R) :
    (l.map block).map (tally ∘ List.length) = List.replicate l.length (tally R) := by
  rw [← List.map_const' (l := l), List.map_map]
  exact List.map_congr_left (fun g hg => congrArg tally (h g hg))

theorem split_stream (l : List G) (block : G → Fin W → List A) (R : ℕ)
    (h : ∀ g ∈ l, ∀ j, (block g j).length = R) :
    split W (List.replicate l.length (tally R),stream l block) = rows l block := by
  let cols := l.map (fun g => List.ofFn (block g))
  let rulers := List.replicate l.length (tally R)
  have hblocks : cols.flatten.map (tally ∘ List.length) = (rulers.map (List.replicate W)).flatten := by
    unfold cols rulers
    rw [← List.map_const' (b := tally R) (l := l), List.map_flatten]
    apply congrArg List.flatten
    simp only [List.map_map, Function.comp_def, List.map_ofFn]
    apply List.map_congr_left
    intro g hg
    simp only [h g hg, List.ofFn_const]
  have hgroups : cols.map (tally ∘ List.length) = rulers.map (fun _ => tally W) := by
    simp only [cols,rulers,List.map_map,Function.comp_def,List.length_ofFn,List.map_const',List.map_replicate]
  have s₁ := Piecework.prescribed cols.flatten
  have s₂ := Piecework.prescribed cols
  rw [hblocks] at s₁
  rw [hgroups] at s₂
  change (scatter W [] (Piecework.segment (rulers.map (fun _ => tally W))
    (Piecework.segment (rulers.map (List.replicate W)).flatten cols.flatten.flatten).1).1).map _ = _
  rw [s₁,s₂]
  exact congrArg (List.map List.flatten) (scatter_columns [] l block)

theorem merge_rows (l : List G) (block : G → Fin W → List A) (R : ℕ)
    (h : ∀ g ∈ l, ∀ j, (block g j).length = R) :
    merge W (List.replicate l.length (tally R),rows l block) = stream l block := by
  have cuts : cutRows W (List.replicate l.length (tally R), rows l block) = bank l block := by
    simp only [cutRows, rows, bank, List.map_ofFn, Iter.entry]
    apply congrArg List.ofFn
    funext j
    have h' := Piecework.prescribed (l.map (fun g => block g j))
    rw [replicate_map_length l _ R (fun g hg => h g hg j)] at h'
    exact congrArg Prod.fst h'
  unfold merge
  simp only [cuts, ruler, List.map_replicate]
  change (align W [] (tally l.length, bank l block)).flatten.flatten = _
  rw [align_bank]
  rfl

private theorem size_copies {Z : Type} [Codec Z] (n : ℕ) (r : Z) :
    size (List.replicate n r) = n * (size r + 1) + 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, size_cons, ih]; ring

private theorem usingCuts {P Q : Type} [Codec P] [Codec Q]
    (f : List Tally × P → Q) (hf : Easy f) (n R : I → ℕ) (x : I → P) :
    let h t := (tally (n t),tally (R t))
    let cost t := size (x t) + (n t + 1) * (R t + 1)
    Space.BoundedTask cost cost (fun t => send (h t, x t))
      (fun t => send (h t, f (List.replicate (n t) (tally (R t)), x t))) := by
  intro h cost
  have gen := (generate (X := Tally)).on h
  simp only [h,tally_length] at gen
  have body := (gen.left fun t => send (x t)).compose
    (hf.on fun t => (List.replicate (n t) (tally (R t)), x t))
  have body' : Task cost (fun t => .fork (send (h t)) (send (x t)))
      (fun t => send (f (List.replicate (n t) (tally (R t)), x t))) := by
    apply body.bound 5
    intro t
    simp only [cost, size_prod, size_copies, size_tally, tally_length]
    ring_nf
    omega
  have both := KernelPassMixBanks.preserveHeader (send ∘ h) _ _ _ body'
  apply (Space.BoundedTask.of_time both).bound 8 16 <;> intro t
  · change size (h t) + cost t + 1 ≤ _
    simp only [h,cost,size_prod,size_tally,tally_length]
    ring_nf
    omega
  · change size (h t, x t) + (size (h t) + cost t) + 1 ≤ _
    simp only [h,cost,size_prod,size_tally,tally_length]
    ring_nf
    omega

variable [Codec A] {α : I → Type}

/-- Physically split the one-row stream into `W` aligned child lanes. Both
rulers are retained and usable by the child-call header adapter. -/
theorem splitTask (l : (t : I) → List (α t)) (block : (t : I) → α t → Fin W → List A)
    (R : I → ℕ) (lengths : ∀ t, ∀ a ∈ l t, ∀ j, (block t a j).length = R t) :
    let h t := (tally (l t).length,tally (R t))
    let cost t := size (stream (l t) (block t)) + ((l t).length+1)*(R t+1)
    Space.BoundedTask cost cost (fun t => send (h t, stream (l t) (block t)))
      (fun t => send (h t, rows (l t) (block t))) := by
  intro h cost
  simpa only [split_stream _ _ _ (lengths _)] using
    (usingCuts (split W) (split_easy W) (fun t => (l t).length) R (fun t => stream (l t) (block t)))

/-- Physically merge the child bank back into one row. -/
theorem mergeTask (l : (t : I) → List (α t)) (block : (t : I) → α t → Fin W → List A)
    (R : I → ℕ) (lengths : ∀ t, ∀ a ∈ l t, ∀ j, (block t a j).length = R t) :
    let h t := (tally (l t).length,tally (R t))
    let cost t := size (rows (l t) (block t)) + ((l t).length+1)*(R t+1)
    Space.BoundedTask cost cost (fun t => send (h t, rows (l t) (block t)))
      (fun t => send (h t, stream (l t) (block t))) := by
  intro h cost
  simpa only [merge_rows _ _ _ (lengths _)] using
    (usingCuts (merge W) (merge_easy W) (fun t => (l t).length) R (fun t => rows (l t) (block t)))

end PhysicalWalsh.ChildLanes

end NearSquareRoot
end Computability
end OAI
