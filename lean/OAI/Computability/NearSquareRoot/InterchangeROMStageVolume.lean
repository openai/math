import OAI.Computability.NearSquareRoot.InterchangeROMStageTablePhysical

/-! # Size of a rendered interchange bank on bounded-width packed records -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStageVolume
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  InterchangeROM InterchangeROMStage InterchangeROMStageTable InterchangeROMTable

/-- The live runtime quantities are the header and the number of payload entries,
including a delimiter for each physical address. -/
def mass (header : Tree) (records width : ℕ) : ℕ :=
  header.count + records*(width+1) + 1

theorem numeral_size_le {p : ℕ} [NeZero p] (a : ZMod p) : (numeral a.val).count ≤ 2*p+1 := by
  change size (tally a.val) ≤ _
  rw [size_tally,tally_length]
  have := a.val_lt
  omega

theorem stream_size {A : Type} {Y : A → Type} {p : ℕ} [NeZero p] (addr : Series A)
    (pay : (a : A) → Series (Y a)) (width : ℕ) (hw : ∀ a, (pay a).count ≤ width)
    (v : (a : A) → Y a → ZMod p) :
    (stripe addr fun a => stripe (pay a) fun k => numeral (v a k).val).count + 1 ≤
      (addr.count*(width+1)+1) * (2*p+2) := by
  have inner (a : A) :
      (stripe (pay a) (fun k => numeral (v a k).val)).count ≤ width*(2*p+2)+1 := by
    have h := stripe_size (pay a) _ (2*p+1) (fun k => numeral_size_le (v a k))
    exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hw a)) _)
  have outer := stripe_size addr _ _ inner
  change _ ≤ addr.count*(width*(2*p+2)+2)+1 at outer
  calc
    _ ≤ addr.count*(width*(2*p+2)+2)+2 := by omega
    _ ≤ addr.count*(width*(2*p+2)+(2*p+2))+(2*p+2) := by gcongr <;> omega
    _ = _ := by ring

private theorem forest_size (xs : List Tree) (B : ℕ) (h : ∀ x ∈ xs, x.count+1 ≤ B) :
    (Task.forest id xs).count ≤ xs.length*B+1 := by
  induction xs with
  | nil => simp [Task.forest,Tree.count]
  | cons a xs ih =>
    have ha := h a List.mem_cons_self
    have rest := ih (fun _ ht => h _ (List.mem_cons_of_mem _ ht))
    simp only [Task.forest_cons,Tree.count,List.length_cons,Nat.succ_mul,id_eq]
    omega

theorem packet_size {A : Type} {p : ℕ} (addr : Series A) (width : ℕ) (header : Tree)
    (xs : List Tree) (h : ∀ t ∈ xs, t.count+1 ≤ (addr.count*(width+1)+1)*(2*p+2)) :
    (packet header xs).count+1 ≤ (xs.length*(2*p+2)+4)*mass header addr.count width := by
  have forest := forest_size _ _ h
  let m := mass header addr.count width
  have quantity : addr.count*(width+1)+1 ≤ m := by dsimp [m,mass]; omega
  have hh : header.count ≤ m := by dsimp [m,mass]; omega
  have one : 1 ≤ m := by dsimp [m,mass]; omega
  calc
    _ ≤ header.count + xs.length*((addr.count*(width+1)+1)*(2*p+2))+3 := by
      change header.count + (Task.forest id xs).count + 1 + 1 ≤ _
      omega
    _ ≤ m + xs.length*(m*(2*p+2)) + 3*m := by gcongr; omega
    _ = _ := by dsimp only [m]; ring

theorem render_size {A : Type} {Y : A → Type} {p : ℕ} [NeZero p] (c : Parameters) (n : ℕ)
    (addr : Series A) (pay : (a : A) → Series (Y a)) (width : ℕ) (hw : ∀ a, (pay a).count ≤ width)
    (v : Ground → (a : A) → Y a → ZMod p) (header : Tree) :
    (packet header (render c n addr pay v)).count+1 ≤
      ((c.1.bank n).length*c.2.2.1*(2*p+2)+4)*mass header addr.count width := by
  have h := packet_size (p:=p) addr width header (render c n addr pay v) (by
    intro t ht
    simp only [render,blocks,List.mem_flatMap,List.mem_map] at ht
    obtain ⟨role,_,k,_,rfl⟩ := ht
    exact stream_size addr pay width hw (v (role,k)))
  simpa only [render,length_blocks] using h

theorem typed_size {A : Type} {Y : A → Type} {p : ℕ} [NeZero p] {f : InterchangeROMStage.Frame}
    (r : f.Realization) (n d : ℕ) (addr : Series A) (pay : (a : A) → Series (Y a)) (width : ℕ)
    (hw : ∀ a, (pay a).count ≤ width)
    (x : (a : A) → Y a → r.Boundary n → Fin d → ZMod p) (header : Tree) :
    (Tree.fork header (r.Tape n d (fun z j => stripe addr (fun a => stripe (pay a)
      (fun k => numeral (x a k z j).val))))).count+1 ≤
      ((f.bank n).length*d*(2*p+2)+4)*mass header addr.count width := by
  let rows := (scalarOrder r n d).tab fun z => stripe addr (fun a => stripe (pay a)
    (fun k => numeral (x a k z.1 z.2).val))
  have h := packet_size (p:=p) addr width header rows (by
    intro t ht
    obtain ⟨z,rfl⟩ := (Series.elements _ _ _).mp ht
    exact stream_size addr pay width hw (fun a k => x a k z.1 z.2))
  unfold Frame.Realization.Tape stripe
  simpa only [packet,rows,stripe,Series.card,scalarOrder_count] using h

end InterchangeROMStageVolume

end NearSquareRoot
end Computability
end OAI
