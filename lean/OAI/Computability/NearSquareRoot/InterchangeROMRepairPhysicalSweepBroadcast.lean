import OAI.Computability.NearSquareRoot.InterchangeROMRoute
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect
import OAI.Computability.IntegerMultiplication.Strip.Cars
import OAI.Computability.IntegerMultiplication.Code.Dup
import OAI.Computability.IntegerMultiplication.Match

/-! # Copying a comparison mark across its contiguous record payload

One fixed P192 command reads the two aligned streams. It takes the length of
each payload from its own list of values and emits that many copies of the
corresponding mark. The clock counts both the input and the output trees.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Broadcast

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open CommonRegisters Space

private abbrev Row := Tree × List Tree

private def repeatRow (row : Row) : List Tree := List.replicate row.2.length row.1
private def fields (rows : List Row) := (rows.map Prod.fst, rows.map Prod.snd, ())
private def answer (rows : List Row) := rows.map repeatRow

private theorem replicate_cost (n : ℕ) (x : Tree) :
    n * size x ≤ size (List.replicate n x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, size_cons, Nat.succ_mul]
    omega

private theorem cell : Computes (fun row : Row => 2*size row + size (repeatRow row)) repeatRow := by
  let shape (r : Row) := (ruler r.2,r.1)
  have h : Easy shape := by dsimp [shape]; fun_prop
  have u := Computes.comp (generate (X:=Tree)) h
  have eq : ((fun i : Tally × Tree => List.replicate i.1.length i.2) ∘ shape) = repeatRow := by
    funext x
    simp [shape,repeatRow]
  rw [eq] at u
  apply u.mono
  intro r
  change size r + ((ruler r.2).length+1)*size r.1 ≤ _
  rw [ruler_length,Nat.add_mul,Nat.one_mul]
  have h₁ := replicate_cost r.2.length r.1
  have h₂ : size r.1 ≤ size r := by rw [size_prod]; omega
  dsimp only [repeatRow] at *
  omega

private theorem row_sum (l : List Row) :
    costSum (fun r : Row => 2*size r + size (repeatRow r)) l ≤ 2*size l + size (answer l) := by
  induction l with
  | nil => simp [answer]
  | cons r l ih =>
    simp only [costSum_cons, size_cons, answer, List.map_cons] at *
    omega

private theorem flat_size (l : List Row) : size l ≤ size (fields l) := by
  induction l with
  | nil => simp [fields]
  | cons r l ih =>
    simp only [fields,List.map_cons,size_cons,size_prod] at *
    omega

private theorem universal : Task (fun l : List Row => size (fields l) + size (answer l))
    (fun l => send (fields l)) (fun l => send (answer l)) := by
  let reassemble (i : List Tree × List (List Tree) × Unit) :=
    zipFair (Tree.atom false) ([] : List Tree) (i.1,i.2.1)
  have hzip : Easy reassemble :=
    (Easy.fst.pair (Easy.snd.compose Easy.fst)).compose (easy_zip _ _)
  have h (l : List Row) : reassemble (fields l) = l := by
    dsimp only [reassemble,fields]
    rw [fair]
    simp
  have joined := (Computes.comp cell.mapping hzip).on fields
  change Task (fun l => size (fields l) + (size (reassemble (fields l)) +
    costSum (fun r : Row => 2*size r + size (repeatRow r)) (reassemble (fields l))))
    (fun l => send (fields l)) (fun l => send (answer (reassemble (fields l)))) at joined
  simp only [h] at joined
  refine joined.bound 4 (fun l => ?_)
  have h₁ := row_sum l
  have h₂ := flat_size l
  omega

/-- The task is instantiated on the universal tree-list interface once, independently
of comparison alphabets, data alphabets and all layout dimensions. -/
noncomputable def command : Cmd := universal.choose
noncomputable def factor : ℕ := universal.choose_spec.choose + 1
noncomputable def regs : ℕ := (RegisterSelect.within_eventually command).exists.choose

theorem within : Within regs command := (RegisterSelect.within_eventually command).exists.choose_spec

def input {A : Type} {D : A → Type} (rows : Series A) (payload : (a : A) → Series (D a))
    (mark : A → Tree) (v : (a : A) → D a → Tree) : Tree :=
  Task.forest id [stripe rows mark, stripe rows (fun a => stripe (payload a) (v a))]

def output {A : Type} {D : A → Type} (rows : Series A) (payload : (a : A) → Series (D a))
    (mark : A → Tree) : Tree :=
  stripe rows fun a => stripe (payload a) fun _ => mark a

/-- Every mark and payload is read as a self-delimiting tree. Empty rows and
empty payloads use the same command. The three bounds use one absolute factor. -/
theorem bounded {A : Type} {D : A → Type} (rows : Series A) (payload : (a : A) → Series (D a))
    (mark : A → Tree) (v : (a : A) → D a → Tree) (env : Env) (deck : Deck) (base : ℕ)
    (hd : DeckCap base deck) :
    let x := input rows payload mark v
    let y := output rows payload mark
    let B := factor * (x.count + y.count + 1)
    BoundedFits env command (pile 0 x deck) (pile 0 y deck) B (base+B) B := by
  dsimp only
  let l : List Row := rows.tab fun a => (mark a,(payload a).tab (v a))
  have hx : send (fields l) = input rows payload mark v := by
    simp only [l,fields,send_prod,input,Task.forest_cons,Task.forest_nil,id_eq,stripe_eq,Series.tab,
      List.map_map,Function.comp_def]
    congr 2
    rw [← Task.forest_send,Task.forest_map,← Task.forest_send,Task.forest_map]
    rfl
  have hy : send (answer l) = output rows payload mark := by
    simp only [answer,l,List.map_map,Function.comp_def,repeatRow,output,stripe_eq,Series.tab,
      List.length_map]
    rw [← Task.forest_send,Task.forest_map,← Task.forest_send,Task.forest_map]
    simp
    rfl
  let c := universal.choose_spec.choose
  let x := input rows payload mark v
  let y := output rows payload mark
  let N := x.count + y.count + 1
  have trace := universal.choose_spec.choose_spec l env deck
  change Fits env command (pile 0 (send (fields l)) deck) (pile 0 (send (answer l)) deck)
    (c*((send (fields l)).count + (send (answer l)).count + 1)) at trace
  rw [hx,hy] at trace
  change Fits env command (pile 0 x deck) (pile 0 y deck) (c*N) at trace
  change BoundedFits env command (pile 0 x deck) (pile 0 y deck)
    ((c+1)*N) (base+(c+1)*N) ((c+1)*N)
  rw [Nat.add_mul,Nat.one_mul]
  apply (BoundedFits.of_fits trace (depth:=c*N) (fun j => ?_) le_rfl).mono (by omega) le_rfl (by omega)
  have cap := hd.pile 0 x j
  change (letters (pile 0 x deck) j).length ≤ base + x.count at cap
  dsimp only [N]
  omega

/-- A width bound and two symbol sizes suffice to express the clock in the
usual number of physical record cells, including the empty-row separators. -/
theorem cells {A : Type} {D : A → Type} (rows : Series A) (payload : (a : A) → Series (D a))
    (mark : A → Tree) (v : (a : A) → D a → Tree) (w m c : ℕ)
    (hw : ∀ a, (payload a).count ≤ w) (hm : ∀ a, (mark a).count ≤ m)
    (hc : ∀ a d, (v a d).count ≤ c) :
    (input rows payload mark v).count + (output rows payload mark).count + 1 ≤
      (m+c+7) * (rows.count*(w+1)+1) := by
  have bound (f : (a : A) → D a → Tree) (n : ℕ) (h : ∀ a d, (f a d).count ≤ n) :
      (stripe rows fun a => stripe (payload a) (f a)).count ≤
        rows.count * (w*(n+1)+1+1)+1 :=
    stripe_size _ _ _ (fun a => (stripe_size _ _ _ (h a)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hw a)) 1))
  have h₁ := stripe_size rows mark m hm
  have h₂ := bound v c hc
  have h₃ := bound (fun a _ => mark a) m (fun a _ => hm a)
  change (stripe rows mark).count + ((stripe rows fun a => stripe (payload a) (v a)).count + 1 + 1)
    + 1 + (stripe rows fun a => stripe (payload a) fun _ => mark a).count + 1 ≤ _
  ring_nf at h₁ h₂ h₃ ⊢
  omega

end InterchangeROMRepair.Physical.Broadcast

end NearSquareRoot
end Computability
end OAI
