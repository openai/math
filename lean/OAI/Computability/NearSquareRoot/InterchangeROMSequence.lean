import OAI.Computability.NearSquareRoot.InterchangeTailBatch
import OAI.Computability.NearSquareRoot.InterchangeROMEffectiveSeries
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxFold

/-! # A generated affine and recursive instruction sequence on one row

The shape header stays on register one. Each instruction receives a fresh
copy beside the current payload and must return the next payload on register
zero. The payload crosses no register during dispatch.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMSequence

open IntegerMultiplication IntegerMultiplication.Code CommonRegisters LoomRegisters Space GeneratorSyntax
  NearSquareRoot.InterchangeBatch

private def start : Cmd := splitRoot 0 (fun _ => .pass) (move 0 1 2)
private def frame : Cmd := (clone 1 0 2).join (pack 0)

/-- A literal instruction list uses right-associated joins, so its previous
instructions do not occupy the return stack during a later subcall. -/
def body {M : Type} (cmd : M → Cmd) : List M → Cmd
  | [] => discard 1
  | m::ms => frame.join ((cmd m).join (body cmd ms))

def command {M : Type} (cmd : M → Cmd) (ms : List M) := start.join (body cmd ms)

theorem within {M : Type} {R : ℕ} (hR : 3≤R) (cmd : M → Cmd) (hcmd : ∀ m, Within R (cmd m))
    (ms : List M) : Within R (command cmd ms) := by
  refine ⟨split_within (by omega) (fun _ => trivial) (move_within (by omega) (by omega) (by omega)),?_⟩
  induction ms with
  | nil => exact discard_within (by omega)
  | cons m ms ih => exact ⟨⟨clone_within (by omega) (by omega) (by omega), (by omega : 0<R)⟩,hcmd m,ih⟩

private theorem frame_run (h x : Tree) (env : Env) (r : Deck) :
    Fits env frame (pile 1 h (pile 0 x r)) (pile 0 (.fork h x) (pile 1 h r)) (45*h.count+3) := by
  have dup := fits_clone (i:=1) (j:=0) (u:=2) (by decide) (by decide) (by decide) h env (pile 0 x r)
  have close := fits_pack h x (pile 1 h r) 0 env
  rw [pile_comm 0 x r 1 h (by decide),pile_comm 0 h _ 1 h (by decide)] at close
  exact dup.join close

private theorem body_run {X M : Type} (cmd : M → Cmd) (opcode : X → M) (input output : X → Tree)
    (h : Tree) (env : Env) (time : X → ℕ) (V S D : ℕ) {x y : Tree} {qs : List X}
    (wire : Chain input output x qs y) (src : ∀ z∈qs, (input z).count≤V) (dst : y.count≤V)
    (op : ∀ z∈qs, ∀ deck base, DeckCap base deck →
      BoundedFits env (cmd (opcode z)) (pile 0 (.fork h (input z)) deck) (pile 0 (output z) deck)
        (time z) (base+S) D)
    (r : Deck) (base : ℕ) (hc : DeckCap base r) :
    BoundedFits env (body cmd (qs.map opcode)) (pile 1 h (pile 0 x r)) (pile 0 y r)
      ((qs.map time).sum + (qs.length+1)*(55*(h.count+1)))
      (base+dataSpace V h.count S) (returnSpace h.count D) := by
  have la : V+100*(h.count+1) ≤ dataSpace V h.count S := le_max_left ..
  have sub : h.count+S ≤ dataSpace V h.count S := le_max_right ..
  have lret : 100*(h.count+1) ≤ returnSpace h.count D := le_max_left ..
  have cret : D+1 ≤ returnSpace h.count D := le_max_right ..
  induction wire with
  | nil x =>
    have t := fits_discard 1 h env (pile 0 x r)
    apply (BoundedFits.of_fits t (cap:=base+dataSpace V h.count S) (depth:=returnSpace h.count D)
      (fun i => by have := ((hc.pile 0 x).pile 1 h) i; omega) (by omega)).mono _ le_rfl le_rfl
    simp; omega
  | @cons q qs y more ih =>
    have rest := ih (fun z hz => src z (List.mem_cons_of_mem _ hz)) dst
      (fun z hz => op z (List.mem_cons_of_mem _ hz))
    have size := src q List.mem_cons_self
    have hd := hc.pile 1 h
    have subrun := op q List.mem_cons_self _ _ hd
    have same := subrun.mono le_rfl (by omega : base+h.count+S ≤ base+dataSpace V h.count S) le_rfl
    rw [← pile_comm 0 (output q) r 1 h (by decide)] at rest
    have next := same.join rest cret
    have prep := BoundedFits.of_fits (frame_run h (input q) env r)
      (cap:=base+dataSpace V h.count S) (depth:=45*h.count+3)
      (fun i => by have := ((hc.pile 0 (input q)).pile 1 h) i; omega) le_rfl
    apply (prep.join next (by omega)).mono _ le_rfl le_rfl
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- One shared input header, the exact sum of the actual instruction clocks
(including recursive clocks), and a single copy of the header beside each
child's peak. The return bound is independent of the word length. -/
theorem run {X M : Type} (cmd : M → Cmd) (opcode : X → M) (input output : X → Tree)
    (h : Tree) (env : Env) (time : X → ℕ) (V S D : ℕ) {x y : Tree} {qs : List X}
    (wire : Chain input output x qs y) (src : ∀ z∈qs, (input z).count≤V) (dst : y.count≤V)
    (op : ∀ z∈qs, ∀ deck base, DeckCap base deck →
      BoundedFits env (cmd (opcode z)) (pile 0 (.fork h (input z)) deck) (pile 0 (output z) deck)
        (time z) (base+S) D)
    (r : Deck) (base : ℕ) (hc : DeckCap base r) :
    BoundedFits env (command cmd (qs.map opcode)) (pile 0 (.fork h x) r) (pile 0 y r)
      ((qs.map time).sum + (qs.length+1)*(110*(h.count+1)))
      (base+dataSpace V h.count S) (returnSpace h.count D) := by
  have size : x.count≤V := by cases wire with
    | nil => exact dst
    | cons q => exact src q List.mem_cons_self
  have la : V+100*(h.count+1) ≤ dataSpace V h.count S := le_max_left ..
  have lret : 100*(h.count+1) ≤ returnSpace h.count D := le_max_left ..
  have openRun : Fits env start (pile 0 (.fork h x) r) (pile 1 h (pile 0 x r)) (42*h.count+4) :=
    fits_pair (fits_move (i:=0) (j:=1) (u:=2) (by decide) (by decide) h env (pile 0 x r))
  have lift := BoundedFits.of_fits openRun (cap:=base+dataSpace V h.count S) (depth:=42*h.count+4)
    (fun i => by have := hc.pile 0 (.fork h x) i; simp only [Tree.count] at this; omega) le_rfl
  have calls := body_run cmd opcode input output h env time V S D wire src dst op r base hc
  apply (lift.join calls (by omega)).mono _ le_rfl le_rfl
  have room : 55*(h.count+1) ≤ (qs.length+1)*(55*(h.count+1)) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have split : (qs.length+1)*(110*(h.count+1)) =
      (qs.length+1)*(55*(h.count+1))+(qs.length+1)*(55*(h.count+1)) := by ring
  rw [split]
  omega

/-- The proof index of each instruction remembers its input row. -/
def trace {M A : Type} (act : M → A → A) (s : A) : List M → List (M × A)
  | [] => []
  | m::ms => (m,s) :: trace act (act m s) ms

@[simp] theorem trace_code {M A : Type} (act : M → A → A) (s : A) (ms : List M) :
    (trace act s ms).map Prod.fst = ms := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih => simp [trace,ih]

theorem trace_chain {M A : Type} (act : M → A → A) (row : A → Tree) (s : A) (ms : List M) :
    Chain (fun z : M × A => row z.2) (fun z => row (act z.1 z.2)) (row s) (trace act s ms)
      (row (ms.foldl (fun x m => act m x) s)) := by
  induction ms generalizing s with
  | nil => exact .nil _
  | cons m ms ih => exact .cons (m,s) (ih (act m s))

theorem body_map {M N : Type} (cmd : M → Cmd) (g : N → M) (ms : List N) :
    body cmd (ms.map g) = body (cmd ∘ g) ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp only [List.map_cons,body,ih,Function.comp_apply]

/-- An effective opcode compiler gives an effective whole-word compiler
for every computable generated word. -/
theorem effective_command {X M : Type} [Primcodable X] [Primcodable M] (cmd : M → Cmd)
    (hc : Effective ltr cmd) {ms : X → List M} (hm : Computable ms) :
    Effective ltr fun x => command cmd (ms x) := by
  let append (_ : X) (x : M × File) := joinFile (file ltr frame) (joinFile (file ltr (cmd x.1)) x.2)
  have hf : Computable₂ append := (primrec_joinFile.to_comp.comp (Computable.const _)
    (primrec_joinFile.to_comp.comp (hc.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd))).to₂
  have act := computable_foldr (z:=fun _ => file ltr (discard 1)) hm (Computable.const _) hf
  have work : Effective ltr (fun x => body cmd (ms x)) := by
    apply act.of_eq
    intro x
    dsimp only
    induction ms x with
    | nil => rfl
    | cons m ms ih => simp only [List.foldr_cons,append,ih,body,joinFile_file]
  exact (effective_const ltr start).join work

/-- The individual instruction compiler can depend on the common stage
index as well as on its entry in the word. -/
theorem effective_family {X M : Type} [Primcodable X] [Primcodable M] (cmd : X → M → Cmd)
    (hc : Effective ltr (fun z : X × M => cmd z.1 z.2)) {ms : X → List M} (hm : Computable ms) :
    Effective ltr fun x => command (cmd x) (ms x) := by
  have tagged : Computable (fun x => (ms x).map (fun m => (x,m))) :=
    computable_map hm (Computable.fst.pair Computable.snd).to₂
  apply (effective_command (fun z : X × M => cmd z.1 z.2) hc tagged).of_eq
  intro x
  simp only [command,body_map,Function.comp_def]

end InterchangeROMSequence

end NearSquareRoot
end Computability
end OAI
