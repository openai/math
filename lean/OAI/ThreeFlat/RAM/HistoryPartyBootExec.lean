import OAI.ThreeFlat.RAM.HistoryPartyBatch
import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.ThreeFlat.RAM.FormulaMemoryAgreement

namespace OAI
/-! # Executing the selected party's 37-word boot and dyadic preparation -/

namespace ThreeFlat.RAM.HistoryPartyBootExec

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan PhysicalPinsExpr PhysicalProcedure
open HistoryPartyBatch
open scoped Fin.CommRing

variable {W : ℕ}

def raw (m : Memory W) (a : ℕ) : ℕ := (m a).val

/-- Only occupied parties read their grid row and copy count. An out-of-range motif
does not need a resident incident pointer. -/
inductive SeedRead (A : Layout) (checks : Bool) (m : ℕ → ℕ) : ℕ → Prop
  | cursor : SeedRead A checks m A.cursor
  | node : SeedRead A checks m (A.nodes+8*(m A.cursor-1)+5)
  | motifCount : SeedRead A checks m (kernel A m+3)
  | incidentPtr (live : A.motif < m (kernel A m+3)) : SeedRead A checks m (kernel A m+4)
  | partyMask (live : A.motif < m (kernel A m+3)) : SeedRead A checks m (incident A m+5)
  | kindIndex (live : occupied A m) : SeedRead A checks m (incident A m+2)
  | copyCount (live : occupied A m) : SeedRead A checks m (incident A m+3)
  | digitWidth (live : occupied A m) : SeedRead A checks m (shape A m+4)
  | kindCount (live : occupied A m) : SeedRead A checks m (shape A m+checks.toNat)

private theorem pick_agreement {src tmp : ℕ → ℕ} {vs : Fin 1 → ℕ} {index : Formula 1}
    (idx : MemoryAgreement W (fun _ => 0) tmp src vs index) (first : ℕ) (xs : List (Formula 1))
    (rows : ∀ e ∈ xs, MemoryAgreement W (fun _ => 0) tmp src vs e) :
    MemoryAgreement W (fun _ => 0) tmp src vs (HistoryPartyBatch.pick index first xs) := by
  induction xs generalizing first with
  | nil => exact MemoryAgreement.lit _
  | cons a xs ih =>
    exact MemoryAgreement.select .eq idx (MemoryAgreement.lit _) (rows a List.mem_cons_self)
      (ih _ (fun e he => rows e (List.mem_cons_of_mem _ he)))

set_option maxRecDepth 15000 in
set_option maxHeartbeats 4000000 in
private theorem seed_agreement (W : ℕ) (A : Layout) (b : Bool) (src tmp : ℕ → ℕ)
    (vs : Fin 1 → ℕ) (same : ∀ x, SeedRead A b src x → tmp x = src x) :
    MemoryAgreement W (fun _ => 0) tmp src vs (seedFormula A b) := by
  unfold seedFormula
  apply pick_agreement
  · exact ⟨rfl, Iff.rfl⟩
  · simp only [List.forall_mem_cons]
    have cursor := same _ .cursor
    have node := same _ .node
    have count := same _ .motifCount
    have ip (h : A.motif < src (kernel A src+3)) := same _ (.incidentPtr h)
    have mask (h : A.motif < src (kernel A src+3)) := same _ (.partyMask h)
    have kind (h : occupied A src) := same _ (.kindIndex h)
    have copies (h : occupied A src) := same _ (.copyCount h)
    have digit (h : occupied A src) := same _ (.digitWidth h)
    have kinds (h : occupied A src) := same _ (.kindCount h)
    clear same
    by_cases hm : A.motif < src (kernel A src+3) <;>
      by_cases hp : src (incident A src+5)/2^A.party%2=1
    all_goals
      simp only [occupied, kernel, incident, shape] at *
      simp [hm, hp] at ip mask kind copies digit kinds
      simp [MemoryAgreement, HistoryPartyBatch.rd,
        add, mul, Formula.Fits, Formula.natural, natOp, natTest, *]

private theorem seedWords_eq (W : ℕ) (A : Layout) (b : Bool) (src tmp : ℕ → ℕ)
    (same : ∀ x, SeedRead A b src x → tmp x = src x) :
    seedWords A b tmp = seedWords A b src := by
  funext j
  simpa only [seed_value] using (seed_agreement W A b src tmp (fun _ => A.seed+j.val) same).1

/-- Representability of each of the 37 rows can be checked once on the original heap. -/
theorem resident_fit (A : Layout) (b : Bool) (m : Memory W)
    (away : ∀ x, SeedRead A b (raw m) x → x < A.seed ∨ A.seed+37 ≤ x)
    (resident : ∀ j : Fin 37, (seedFormula A b).Fits W (fun _ => 0) (raw m)
      (fun _ => A.seed+j.val)) :
    ∀ j : Fin 37, ∀ μ : Memory W, agreesOutside A.seed (A.seed+37) μ m →
      (seedFormula A b).Fits W (fun _ => 0) (raw μ) (fun _ => A.seed+j.val) := by
  intro j μ frame
  exact (seed_agreement W A b (raw m) (raw μ) _
    (fun x hx => congrArg Fin.val (frame x (away x hx)))).2.mpr (resident j)

def seedMemory (A : Layout) (b : Bool) (m : Memory W) : Memory W :=
  fillSegment A.seed 37
    (fun x => (seedWords A b (raw m) ⟨(x-A.seed)%37, Nat.mod_lt _ (by decide)⟩ : Word W)) m

theorem seedMemory_at (A : Layout) (b : Bool) (m : Memory W) (j : Fin 37) :
    seedMemory A b m (A.seed+j.val) = (seedWords A b (raw m) j : Word W) := by
  have before : A.seed ≤ A.seed+j.val := by omega
  have last : A.seed+j.val < A.seed+37 := by have := j.isLt; omega
  simp only [seedMemory, fillSegment, ite_eq_left (And.intro before last), Nat.add_sub_cancel_left,
    Nat.mod_eq_of_lt j.isLt]

def extent (A : Layout) (m : ℕ → ℕ) := max (copies A m) (copies A m * digit A m)

private theorem pick_fits (W : ℕ) (mem : ℕ → ℕ) (vs : Fin 1 → ℕ) (index : Formula 1)
    (fi : index.Fits W (fun _ => 0) mem vs) (small : index.natural W (fun _ => 0) mem vs < 2^W)
    (first : ℕ) (xs : List (Formula 1)) (room : first + xs.length < 2^W)
    (rows : ∀ e ∈ xs, e.Fits W (fun _ => 0) mem vs) :
    (HistoryPartyBatch.pick index first xs).Fits W (fun _ => 0) mem vs := by
  induction xs generalizing first with
  | nil => trivial
  | cons a xs ih =>
    simp only [List.length_cons] at room
    change index.Fits W (fun _ => 0) mem vs ∧ True ∧
      index.natural W (fun _ => 0) mem vs < 2^W ∧ first < 2^W ∧
      (if natTest .eq (index.natural W (fun _ => 0) mem vs) first then a.Fits W (fun _ => 0) mem vs
       else (HistoryPartyBatch.pick index (first+1) xs).Fits W (fun _ => 0) mem vs)
    refine ⟨fi,trivial,small,by omega,?_⟩
    split
    · exact rows a (by simp)
    · exact ih (first+1) (by omega) (fun e he => rows e (List.mem_cons_of_mem _ he))

set_option maxRecDepth 15000 in
set_option maxHeartbeats 4000000 in
/-- The seed reads only bounded active addresses. Its longest compared quantity
is the dyadic extent, which is bounded by the dyadic stage's existing power capacity. -/
theorem seed_fits (W : ℕ) (A : Layout) (b : Bool) (m : Memory W) (j : Fin 37)
    (room : A.seed+37 < 2^W) (motif : A.motif < 2^W)
    (probes : ∀ x, SeedRead A b (raw m) x → x < 2^W)
    (party : A.motif < raw m (kernel A (raw m)+3) → 2^A.party < 2^W)
    (power : 2^(Nat.clog 2 (extent A (raw m))) < 2^W) :
    (seedFormula A b).Fits W (fun _ => 0) (raw m) (fun _ => A.seed+j.val) := by
  have addr : A.seed+j.val < 2^W := by have := j.isLt; omega
  have seed : A.seed < 2^W := by omega
  unfold seedFormula
  apply pick_fits
  · exact ⟨trivial,trivial,addr,seed⟩
  · change A.seed+j.val-A.seed < 2^W
    omega
  · change 0+37 < 2^W
    omega
  · have value (x : ℕ) : raw m x < 2^W := (m x).isLt
    have cap : extent A (raw m) < 2^W :=
      (Nat.le_pow_clog (by decide : 1 < 2) _).trans_lt power
    have long : copies A (raw m) * digit A (raw m) < 2^W :=
      (le_max_right _ _).trans_lt cap
    have cursor := probes _ .cursor
    have node := probes _ .node
    have count := probes _ .motifCount
    have ip (h : A.motif < raw m (kernel A (raw m)+3)) := probes _ (.incidentPtr h)
    have mask (h : A.motif < raw m (kernel A (raw m)+3)) := probes _ (.partyMask h)
    have kind (h : occupied A (raw m)) := probes _ (.kindIndex h)
    have copiesAt (h : occupied A (raw m)) := probes _ (.copyCount h)
    have digitAt (h : occupied A (raw m)) := probes _ (.digitWidth h)
    have kindsAt (h : occupied A (raw m)) := probes _ (.kindCount h)
    have divSmall : raw m (incident A (raw m)+5) / 2^A.party < 2^W :=
      (Nat.div_le_self _ _).trans_lt (value _)
    have remSmall : raw m (incident A (raw m)+5) / 2^A.party % 2 < 2^W := by omega
    have zero : 0 < 2^W := by omega
    have one : 1 < 2^W := by omega
    have two : 2 < 2^W := by omega
    have nonzeroWidth : W ≠ 0 := by
      intro eq
      subst W
      norm_num at one
    clear probes cap power
    by_cases hm : A.motif < raw m (kernel A (raw m)+3) <;>
      by_cases hp : raw m (incident A (raw m)+5) / 2^A.party % 2 = 1
    all_goals
      simp only [copies,digit,occupied,shape,incident,kernel] at *
      simp [hm,hp] at ip mask party kind copiesAt digitAt kindsAt long
      simp [HistoryPartyBatch.rd,eqz,lt,rem,div,add,mul,Formula.Fits,
        Formula.natural,opFits,natOp,natTest, *]

def output (A : Layout) (b : Bool) (m : Memory W) : Memory W :=
  HistoryDyadic.finish ((A.seed+1 : ℕ) : Word W) (seedMemory A b m) (Nat.clog 2 (extent A (raw m)))

def boot (W : ℕ) (A : Layout) (b : Bool) : Procedure W :=
  PhysicalInputPhases.writing (HeaderScan.closed (seedFormula A b)) Fin.elim0 A.seed 37

def bootCost (A : Layout) (b : Bool) := 4+37*(2*(seedFormula A b).work+4)

theorem prefix_size (W : ℕ) (A : Layout) (b : Bool) :
    let p := (boot W A b).seq (dyadic W A)
    p.labels = 20+3*(seedFormula A b).work ∧
    p.registers = 9+(seedFormula A b).work ∧ p.slots = 1 := by
  change 6+(HeaderScan.closed (w:=W) (seedFormula A b)).labels+13 = _ ∧
    4+(HeaderScan.closed (w:=W) (seedFormula A b)).binds+5 = _ ∧ 0+1 = (1 : ℕ)
  rw [Term.labels_eq, HeaderScan.binds_closed]
  omega

private theorem seed_eval (A : Layout) (b : Bool) (m : Memory W) (a : Word W) (j : Fin 37)
    (index : a.val = A.seed+j.val)
    (fits : (seedFormula A b).Fits W (fun _ => 0) (raw m) (fun _ => a.val)) :
    (HeaderScan.closed (seedFormula A b) : Term W 0 1).eval Fin.elim0 m (fun _ => a) =
      (seedWords A b (raw m) j : Word W) := by
  have word := (seedFormula A b).value_eq_natural (fun _ => 0) (raw m) (fun _ => a.val) fits
  have row : (seedFormula A b).natural W (fun _ => 0) (raw m) (fun _ => a.val) =
      seedWords A b (raw m) j := by
    rw [index]
    exact seed_value W A b _ _ j
  rw [row] at word
  simpa only [HeaderScan.eval_closed, raw, Fin.cast_val_eq_self, Nat.cast_zero] using word

/-- The protected inputs are concrete cell addresses in the original heap. The fit
certificate concerns arithmetic on the 37 row operands during the write. -/
theorem boot_exec (A : Layout) (b : Bool) (m : Memory W) (room : A.seed+37 < 2^W)
    (away : ∀ x, SeedRead A b (raw m) x → x < A.seed ∨ A.seed+37 ≤ x)
    (fit : ∀ j : Fin 37, ∀ μ : Memory W, agreesOutside A.seed (A.seed+37) μ m →
      (seedFormula A b).Fits W (fun _ => 0) (raw μ) (fun _ => A.seed+j.val)) :
    (boot W A b).Exec m (seedMemory A b m) (bootCost A b) := by
  unfold boot bootCost
  rw [← HeaderScan.binds_closed (w:=W) (seedFormula A b)]
  let seedRow (x : ℕ) : Word W :=
    (seedWords A b (raw m) ⟨(x-A.seed) % 37, Nat.mod_lt _ (by decide)⟩ : Word W)
  let e : Term W 0 1 := HeaderScan.closed (seedFormula A b)
  have computes (orig : Memory W) (original : orig=m) (a : Word W) (μ : Memory W)
      (lo : A.seed ≤ a.val) (hi : a.val < A.seed+37)
      (frame : agreesOutside A.seed (A.seed+37) μ orig) :
      e.eval Fin.elim0 μ (fun _ => a) = seedRow a.val := by
    subst orig
    let j : Fin 37 := ⟨a.val-A.seed, by omega⟩
    have index : a.val = A.seed+j.val := by dsimp [j]; omega
    have bounded := fit j μ frame
    rw [← index] at bounded
    change (HeaderScan.closed (seedFormula A b) : Term W 0 1).eval Fin.elim0 μ (fun _ => a) = _
    rw [seed_eval A b μ a j index bounded]
    have same := seedWords_eq W A b (raw m) (raw μ) (fun x hx => congrArg Fin.val (frame x (away x hx)))
    rw [same]
    exact congrArg (fun cell : Fin 37 => (seedWords A b (raw m) cell : Word W))
      (Fin.ext (Nat.mod_eq_of_lt j.isLt).symm)
  intro P R K machine pc reg pub exit installed params cfg input start original
  subst input
  exact PhysicalInputPhases.writing_spec e Fin.elim0 A.seed 37 room (fun x => x=m) seedRow
    computes machine pc reg pub exit installed params cfg m start rfl

theorem dyadic_exec (A : Layout) (b : Bool) (m : Memory W) (room : A.seed+37 < 2^W)
    (power : 2^(Nat.clog 2 (extent A (raw m))) < 2^W) :
    (dyadic W A).Exec (seedMemory A b m) (output A b m) (6+(3*Nat.clog 2 (extent A (raw m))+5)) := by
  intro P R K M pc reg pub exit installed data c src entry eq
  subst src
  have ptr : M.publicData (pub (0 : Fin 1)) = (A.seed : Word W) := data (0 : Fin 1)
  have startWord : seedMemory A b m A.seed = ((A.seed+1 : ℕ) : Word W) :=
    seedMemory_at A b m 0
  have sizeWord : seedMemory A b m (A.seed+1) = (extent A (raw m) : Word W) :=
    seedMemory_at A b m 1
  have extentFit : extent A (raw m) < 2^W :=
    (Nat.le_pow_clog (by decide : 1 < 2) _).trans_lt power
  have advance := HistoryDyadic.advance M pc reg (pub (0 : Fin 1)) exit installed c (seedMemory A b m) entry
  dsimp only at advance
  rw [ptr, Fin.val_cast_of_lt (by omega : A.seed < 2^W), startWord,
    Fin.val_cast_of_lt (by omega : A.seed+1 < 2^W), sizeWord, Fin.val_cast_of_lt extentFit] at advance
  obtain ⟨out,atExit,run⟩ := advance power
  exact ⟨_,le_rfl,out,_,run,atExit,rfl⟩

theorem prefix_exec (W : ℕ) (A : Layout) (b : Bool) (m : Memory W) (room : A.seed+37 < 2^W)
    (away : ∀ x, SeedRead A b (raw m) x → x < A.seed ∨ A.seed+37 ≤ x)
    (fit : ∀ j : Fin 37, ∀ μ : Memory W, agreesOutside A.seed (A.seed+37) μ m →
      (seedFormula A b).Fits W (fun _ => 0) (raw μ) (fun _ => A.seed+j.val))
    (power : 2^(Nat.clog 2 (extent A (raw m))) < 2^W) :
    ((boot W A b).seq (dyadic W A)).Exec m (output A b m)
      (bootCost A b + (6+(3*Nat.clog 2 (extent A (raw m))+5))) :=
  Procedure.Exec.then (boot_exec A b m room away fit) (dyadic_exec A b m room power)

/-- The two dyadic writes occupy precisely the exponent and power cells of the seed. -/
theorem output_at (A : Layout) (b : Bool) (m : Memory W) (room : A.seed+37 < 2^W) (x : ℕ) :
    output A b m x =
      if x=A.seed+3 then ((2^(Nat.clog 2 (extent A (raw m))) : ℕ) : Word W)
      else if x=A.seed+2 then (Nat.clog 2 (extent A (raw m)) : Word W) else seedMemory A b m x := by
  have two : ((A.seed+1 : ℕ) : Word W)+1 = ((A.seed+2 : ℕ) : Word W) :=
    (Nat.cast_succ (A.seed+1)).symm
  have three : ((A.seed+2 : ℕ) : Word W)+1 = ((A.seed+3 : ℕ) : Word W) :=
    (Nat.cast_succ (A.seed+2)).symm
  simp only [output, HistoryDyadic.finish, writeMemory, two, three,
    Fin.val_cast_of_lt (by omega : A.seed+2 < 2^W), Fin.val_cast_of_lt (by omega : A.seed+3 < 2^W)]

theorem output_outside (A : Layout) (b : Bool) (m : Memory W) (room : A.seed+37 < 2^W)
    (x : ℕ) (outside : x < A.seed ∨ A.seed+37 ≤ x) : output A b m x = m x := by
  rw [output_at A b m room x]
  simp only [seedMemory, fillSegment, ite_eq_right (by omega : x ≠ A.seed+3),
    ite_eq_right (by omega : x ≠ A.seed+2), ite_eq_right (by omega : ¬(A.seed ≤ x ∧ x < A.seed+37))]


end ThreeFlat.RAM.HistoryPartyBootExec

end OAI
