import OAI.Computability.NearSquareRoot.InterchangeROMTableMask
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomROM

/-! # Assembling the persistent mask row from individual direction rows

The physical input and output are banks of whole address streams. Each input
stream contains a single three-way comparison at every address. One four-register
program combines them into the singleton stream containing the little-endian sign
mask at every address. Its coefficient is computable from the layout and its
linear clock is independent of the number of addresses.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMTable

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open InterchangeROMRepair GeneratorSyntax LoomRegisters Space

/-- Attach a singleton field delimiter to the numeral produced at each address. -/
def maskResultTable (pos : List ℕ) := (comparisonTable pos).map fun kv =>
  (kv.1,Tree.fork kv.2 (.atom false))

private theorem mapResult {s : List (Tree × Tree)} {x y : Tree} (hm : (x,y) ∈ s) (f : Tree → Tree) :
    RegisterLookup.read (s.map fun kv => (kv.1, f kv.2)) x = f (RegisterLookup.read s x) := by
  induction s with
  | nil => cases hm
  | cons kv s ih =>
    simp only [List.map_cons,RegisterLookup.read]
    by_cases h : kv.1 = x
    · simp [h]
    · simp only [h,ite_false]
      exact ih ((List.mem_cons.mp hm).resolve_left fun e => h (congrArg Prod.fst e).symm)

theorem maskResult_correct {m : ℕ} (cols : Series (Fin m)) (v : Fin m → Ordering) :
    let t := maskResultTable (cols.tab Fin.val)
    let p := stripe cols (comparisonMark ∘ comparisonCode ∘ v)
    let q := stripe (Series.natural 1) (fun _ => numeral (Raw.mask (fun j => decide (v j = .gt))).val)
    RegisterLookup.read t p = q ∧ (p,q) ∈ t := by
  have h := comparisonTable_correct cols v
  exact ⟨(mapResult h.2 (fun t => Tree.fork t (.atom false))).trans
    (congrArg (fun t => Tree.fork t (.atom false)) h.1),List.mem_map.mpr ⟨_,h.2,rfl⟩⟩

private theorem computable_comparisonBytes {X : Type} [Primcodable X] {pos : X → List ℕ}
    (hp : Computable pos) : Computable (fun x => spelledTable (comparisonTable (pos x))) := by
  apply computable_spelled_literal (letter := fun _ => comparisonMark) (Computable.const _)
    (Computable.list_length.comp hp) ((Primrec.dom_finite (fun v => spelling (comparisonMark v))).to_comp.comp Computable.snd).to₂
  exact (primrec_spelling_numeral.to_comp.comp
    (primrec_maskValue.to_comp.comp (hp.comp Computable.fst) Computable.snd)).to₂

theorem computable_maskResultBytes {X : Type} [Primcodable X] {pos : X → List ℕ}
    (hp : Computable pos) : Computable (fun x => spelledTable (maskResultTable (pos x))) := by
  let f (u : List ℕ × List ℕ) := (u.1,2 :: u.2 ++ [0])
  have hf : Primrec f := Primrec.fst.pair (Primrec.list_cons.comp (Primrec.const 2)
    (Primrec.list_append.comp Primrec.snd (Primrec.const [0])))
  have c := (Primrec.list_map Primrec.id (hf.comp Primrec.snd).to₂).to_comp.comp (computable_comparisonBytes hp)
  apply c.of_eq
  intro x
  simp [f,maskResultTable,InterchangeROMTable.spelledTable,List.map_map,Function.comp_def]

def maskRowsCommand (rank : ℕ) (pos : List ℕ) :=
  alignedCommand rank (Series.natural 1) (RegisterTable.command (maskResultTable pos))

def maskRowsFactor (pos : List ℕ) : ℕ :=
  alignedFactor pos.length 1 (2*RegisterTable.cost (maskResultTable pos))

theorem maskRows_within (rank : ℕ) (pos : List ℕ) : CommonRegisters.Within 4 (maskRowsCommand rank pos) :=
  aligned_within _ _ (RegisterTable.within (by decide : 2 ≤ 4) _)

theorem effective_maskRowsCommand {X : Type} [Primcodable X] {rank : X → ℕ} {pos : X → List ℕ}
    (hr : Computable rank) (hp : Computable pos) :
    Effective ltr fun x => maskRowsCommand (rank x) (pos x) :=
  effective_aligned hr (fun _ => Series.natural 1) (Computable.const _)
    (RegisterTable.effective (computable_maskResultBytes hp))

set_option backward.isDefEq.respectTransparency false in
theorem computable_maskRowsFactor {X : Type} [Primcodable X] {pos : X → List ℕ} (hp : Computable pos) :
    Computable fun x => maskRowsFactor (pos x) := by
  have h : Primrec (fun v : ℕ × ℕ => alignedFactor v.1 1 (2*v.2)) :=
    primrec_alignedFactor Primrec.fst (Primrec.const 1)
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
  have c : Computable (fun x => RegisterTable.cost (maskResultTable (pos x))) :=
    computable_tableCost (t := fun x => maskResultTable (pos x)) (computable_maskResultBytes hp)
  let g (x : X) := ((pos x).length, RegisterTable.cost (maskResultTable (pos x)))
  have hg : Computable g := (Computable.list_length.comp hp).pair c
  have result := h.to_comp.comp hg
  exact result

open private rows_le_clock from OAI.Computability.NearSquareRoot.ScheduleRegisterLoomROM

/-- The designated existing input field supplies the row-count scaffold. -/
theorem maskRows_bounded {m : ℕ} {A : Type} (cols : Series (Fin m)) (rows : Series A)
    (k : Fin m) (v : A → Fin m → Ordering) (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let pos := cols.tab Fin.val
    let D := maskRowsFactor pos * (rows.count+1)
    BoundedFits env (maskRowsCommand (cols.explore.idxOf k) pos)
      (pile 0 (stripe cols (fun j => stripe rows fun a => comparisonMark (comparisonCode (v a j)))) r)
      (pile 0 (stripe (Series.natural 1) (fun _ => stripe rows fun a =>
        numeral (Raw.mask (fun j => decide (v a j = .gt))).val)) r) D (base+D) D := by
  let pos := cols.tab Fin.val
  let tab := maskResultTable pos
  let src (a : A) := comparisonMark ∘ comparisonCode ∘ v a
  let dst (a : A) (_ : Fin 1) := numeral (Raw.mask (fun j => decide (v a j = .gt))).val
  have pair (a : A) : RegisterLookup.read tab (stripe cols (src a)) = stripe (Series.natural 1) (dst a) ∧
      (stripe cols (src a),stripe (Series.natural 1) (dst a)) ∈ tab := maskResult_correct cols (v a)
  have vol (a : A) := rows_le_clock (pair a).2
  have letter {K : Type} (s : Series K) (f : K → Tree) (j : K) : (f j).count ≤ (stripe s f).count := by
    rw [stripe_simple]
    exact count_le_forest f (s.complete j)
  have run := aligned_linear cols (Series.natural 1) rows k src dst (RegisterTable.command tab)
    (2*RegisterTable.cost tab) 1 (by decide)
    (fun a j => by have h := letter cols (src a) j; have hsize := vol a; omega)
    (fun a j => by have h := letter (Series.natural 1) (dst a) j; have hsize := vol a; omega)
    (fun a env r base hd => by
      have one := RegisterTable.run_lookup _ _ _ (pair a).2 (pair a).1 env r
      have h := vol a
      exact (BoundedFits.of_fits one (cap := base+2*RegisterTable.cost tab) (depth := 2*RegisterTable.cost tab)
        (fun i => by have hj := hd.pile 0 (stripe cols (src a)) i; omega)
        (by omega)).mono (by omega) (by omega) (by omega)) env r base hr
  simpa only [maskRowsCommand,maskRowsFactor,Series.card,Series.count_natural,Nat.mul_one,src,dst,tab,pos,
    Function.comp_def] using run

/-- Return the bare mask stream for parking alongside the data bank. -/
def maskRowCommand (rank : ℕ) (pos : List ℕ) := (maskRowsCommand rank pos).join (cellCommand 0)

def maskRowFactor (pos : List ℕ) :=
  maskRowsFactor pos + 100 * (RegisterTable.cost (maskResultTable pos)+4) + 3

theorem maskRow_within (rank : ℕ) (pos : List ℕ) : CommonRegisters.Within 4 (maskRowCommand rank pos) :=
  ⟨maskRows_within _ _, RegisterSelect.within_mono (by decide : 3 ≤ 4) _ (cell_within _)⟩

theorem effective_maskRowCommand {X : Type} [Primcodable X] {rank : X → ℕ} {pos : X → List ℕ}
    (hr : Computable rank) (hp : Computable pos) :
    Effective ltr fun x => maskRowCommand (rank x) (pos x) :=
  (effective_maskRowsCommand hr hp).join (effective_const ltr (cellCommand 0))

theorem computable_maskRowFactor {X : Type} [Primcodable X] {pos : X → List ℕ} (hp : Computable pos) :
    Computable fun x => maskRowFactor (pos x) := by
  have cost : Computable fun x => RegisterTable.cost (maskResultTable (pos x)) :=
    computable_tableCost (t := fun x => maskResultTable (pos x)) (computable_maskResultBytes hp)
  exact Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp (computable_maskRowsFactor hp)
    (Primrec.nat_mul.to_comp.comp (Computable.const 100)
      (Primrec.nat_add.to_comp.comp cost (Computable.const 4)))) (Computable.const 3)

theorem maskRow_bounded {m : ℕ} {A : Type} (cols : Series (Fin m)) (rows : Series A)
    (k : Fin m) (v : A → Fin m → Ordering) (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let pos := cols.tab Fin.val
    let D := maskRowFactor pos * (rows.count+1)
    BoundedFits env (maskRowCommand (cols.explore.idxOf k) pos)
      (pile 0 (stripe cols (fun j => stripe rows fun a => comparisonMark (comparisonCode (v a j)))) r)
      (pile 0 (stripe rows fun a => numeral (Raw.mask (fun j => decide (v a j = .gt))).val) r)
      D (base+D) D := by
  let pos := cols.tab Fin.val
  let out (a : A) := numeral (Raw.mask (fun j => decide (v a j = .gt))).val
  let C := RegisterTable.cost (maskResultTable pos)
  let F := maskRowsFactor pos
  let V := rows.count+1
  let word := stripe rows out
  let bank := Tree.fork word (.atom false)
  have hx (a : A) : (out a).count ≤ C := by
    have z := rows_le_clock (maskResult_correct cols (v a)).2
    change _ + (Tree.fork (out a) (.atom false)).count + 1 ≤ C at z
    simp only [Tree.count] at z
    omega
  have vol := stripe_size rows out C hx
  have bankSize : bank.count ≤ (C+4)*V := by
    change (stripe rows out).count + 1 + 1 ≤ (C+4) * (rows.count+1)
    nlinarith
  have left := maskRows_bounded cols rows k v env r base hr
  have right := cell_fits id [word] 0 word rfl env r
  change Fits env (cellCommand 0) (pile 0 bank r) (pile 0 word r) (90*bank.count) at right
  let D := (F+100*(C+4)+3)*V
  have hV : 1 ≤ V := Nat.le_add_left 1 rows.count
  have resources : D = F*V+100*((C+4)*V)+3*V := by dsimp [D]; ring
  have hcap := BoundedFits.of_fits right (cap := base+D) (depth := D)
    (fun i => by have hj := hr.pile 0 bank i; omega) (by omega)
  have call := (left.mono le_rfl (cap' := base+D) (by change base+F*V ≤ _; omega)
    (depth' := F*V) le_rfl).join hcap (by omega)
  exact call.mono (by change F*V+90*bank.count+2 ≤ D; omega) le_rfl le_rfl

end InterchangeROMTable

end NearSquareRoot
end Computability
end OAI
