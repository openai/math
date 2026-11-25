import OAI.Computability.NearSquareRoot.InterchangeROMStageTableCoverage
import OAI.Computability.NearSquareRoot.InterchangeROMStageRows
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomROM

/-! # Execution of the ground rectangle matrices on packed physical rows -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStageTable

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  InterchangeROMStage InterchangeROMTable LoomRegisters Space

def bytes (c : Parameters) (t : Frame.Table) : SpellingTable :=
  spelledTable (matrixTable c.2.1 (expandRoles t.2.1 c.2.2.1).length (gateMatrix c t))

def command (c : Parameters) (t : Frame.Table) : Cmd :=
  romPayload 0 (expandRoles t.2.2 c.2.2.1).length (bytes c t)

theorem expandRoles_length (ts : List Role) (d : ℕ) : (expandRoles ts d).length = ts.length*d :=
  length_blocks ts d (fun a b => (a,b))

theorem command_eq (c : Parameters) (t : Frame.Table) :
    command c t = romPayload 0 (t.2.2.length*c.2.2.1) (spelledTable
      (matrixTable c.2.1 (t.2.1.length*c.2.2.1) (gateMatrix c t))) := by
  simp only [command,bytes,expandRoles_length]

theorem scalarOrder_count {f : Frame} (r : Frame.Realization f) (n lanes : ℕ) :
    (scalarOrder r n lanes).count = (f.bank n).length*lanes := by
  rw [← expandRoles_length,← scalarOrder_tab,Series.card]

def charge (c : Parameters) (t : Frame.Table) (recordCount width : ℕ) : ℕ :=
  romPayloadFactor (t.2.1.length*c.2.2.1) (t.2.2.length*c.2.2.1) (bytes c t) *
    (recordCount*(width+1)+1)

/-- A single label and a single lane supply the scaffold of every gate. -/
theorem gate_source_positive (f : Frame) (lanes : ℕ) (tag : Fin 5) (hl : 0 < f.labels)
    (hd : 0 < lanes) : 0 < (f.bank (inputBoundary tag)).length*lanes := by
  have h : InterchangeROMStage.label 0 ∈ f.labelsBank :=
    List.mem_map.mpr ⟨0,List.mem_range.mpr hl,rfl⟩
  have h' : InterchangeROMStage.label 0 ∈ f.bank (inputBoundary tag) := by
    fin_cases tag <;> simp [inputBoundary,Frame.bank,h]
  exact Nat.mul_pos (List.length_pos_of_mem h') hd

/-- Each address and each payload position has independent ground inputs.
The compiled table threads the whole matrix through both physical levels. -/
theorem packed_gate (c : Parameters) (r : Frame.Realization c.1) [Fact c.2.1.Prime] (tag : Fin 5)
    [Fintype (r.Boundary (inputBoundary tag))] {A : Type} {Y : A → Type}
    (addr : Series A) (pay : (a : A) → Series (Y a))
    (width : ℕ) (hw : ∀ a, (pay a).count ≤ width)
    (active : 0 < (c.1.bank (inputBoundary tag)).length*c.2.2.1)
    (x : (a : A) → Y a → r.Boundary (inputBoundary tag) → D (decode c) → ZMod c.2.1)
    (env : Env) (deck : Deck) (base : ℕ) (hbase : DeckCap base deck) :
    let n := inputBoundary tag
    let t := c.1.gate tag n
    let g := decode c
    let inp := scalarOrder r n c.2.2.1
    let out := scalarOrder r (n+1) c.2.2.1
    let u := stripe inp (fun z => stripe addr fun a => stripe (pay a) fun k => numeral (x a k z.1 z.2).val)
    let v := stripe out (fun z => stripe addr fun a => stripe (pay a) fun k =>
      numeral (gateNative r c.2.1 c.2.2.1 g.minor g.base g.query tag (x a k) z.1 z.2).val)
    let T := charge c t addr.count width
    BoundedFits env (command c t) (pile 0 u deck) (pile 0 v deck) T (base+T) T := by
  classical
  let n := inputBoundary tag
  let t := c.1.gate tag n
  let g := decode c
  let lanes := c.2.2.1
  let : DecidableEq (r.Boundary n × Fin lanes) := Classical.decEq _
  let : BEq (r.Boundary n × Fin lanes) := instBEqOfDecidableEq
  let inp := scalarOrder r n lanes
  let out := scalarOrder r (n+1) lanes
  have cntI : inp.count = t.2.1.length*lanes := scalarOrder_count r n lanes
  have cntO : out.count = t.2.2.length*lanes := scalarOrder_count r (n+1) lanes
  have pos : 0 < inp.explore.length := by change 0 < inp.count; exact cntI.symm ▸ active
  let k := inp.explore[0]'pos
  have idx : inp.explore.idxOf k = 0 := inp.nodup.idxOf_getElem 0 pos
  let table := matrixTable c.2.1 inp.count (gateMatrix c t)
  let v := fun a j (z : r.Boundary n × Fin lanes) => numeral (x a j z.1 z.2).val
  let w := fun a j (z : r.Boundary (n+1) × Fin lanes) =>
    numeral (gateNative r c.2.1 lanes g.minor g.base g.query tag (x a j) z.1 z.2).val
  have run := romLayout_bounded inp out k addr pay width hw v w table
    (fun a j => frame_gate_lookup c r tag (x a j)) env deck base hbase
  have eq : spelledTable table = bytes c t := by
    simp only [bytes,expandRoles_length,table,cntI,lanes]
  dsimp only at run ⊢
  rw [idx,cntI,cntO,eq] at run
  simpa only [command,expandRoles_length,charge] using run

/-- Serialization of an arbitrary bank agrees with the literal block ordering used
to build the source ranks of movement instructions. -/
theorem forest_blocks {f : Frame} (r : Frame.Realization f) (n lanes : ℕ) (x : Ground → Tree) :
    Task.forest id (blocks (f.bank n) lanes (fun a d => x (a,d))) =
      stripe (scalarOrder r n lanes) (fun a => x (slot r n lanes a)) := by
  have h : (expandRoles (f.bank n) lanes).map x =
      blocks (f.bank n) lanes (fun a d => x (a,d)) := by
    simp [expandRoles,blocks,List.map_flatMap,List.map_map,Function.comp_def]
  rw [← h,← scalarOrder_tab,stripe,Series.map_tab]
  rfl

/-- A header is parked during the local matrix operation and restored at exit.
The bound requires capacity only on the actual incoming deck. -/
theorem underHeader_bounded {c : Cmd} (header u v : Tree) (time : ℕ) (env : Env)
    (leaf : ∀ d b, DeckCap b d → Fits env c (pile 0 u d) (pile 0 v d) time)
    (deck : Deck) (base : ℕ) (hbase : DeckCap base deck) :
    let T := 84*header.count+time+11
    BoundedFits env (InterchangeROM.underHeader c) (pile 0 (.fork header u) deck)
      (pile 0 (.fork header v) deck) T (base+((Tree.fork header u).count+T)) T := by
  have mv := fits_move (i:=0) (j:=1) (u:=2) (by decide) (by decide) header env (pile 0 u deck)
  have back := fits_move (i:=1) (j:=0) (u:=2) (by decide) (by decide) header env (pile 0 v deck)
  rw [pile_comm 1 _ deck 0 _ (by decide)] at mv back
  have full : Fits env (InterchangeROM.underHeader c) (pile 0 (.fork header u) deck)
      (pile 0 (.fork header v) deck) (84*header.count+time+11) :=
    (fits_pair (mv.join ((leaf _ _ (hbase.pile 1 header)).join (back.join (fits_pack _ _ _ _ _))))).mono
      (by omega)
  exact BoundedFits.of_fits full (fun i => by have := hbase.pile 0 (Tree.fork header u) i; omega) le_rfl

/-- One rendered list of packed P192 row trees at a gate boundary. -/
def render {A : Type} {Y : A → Type} {p : ℕ} (c : Parameters) (n : ℕ)
    (addr : Series A) (pay : (a : A) → Series (Y a)) (v : Ground → (a : A) → Y a → ZMod p) :
    List Tree :=
  blocks (c.1.bank n) c.2.2.1 fun role d =>
    stripe addr fun a => stripe (pay a) fun k => numeral (v (role,d) a k).val

/-- Physical gate execution on the same block list used by every routed stage.
The specification for the new rows is tested at every address and payload position. -/
theorem raw_gate (c : Parameters) (r : Frame.Realization c.1) [Fact c.2.1.Prime] (tag : Fin 5)
    [Fintype (r.Boundary (inputBoundary tag))] {A : Type} {Y : A → Type}
    (addr : Series A) (pay : (a : A) → Series (Y a)) (width : ℕ) (hw : ∀ a, (pay a).count ≤ width)
    (active : 0 < (c.1.bank (inputBoundary tag)).length*c.2.2.1)
    (x y : Ground → (a : A) → Y a → ZMod c.2.1)
    (correct : ∀ (z : r.Boundary (inputBoundary tag+1) × Fin c.2.2.1) a k,
      let g := decode c
      gateNative r c.2.1 c.2.2.1 g.minor g.base g.query tag
        (fun v d => x (slot r (inputBoundary tag) c.2.2.1 (v,d)) a k) z.1 z.2 =
          y (slot r (inputBoundary tag+1) c.2.2.1 z) a k)
    (header : Tree) (env : Env) (deck : Deck) (base : ℕ) (hbase : DeckCap base deck) :
    let n := inputBoundary tag
    let t := c.1.gate tag n
    let input := InterchangeROM.packet header (render c n addr pay x)
    let output := InterchangeROM.packet header (render c (n+1) addr pay y)
    let T := 84*header.count + charge c t addr.count width + 11
    BoundedFits env (InterchangeROM.underHeader (command c t)) (pile 0 input deck) (pile 0 output deck)
      T (base+(input.count+T)) T := by
  let n := inputBoundary tag
  let lanes := c.2.2.1
  let g := decode c
  let X (a : A) (k : Y a) (v : r.Boundary n) (d : Fin lanes) := x (slot r n lanes (v,d)) a k
  apply underHeader_bounded _ _ _ _ _ _ deck base hbase
  intro d b hd
  have h := (packed_gate c r tag addr pay width hw active X env d b hd).fits
  let row (v : Ground → (a : A) → Y a → ZMod c.2.1) (z : Ground) :=
    stripe addr fun a => stripe (pay a) fun k => numeral (v z a k).val
  have left := forest_blocks r n lanes (row x)
  have right := forest_blocks r (n+1) lanes (row y)
  change Fits env _ (pile 0 (Task.forest id (blocks _ _ _)) d) (pile 0 (Task.forest id (blocks _ _ _)) d) _
  rw [left,right]
  have result (z : r.Boundary (n+1) × Fin lanes) :
      (stripe addr fun a => stripe (pay a) fun k =>
        numeral (gateNative r c.2.1 lanes g.minor g.base g.query tag (X a k) z.1 z.2).val) =
          row y (slot r (n+1) lanes z) := by
    unfold row
    congr 1
    funext a
    congr 1
    funext k
    exact congrArg (fun a : ZMod c.2.1 => numeral a.val) (correct z a k)
  have alt := congrArg (stripe (scalarOrder r (n+1) lanes)) (funext result)
  exact alt ▸ h

end InterchangeROMStageTable

namespace InterchangeROMStage.Frame.Realization

open IntegerMultiplication.Code IntegerMultiplication.Strip InterchangeROMStageTable

/-- Physical tree for the scalar lane bank at a native stage boundary. Its
serialized list is the boundary's enumeration followed by ascending lane indices. -/
noncomputable def Tape {f : Frame} (r : Realization f) (n lanes : ℕ)
    (x : r.Boundary n → Fin lanes → Tree) : Tree :=
  stripe (scalarOrder r n lanes) fun z => x z.1 z.2

theorem tape_eq_forest {f : Frame} (r : Realization f) (n lanes : ℕ)
    (x : r.Boundary n → Fin lanes → Tree) :
    r.Tape n lanes x = Task.forest id (((r.order n).explore.flatMap fun a =>
      (List.finRange lanes).map (Prod.mk a)).map fun z => x z.1 z.2) := rfl

end InterchangeROMStage.Frame.Realization

namespace InterchangeROMStageTable

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  InterchangeROMStage InterchangeROMTable LoomRegisters Space

/-- Execution of a table in native bank order, with its newly computed tape
specified directly by the corresponding native operator. -/
theorem raw_gate_typed (c : Parameters) (r : Frame.Realization c.1) [Fact c.2.1.Prime] (tag : Fin 5)
    [Fintype (r.Boundary (inputBoundary tag))] {A : Type} {Y : A → Type}
    (addr : Series A) (pay : (a : A) → Series (Y a)) (width : ℕ) (hw : ∀ a, (pay a).count ≤ width)
    (active : 0 < (c.1.bank (inputBoundary tag)).length*c.2.2.1)
    (x : (a : A) → Y a → r.Boundary (inputBoundary tag) → D (decode c) → ZMod c.2.1)
    (header : Tree) (env : Env) (deck : Deck) (base : ℕ) (hbase : DeckCap base deck) :
    let n := inputBoundary tag
    let t := c.1.gate tag n
    let g := decode c
    let input := Tree.fork header (r.Tape n c.2.2.1 fun z d =>
      stripe addr fun a => stripe (pay a) fun k => numeral (x a k z d).val)
    let y := fun a k => gateNative r c.2.1 c.2.2.1 g.minor g.base g.query tag (x a k)
    let output := Tree.fork header (r.Tape (n+1) c.2.2.1 fun z d =>
      stripe addr fun a => stripe (pay a) fun k => numeral (y a k z d).val)
    let T := 84*header.count+charge c t addr.count width+11
    BoundedFits env (InterchangeROM.underHeader (command c t)) (pile 0 input deck) (pile 0 output deck)
      T (base+(input.count+T)) T := by
  apply underHeader_bounded _ _ _ _ _ _ deck base hbase
  intro d b hd
  exact (packed_gate c r tag addr pay width hw active x env d b hd).fits

end InterchangeROMStageTable

end NearSquareRoot
end Computability
end OAI
