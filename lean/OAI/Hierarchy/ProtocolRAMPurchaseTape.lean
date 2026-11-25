import OAI.Hierarchy.ProtocolRAMPurchaseOwners
import OAI.Hierarchy.ProtocolRAMPurchaseWalkCost
import OAI.Hierarchy.ProtocolRAMPurchaseGateColumns
import OAI.Hierarchy.ProtocolRAMPurchasePadding

namespace OAI
/-! # The sampler purchase tape from live CT rows

The controller inverts the current input-socket column, follows every padded
sequence of sampler choices, rejects repeated or missing tiles, and emits the
three physical NAND operand columns used by the purchase interpreter. Its ROM
and the two public directories depend only on sizes and bank locations.
-/

namespace Hierarchy.ProtocolRAM.PurchaseTape
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section

variable {w n m groups D h : ℕ} {G : Type*}

structure Plan (D : ℕ) where
  columns : ProtocolRAMPurchaseOwners.Columns
  neighbor : Fin D → Bank
  ownerScratch : ℕ
  directory : ℕ
  source : Bank
  gates : GateColumns.Directory
  work : ℕ
  first : ℕ
  packed : ℕ

abbrev count (n D h : ℕ) := (PurchaseDFS.layout n D h).length

def edge (s : Plan D) (d : Fin D) := ProtocolRAMPurchaseOwners.nextWord s.columns (s.neighbor d) .row

def paths (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (sampler : Fin m → Fin D → Option (Fin m)) (h : ℕ) :=
  (PurchaseDFS.layout n D h).map (PurchaseDFS.filled (ProtocolRAMPurchaseOwners.successor p encode sampler))

theorem rows_paths (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups)
    (sampler : Fin m → Fin D → Option (Fin m)) (h : ℕ) :
    List.ofFn (fun i : PurchaseDirectory.Index n D h => List.ofFn
      (PurchaseColumns.rowTile (ProtocolRAMPurchaseOwners.successor p enc sampler) i)) = paths p enc sampler h := by
  unfold paths
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_ofFn,List.getElem_map]
    rw [PurchaseDFS.filled_eq_state_rows]
    rfl

def code (s : Plan D) (w n groups m h : ℕ) : Procedure w :=
  ((ProtocolRAMPurchaseOwners.program w n groups m s.ownerScratch s.columns).seq
    (program w (PurchaseColumns.passes s.directory s.source.base n h (edge s)))).seq
      (ProtocolRAMPurchaseGateColumns.code w (count n D h) (h+1) s.source s.gates s.work s.packed)

def output (s : Plan D) (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups) (h : ℕ) (mem : Memory w) :=
  let owners := ProtocolRAMPurchaseOwners.image s.ownerScratch s.columns p enc mem
  let columns := result (PurchaseColumns.passes s.directory s.source.base n h (edge s)) owners
  ProtocolRAMPurchaseGateColumns.output (count n D h) (h+1) s.source s.gates s.work s.packed columns

def ticks (s : Plan D) (n groups m h : ℕ) :=
  (ProtocolRAMPurchaseOwners.work n groups m +
    clock (PurchaseColumns.passes s.directory s.source.base n h (edge s))) +
      clock (GateColumns.passes s.source s.gates s.work (ProtocolRAMPurchaseGateColumns.gates (count n D h) (h+1)) s.packed)

/-- Every side condition is an address/word bound on the public processor layout. -/
structure Fits (s : Plan D) (w n groups m h : ℕ) : Prop where
  owners : ProtocolRAMPurchaseOwners.Fits s.columns w n groups m s.ownerScratch
  rowRoom : n < 2^w
  degree : D ≤ 2^w
  wide : 0<w
  choices : ∀ j, (s.neighbor j).Fits w s.columns.owner.base
  ids : s.directory+(h+1)*PurchaseDirectory.span n D h ≤ s.columns.owner.base
  gateROM : s.gates.base+6*s.gates.stride ≤ s.columns.owner.base ∨
    (s.ownerScratch+2*n ≤ s.gates.base ∧ s.source.base+s.source.size ≤ s.gates.base)
  sourceAfter : s.columns.owner.base ≤ s.source.base
  fields : ∀ j, (PurchaseColumns.field s.directory n h (edge s) j).inputEnd ≤ s.source.base
  sourceCapacity : (h+1)*count n D h ≤ s.source.size
  sourceFit : s.source.Fits w s.packed
  gateFit : ∀ j, j<6 → (s.gates.bank j).Fits w s.packed
  target : s.packed+3*ProtocolRAMPurchaseGateColumns.gates (count n D h) (h+1) < 2^w

/-- Two fixed directories, the finite sampler tables, and the actual CT row
columns are all read from memory before the processor starts. -/
structure Loaded (s : Plan D) (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups)
    (sampler : Fin m → Fin D → Option (Fin m)) (h : ℕ) (mem : Memory w) : Prop where
  route : ProtocolRAMPurchaseOwners.Loaded s.columns p enc mem
  starts : PurchaseDirectory.Loaded s.directory n D h mem
  samplerColumns : ∀ j, Native.Resident (s.neighbor j) mem (fun o => ProtocolRAMPurchaseOwners.portCode (sampler o j))
  gateColumns : GateColumns.Mounted s.gates (ProtocolRAMPurchaseGateColumns.spec
    (R:=count n D h) (H:=h+1) (n+1) s.work s.first) mem


abbrev prefixCode (s : Plan D) (w n groups m h : ℕ) : Procedure w :=
  (ProtocolRAMPurchaseOwners.program w n groups m s.ownerScratch s.columns).seq
    (program w (PurchaseColumns.passes s.directory s.source.base n h (edge s)))

abbrev prefixOut (s : Plan D) (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups) (h : ℕ) (mem : Memory w) :=
  result (PurchaseColumns.passes s.directory s.source.base n h (edge s))
    (ProtocolRAMPurchaseOwners.image s.ownerScratch s.columns p enc mem)

abbrev prefixTicks (s : Plan D) (n groups m h : ℕ) :=
  ProtocolRAMPurchaseOwners.work n groups m + clock (PurchaseColumns.passes s.directory s.source.base n h (edge s))

private theorem columns_above {w : ℕ} (n : ℕ) (es : List Expr) (base : ℕ) (mem : Memory w)
    (a : ℕ) (late : base+es.length*n≤a) : result (Native.columns n base es) mem a=mem a := by
  induction es generalizing base mem with
  | nil => rfl
  | cons e es ih =>
    rw [List.length_cons,Nat.succ_mul] at late
    simp only [Native.columns,result]
    rw [ih (base+n) _ (by omega)]
    apply ProtocolRAMGeneratedWrite.frame_image
    right
    change base+n≤a
    omega

/-- The two native prefixes fill the actual tile rows required by `PurchaseStage.dispatch`,
while preserving the immutable descriptor tape and any earlier signed mark bank. -/
theorem columns_run (s : Plan D) (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups)
    (sampler : Fin m → Fin D → Option (Fin m)) (h : ℕ) (mem : Memory w)
    (size : Fits s w n groups m h) (input : Loaded s p enc sampler h mem) :
    let rows := PurchaseColumns.rowTile (h:=h) (ProtocolRAMPurchaseOwners.successor p enc sampler)
    let after := prefixOut s p enc h mem
    (prefixCode s w n groups m h).Exec mem after (prefixTicks s n groups m h) ∧
    ProtocolRAMPurchaseGateColumns.TileRows s.source rows after ∧
    GateColumns.Mounted s.gates (ProtocolRAMPurchaseGateColumns.spec (R:=count n D h) (H:=h+1) (n+1) s.work s.first) after ∧
    ∀ a < s.columns.owner.base, after a=mem a := by
  let choices := ProtocolRAMPurchaseOwners.successor p enc sampler
  let owners := ProtocolRAMPurchaseOwners.image s.ownerScratch s.columns p enc mem
  let rows := PurchaseColumns.rowTile (h:=h) choices
  let ps := PurchaseColumns.passes s.directory s.source.base n h (edge s)
  let after := result ps owners
  have r₁ : (ProtocolRAMPurchaseOwners.program w n groups m s.ownerScratch s.columns).Exec
      mem owners (ProtocolRAMPurchaseOwners.work n groups m) :=
    ProtocolRAMPurchaseOwners.run s.columns p enc mem size.owners input.route
  have preserve (a : ℕ) (ha : a < s.columns.owner.base) : owners a=mem a :=
    ProtocolRAMPurchaseOwners.below s.columns p enc mem size.owners a ha
  have directory := input.starts.of_frame (m':=owners) (fun a _ ha => preserve a (ha.trans_le size.ids))
  have next (r : Fin n) (d : Fin D) : (edge s d).eval owners (r.val:Word w) = (PurchaseWord.code (choices r d):Word w) := by
    have line := ProtocolRAMPurchaseOwners.nextWord_image s.columns (s.neighbor d) .row p enc
      (fun o=>sampler o d) mem size.owners input.route (input.samplerColumns d) (size.choices d) (r.val:Word w) r rfl
    calc
      _ = (ProtocolRAMPurchaseOwners.portCode (choices r d):Word w) := line
      _ = (PurchaseWord.code (choices r d):Word w) := by cases choices r d <;> rfl
  have cap := size.sourceCapacity
  have fit := size.sourceFit.2.2
  have target := size.target
  have sourceRoom : s.source.base+(h+1)*count n D h<2^w := by omega
  have ⟨r₂,read⟩ := PurchaseColumns.emit s.directory s.source.base (edge s) choices owners directory
    size.rowRoom size.degree next (fun j=>Expr.fits_of_inputEnd _ (size.fields j) (by omega)) sourceRoom
  have raw : ProtocolRAMPurchaseGateColumns.TileRows s.source rows after := by
    intro i j
    simpa only [Nat.add_assoc] using read i j
  have gateROM := GateColumns.mounted_of_frame s.gates _ input.gateColumns (m':=after) (by
    intro a lo hi
    rcases size.gateROM with early | ⟨lateScratch,lateSource⟩
    · have early := hi.trans_le early
      exact (result_below ps owners a (fun q hq =>
        (early.trans_le size.sourceAfter).trans_le (Native.columns_below _ q hq))).trans (preserve a early)
    · have above := columns_above (count n D h) (List.ofFn (PurchaseColumns.field s.directory n h (edge s)))
        s.source.base owners a (by simp only [List.length_ofFn]; omega)
      have own := size.owners.owner.2.2
      have bounded := size.owners.count
      exact above.trans (ProtocolRAMPurchaseOwners.frame s.ownerScratch s.columns p enc mem a
        (.inr (by omega)) (.inr (by omega))))
  exact ⟨r₁.then r₂,raw,gateROM,fun a early =>
    (result_below ps owners a (fun q hq =>
      (early.trans_le size.sourceAfter).trans_le (Native.columns_below _ q hq))).trans (preserve a early)⟩

/-- A single executable procedure builds the packed addresses of the literal
canonical path list. No permutation-dependent paths are supplied as advice. -/
theorem run (s : Plan D) (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups)
    (sampler : Fin m → Fin D → Option (Fin m)) (h : ℕ) (mem : Memory w)
    (size : Fits s w n groups m h) (input : Loaded s p enc sampler h mem) :
    (code s w n groups m h).Exec mem (output s p enc h mem) (ticks s n groups m h) ∧
    MarkTape.Packed s.packed (MarkTape.compilePaths (n+1) s.work s.first (paths p enc sampler h))
      (output s p enc h mem) := by
  let choices := ProtocolRAMPurchaseOwners.successor p enc sampler
  let rows := PurchaseColumns.rowTile (h:=h) choices
  let after := prefixOut s p enc h mem
  obtain ⟨prefixRun,raw,gateROM,_⟩ := columns_run s p enc sampler h mem size input
  obtain ⟨r₃,packed,_,_,_⟩ := ProtocolRAMPurchaseGateColumns.execute s.source s.gates s.work s.first s.packed
    rows after raw gateROM size.wide size.sourceCapacity size.sourceFit size.gateFit size.target
  refine ⟨prefixRun.then r₃, ?_⟩
  change MarkTape.Packed s.packed _
    (ProtocolRAMPurchaseGateColumns.output (count n D h) (h+1) s.source s.gates s.work s.packed after)
  simpa only [rows,choices,rows_paths] using packed

/-- The polynomial in the stage size is linear once the sampler degree and
chain length are fixed by the requested quantitative parameters. -/
theorem cost (s : Plan D) (n groups m h : ℕ) :
    ticks s n groups m h ≤ 15+6*(groups*m)+70*n +
      (4+(h+1)*(4+n*D^h*(2*PurchaseColumns.fieldBudget D h+4)) +
        (16+3*(n*D^h*(4*(h+1)+3))*64)) := by
  have dfs := PurchaseColumns.clock_bound s.directory s.source.base n h (edge s)
    (fun d => by simp [edge,ProtocolRAMPurchaseOwners.nextWord_work,Expr.work])
  have gates := GateColumns.ticks (ProtocolRAMPurchaseGateColumns.gates (count n D h) (h+1)) s.source s.gates s.work s.packed
  simp only [ProtocolRAMPurchaseGateColumns.gates,count,PurchaseDFS.length_layout] at gates
  simpa only [ticks,ProtocolRAMPurchaseGateColumns.gates,count,PurchaseDFS.length_layout,ProtocolRAMPurchaseOwners.work,Nat.add_assoc] using Nat.add_le_add_left (Nat.add_le_add dfs gates) (ProtocolRAMPurchaseOwners.work n groups m)

end
end Hierarchy.ProtocolRAM.PurchaseTape

end OAI
