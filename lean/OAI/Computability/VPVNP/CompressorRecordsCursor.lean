import OAI.Computability.VPVNP.CompressorRecordsCursorCapacity
import OAI.Computability.VPVNP.CompressorRecordsCursorWords
import OAI.Computability.VPVNP.CompressorRecordGreedyInit

/-!
# Level-zero records of the compressor

Six parallel columns are indexed by a base or actual port number. At either
granularity the outgoing column stores an incoming port, and the incoming
column gives the unique outgoing port. Two additional columns give the base
arc's displacement and the actual arc's width. Every cell in these columns
has a direct address in the current level. To query a width at an incoming
port, follow that port's incoming entry into the width column.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM CursorNetwork Compression CursorRAM

/-- A state-independent incidence directory for the native descriptor stages. -/
structure IncidenceDirectory (w : ℕ) where
  /-- Base address of the column mapping each outgoing base port to its incoming mate. -/
  baseOut : Word w
  /-- Base address of the inverse column mapping each incoming base port to its outgoing mate. -/
  baseIn : Word w
  /-- Base address of the lane-displacement column indexed by outgoing base port. -/
  shift : Word w
  /-- Base address of the column mapping each outgoing actual port to its incoming mate. -/
  actualOut : Word w
  /-- Base address of the inverse column mapping each incoming actual port to its outgoing
  mate. -/
  actualIn : Word w
  /-- Base address of the arc-width column indexed by outgoing actual port. -/
  width : Word w

namespace IncidenceDirectory

variable {w a l : ℕ}

/-- Encode a base port as its base-site number times the degree plus its slot. -/
def basePort (X : State a l) (e : X.Base × Fin (2^a)) : Word w :=
  encode w ((X.baseIndex e.1).val * 2^a + e.2.val)

/-- Encode an actual port by combining the base-site index, binary lane number, and slot in
that order. -/
def actualPort (X : State a l) (e : (X.Base × BitWord l) × Fin (2^a)) : Word w :=
  encode w (((X.baseIndex e.1.1).val * 2^l + (bitWordFinEquiv l e.1.2).val)*2^a + e.2.val)

/-- Complete base and actual incidence records of a state. -/
structure Represents (T : IncidenceDirectory w) (X : State a l) (m : Memory w) : Prop where
  baseOut : ∀ e, m (T.baseOut + basePort X e).val = basePort X (X.slots.base.target e)
  baseIn : ∀ e, m (T.baseIn + basePort X e).val = basePort X (X.slots.base.target.symm e)
  shift : ∀ e, m (T.shift + basePort X e).val = encode w (bitWordFinEquiv l (X.slots.displacement e)).val
  actualOut : ∀ e, m (T.actualOut + actualPort X e).val = actualPort X (X.slots.actualGraph.target e)
  actualIn : ∀ e, m (T.actualIn + actualPort X e).val = actualPort X (X.slots.actualGraph.target.symm e)
  width : ∀ e, m (T.width + actualPort X e).val = encode w (X.width ((e.1.1,e.2),e.1.2))

/-- Read the actual source width at any incoming slot in two direct probes. -/
theorem Represents.incomingWidth {T : IncidenceDirectory w} {X : State a l} {m : Memory w}
    (rep : T.Represents X m) (e : (X.Base × BitWord l) × Fin (2^a)) :
    let src := X.slots.actualGraph.target.symm e
    m (T.width + m (T.actualIn + actualPort X e).val).val =
      encode w (X.width ((src.1.1,src.2),src.1.2)) := by
  rw [rep.actualIn]; exact rep.width _

/-- Use these same base records in the greedy operand scans. -/
def greedyTables (T : IncidenceDirectory w) (a : ℕ) (labels zero : Word w) : Greedy.PortTables w :=
  ⟨encode w (2^a), T.baseOut, T.baseIn, T.shift, labels, zero⟩

theorem Represents.greedy {T : IncidenceDirectory w} {X : State a l} {m : Memory w}
    (rep : T.Represents X m) (labels zero : Word w)
    (hd : 2^a < 2^w) (hfit : Fintype.card X.Base * 2^a ≤ 2^w) :
    (T.greedyTables a labels zero).Represents X.slots.base X.baseIndex m where
  degree := Nat.mod_eq_of_lt hd
  fits := hfit
  vertices := (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)).trans hfit
  outgoing := rep.baseOut
  incoming := rep.baseIn

end IncidenceDirectory

namespace CursorRAM

variable {w b l a pad : ℕ} {S : Type} [Fintype S]

/-- A level-zero cursor coordinate and base bit string together with one port slot. -/
abbrev BasePort (b l a : ℕ) := (Fin (b+l) × BitWord b) × Fin (2^a)
/-- A level-zero base position refined by its lane bit string and a port slot. -/
abbrev ActualPort (b l a : ℕ) := ((Fin (b+l) × BitWord b) × BitWord l) × Fin (2^a)

/-- The loop counter enumerates all actual sources once. -/
def actualOrder (b l a : ℕ) : ActualPort b l a ≃ Fin (rowCount b l a) :=
  ((cursorActualIndex b l).prodCongr (Equiv.refl _)).trans finProdFinEquiv

/-- Number level-zero base ports consecutively in cursor-base order, with slots consecutive
inside each base position. -/
def baseOrder (b l a : ℕ) : BasePort b l a ≃ Fin ((b+l)*2^b*2^a) :=
  ((cursorBaseIndex b l).prodCongr (Equiv.refl _)).trans finProdFinEquiv

theorem actualOrder_val (e : ActualPort b l a) :
    (actualOrder b l a e).val = cursorActualSlotNumber e := by
  change e.2.val + 2^a * _ = _ * 2^a + e.2.val
  ac_rfl

theorem baseOrder_val (e : BasePort b l a) :
    (baseOrder b l a e).val = cursorBaseSlotNumber e := by
  change e.2.val + 2^a * _ = _ * 2^a + e.2.val
  ac_rfl

/-- The eleven initializer operands giving the degree, cursor dimension, base and lane radices,
arc width, and six incidence column bases. -/
def publicWords (w b l a W start : ℕ) : Fin 11 → Word w :=
  ![encode w (2^a), encode w (b+l), encode w (2^b), encode w (2^l), encode w W,
    encode w (start + 0*rowCount b l a), encode w (start + 1*rowCount b l a),
    encode w (start + 2*rowCount b l a), encode w (start + 3*rowCount b l a),
    encode w (start + 4*rowCount b l a), encode w (start + 5*rowCount b l a)]

/-- Lay out the six level-zero incidence columns at equally spaced addresses starting at the
supplied workspace location. -/
def directory (w b l a start : ℕ) : IncidenceDirectory w :=
  let p := publicWords w b l a 0 start
  ⟨p 5, p 6, p 7, p 8, p 9, p 10⟩

theorem publicWords_parameters (w b l a W start : ℕ) :
    Parameters (publicWords w b l a W start) b l a W := ⟨rfl,rfl,rfl,rfl,rfl⟩

variable (hD : 1 < b+l) (hd : 2+pad = 2^a) (bits : S → ℕ)
local notation "X₀" => cursorState (cursorCoordinateLabels b l) hD hd bits
local notation "W₀" => ∑ s, bits s

/-- The level-zero record for an actual outgoing port, encoding its base source and target,
displacement, actual target, and width. -/
noncomputable def typedRow (e : ActualPort b l a) : Row (Word w) :=
  let B := IncidenceDirectory.basePort (w := w) X₀
  let A := IncidenceDirectory.actualPort (w := w) X₀
  let src := (e.1.1,e.2)
  ⟨B src, B ((X₀).slots.base.target src), encode w (bitWordFinEquiv l ((X₀).slots.displacement src)).val,
    A ((X₀).slots.actualGraph.target e), encode w ((X₀).width (src,e.1.2))⟩

private theorem baseNumber (e : BasePort b l a) :
    IncidenceDirectory.basePort X₀ e = encode w (baseOrder b l a e).val := by
  rw [baseOrder_val]; rfl

private theorem actualNumber (e : ActualPort b l a) :
    IncidenceDirectory.actualPort X₀ e = encode w (actualOrder b l a e).val := by
  rw [actualOrder_val, cursorActualSlotNumber, cursorActualIndex_val]; rfl

/-- The actual emitted six values use the slot permutation of the typed state. -/
theorem visit_row (start : ℕ) (fit : rowCount b l a < 2^w) (e : ActualPort b l a) :
    wordRow (publicWords w b l a W₀ start) (encode w (actualOrder b l a e).val) =
      typedRow hD hd bits e := by
  rcases e with ⟨⟨⟨j,x⟩,g⟩,s⟩
  rw [actualOrder_val, cursorActualSlotNumber, cursorActualIndex_val, cursorBaseIndex_val,
    wordRow_exact (publicWords_parameters ..) hD (by omega) fit j.isLt
      (bitWordFinEquiv b x).isLt (bitWordFinEquiv l g).isLt s.isLt]
  dsimp only [typedRow]
  simp only [Row.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (encode w) (congrArg (fun v => v*2^a+s.val) (cursorBaseIndex_val j x))).symm
  · exact ((baseNumber hD hd bits _).trans (congrArg (encode w)
      ((baseOrder_val _).trans (cursorBaseTargetNumber hD hd bits j x s)))).symm
  · exact (congrArg (encode w) (cursorDisplacementNumber hD hd bits j x s)).symm
  · exact ((actualNumber hD hd bits _).trans (congrArg (encode w)
      ((actualOrder_val _).trans (cursorActualTargetNumber hD hd bits j x g s)))).symm
  · exact (congrArg (encode w) (cursorSlotWidth hD hd bits j x g s)).symm

/-- Decode a row within a given column. The base arrays occupy prefixes of their
reserved regions. The words after each base prefix are immaterial. -/
private noncomputable def column (t : Fin 6) (i : ℕ) : Word w :=
  haveI : NeZero (b+l) := ⟨by omega⟩
  haveI : NeZero (rowCount b l a) := ⟨by unfold rowCount; positivity⟩
  let e := (baseOrder b l a).symm (Fin.ofNat _ i)
  let z := (actualOrder b l a).symm (Fin.ofNat _ i)
  ![IncidenceDirectory.basePort X₀ ((X₀).slots.base.target e),
    IncidenceDirectory.basePort X₀ ((X₀).slots.base.target.symm e),
    encode w (bitWordFinEquiv l ((X₀).slots.displacement e)).val,
    IncidenceDirectory.actualPort X₀ ((X₀).slots.actualGraph.target z),
    IncidenceDirectory.actualPort X₀ ((X₀).slots.actualGraph.target.symm z),
    encode w ((X₀).width ((z.1.1,z.2),z.1.2))] t

/-- Interpret an external address relative to the level's reserved region. -/
private noncomputable def specification (start : ℕ) (addr : ℕ) : Word w :=
  column hD hd bits (Fin.ofNat _ ((addr-start)/rowCount b l a)) ((addr-start)%rowCount b l a)

private theorem baseRows_le (b l a : ℕ) : (b+l)*2^b*2^a ≤ rowCount b l a :=
  Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos l))

private theorem atColumn {start : ℕ} (room : start + 6*rowCount b l a ≤ 2^w)
    (t : Fin 6) {i : ℕ} (hi : i < rowCount b l a) :
    specification (w := w) hD hd bits start ((encode w (start + t.val * rowCount b l a) + encode w i).val) =
      column hD hd bits t i := by
  let n := rowCount b l a
  have haddr : start + t.val * n + i < 2^w := by
    have h : t.val*n+i < 6*n := packed_lt t.isLt hi
    change start+6*n ≤ 2^w at room
    omega
  have hpre : start + t.val*n < 2^w := by omega
  have hival : i < 2^w := by omega
  change column hD hd bits (Fin.ofNat _ ((_ - start)/n)) ((_ - start)%n) = _
  rw [Fin.val_add, Fin.val_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt hpre, Nat.mod_eq_of_lt hival,
    Nat.mod_eq_of_lt haddr, Nat.add_assoc, Nat.add_sub_cancel_left, Nat.mul_add_mod_of_lt hi,
    Nat.mul_comm t.val n, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, Nat.add_zero]
  have ht : Fin.ofNat 6 t.val = t := Fin.ext (Nat.mod_eq_of_lt t.isLt)
  rw [ht]

private theorem baseCol {start : ℕ} (room : start + 6*rowCount b l a ≤ 2^w)
    (t : Fin 6) (e : BasePort b l a) :
    specification (w := w) hD hd bits start
      ((encode w (start + t.val * rowCount b l a) + IncidenceDirectory.basePort X₀ e).val) =
      column hD hd bits t (baseOrder b l a e).val := by
  rw [baseNumber]
  exact atColumn hD hd bits room t ((baseOrder b l a e).isLt.trans_le (baseRows_le ..))

private theorem actualCol {start : ℕ} (room : start + 6*rowCount b l a ≤ 2^w)
    (t : Fin 6) (e : ActualPort b l a) :
    specification (w := w) hD hd bits start
      ((encode w (start + t.val * rowCount b l a) + IncidenceDirectory.actualPort X₀ e).val) =
      column hD hd bits t (actualOrder b l a e).val := by
  rw [actualNumber]; exact atColumn hD hd bits room t (actualOrder b l a e).isLt

private theorem directory_spec {start : ℕ} (room : start + 6*rowCount b l a ≤ 2^w) :
    (directory w b l a start).Represents X₀ (specification hD hd bits start) := by
  constructor
  all_goals intro e
  case baseOut =>
    apply (baseCol hD hd bits room 0 e).trans
    simp [column]
    erw [Equiv.symm_apply_apply]
  case baseIn =>
    apply (baseCol hD hd bits room 1 e).trans
    simp [column]
    erw [Equiv.symm_apply_apply]
  case shift =>
    apply (baseCol hD hd bits room 2 e).trans
    simp [column]
    erw [Equiv.symm_apply_apply]
  case actualOut =>
    apply (actualCol hD hd bits room 3 e).trans
    simp [column]
    erw [Equiv.symm_apply_apply]
  case actualIn =>
    apply (actualCol hD hd bits room 4 e).trans
    simp [column]
    erw [Equiv.symm_apply_apply]
  case width =>
    apply (actualCol hD hd bits room 5 e).trans
    simp [column]
    erw [Equiv.symm_apply_apply]

private noncomputable def typedWrites (T : IncidenceDirectory w) (e : ActualPort b l a) : List (Word w × Word w) :=
  let r := typedRow (w := w) hD hd bits e
  let src := IncidenceDirectory.actualPort (w := w) X₀ e
  [(T.baseOut+r.sourceBase,r.targetBase), (T.baseIn+r.targetBase,r.sourceBase),
   (T.shift+r.sourceBase,r.displacement), (T.actualOut+src,r.targetActual),
   (T.actualIn+r.targetActual,src), (T.width+src,r.width)]

private theorem rowWrites_typed (start : ℕ) (fit : rowCount b l a < 2^w) (e : ActualPort b l a) :
    rowWrites (publicWords w b l a W₀ start) (actualOrder b l a e).val =
      typedWrites hD hd bits (directory w b l a start) e := by
  dsimp only [rowWrites]
  rw [visit_row hD hd bits start fit e]
  dsimp only [typedWrites]
  rw [actualNumber hD hd bits e]
  rfl

private theorem written_correct {T : IncidenceDirectory w} {m : Memory w} (rep : T.Represents X₀ m)
    (e : ActualPort b l a) (v : Word w × Word w) (hv : v ∈ typedWrites hD hd bits T e) :
    m v.1.val = v.2 := by
  simp only [typedWrites, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact rep.baseOut _
  · exact (rep.baseIn _).trans (congrArg (IncidenceDirectory.basePort X₀)
      ((X₀).slots.base.target.symm_apply_apply _))
  · exact rep.shift _
  · exact rep.actualOut _
  · exact (rep.actualIn _).trans (congrArg (IncidenceDirectory.actualPort X₀)
      ((X₀).slots.actualGraph.target.symm_apply_apply e))
  · exact rep.width _

private theorem complete_of_writes (T : IncidenceDirectory w) (m : Memory w)
    (h : ∀ e v, v ∈ typedWrites hD hd bits T e → m v.1.val = v.2) : T.Represents X₀ m := by
  have atIndex (e : ActualPort b l a) (i : Fin 6) := h e
    ((typedWrites hD hd bits T e).get i) (List.get_mem ..)
  constructor
  · intro e; exact atIndex ((e.1,0),e.2) 0
  · intro e
    let z := (X₀).slots.base.target.symm e
    have he := atIndex ((z.1,0),z.2) 1
    change m (T.baseIn+IncidenceDirectory.basePort X₀ ((X₀).slots.base.target z)).val =
      IncidenceDirectory.basePort X₀ z at he
    rwa [show (X₀).slots.base.target z = e from (X₀).slots.base.target.apply_symm_apply e] at he
  · intro e; exact atIndex ((e.1,0),e.2) 2
  · intro e; exact atIndex e 3
  · intro e
    let z := (X₀).slots.actualGraph.target.symm e
    have he := atIndex z 4
    change m (T.actualIn+IncidenceDirectory.actualPort X₀ ((X₀).slots.actualGraph.target z)).val =
      IncidenceDirectory.actualPort X₀ z at he
    rwa [show (X₀).slots.actualGraph.target z = e from (X₀).slots.actualGraph.target.apply_symm_apply e] at he
  · intro e; exact atIndex e 5

open PrimedStackRAM in
/-- From arbitrary memory, the fixed finite program initializes the graph directory of
the typed compressor. It visits every actual outgoing slot and accounts for six probes
plus one call. The full incoming columns follow from bijectivity of the slot matchings. -/
theorem initialize_cursor {start : ℕ} (room : start + 6*rowCount b l a ≤ 2^w)
    (widthFits : W₀ < 2^w) (m : Memory w) :
    let p := publicWords w b l a W₀ start
    let n := rowCount b l a
    let M := (template visit 0).instantiate w p
    let rs := scanReports p 0 n
    let mem := after m (eventLog rs)
    let T := directory w b l a start
    runSegment M.program (1+visit.length) (some (encode w 0)) m (List.replicate n []) = some rs ∧
    T.Represents X₀ mem ∧
    (∀ e : ActualPort b l a, (mem (T.width + IncidenceDirectory.actualPort X₀ e).val).val =
      (X₀).width ((e.1.1,e.2),e.1.2)) ∧
    rs.length = n ∧ (∀ r ∈ rs, r.events.length = visit.length ∧ countProbes r.events = 6) ∧
    RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) rs = 7*n ∧
    (∀ addr, ¬ Touches p 0 n addr → mem addr = m addr) := by
  intro p n M rs mem T
  let spec := specification (w := w) hD hd bits start
  have fit : n < 2^w := by
    have hp : 0 < n := by dsimp [n, rowCount]; positivity
    change start+6*n ≤ 2^w at room
    omega
  have correct := written_correct hD hd bits (directory_spec hD hd bits room)
  have typed (e : ActualPort b l a) : rowWrites p (actualOrder b l a e).val =
      typedWrites hD hd bits T e := rowWrites_typed hD hd bits start fit e
  have agree (i : ℕ) (_ : 0 ≤ i) (hi : i < 0+n) (av) (hv : av ∈ rowWrites p i) :
      spec av.1.val = av.2 := by
    let u : Fin n := ⟨i,by omega⟩
    let e := (actualOrder b l a).symm u
    have he : (actualOrder b l a e).val = i := congrArg Fin.val ((actualOrder b l a).apply_symm_apply u)
    exact correct e av (by rwa [← he, typed] at hv)
  obtain ⟨out, hout, _, _, hfinal, hkeep⟩ := scan_run p 0 n m spec agree
  have hnative := scan_native p 0 n m
  obtain rfl : out = rs := Option.some.inj (hout.symm.trans hnative)
  have hrep : T.Represents X₀ mem := by
    apply complete_of_writes hD hd bits T mem
    intro e v hv
    have hmem := (typed e).symm ▸ hv
    have htouch : Touches p 0 n v.1.val :=
      ⟨(actualOrder b l a e).val, Nat.zero_le _, by rw [Nat.zero_add]; exact (actualOrder b l a e).isLt,
       v,hmem,rfl⟩
    exact (hfinal _ htouch).trans (correct e v hv)
  refine ⟨hnative,hrep,?_,scanReports_length ..,scanReports_work p 0 n,scan_cost ..,hkeep⟩
  rintro ⟨⟨⟨j,x⟩,g⟩,i⟩
  apply (congrArg Fin.val (hrep.width (((j,x),g),i))).trans
  apply Nat.mod_eq_of_lt
  change (X₀).width (((j,x),i),g) < _
  erw [cursorSlotWidth hD hd bits j x g i]
  split <;> omega

/-- Linear cost in the Section 12 position count at fixed dyadic degree. -/
theorem initialization_cost (p : Fin 11 → Word w) :
    RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) (scanReports p 0 (rowCount b l a)) =
      (7*2^a) * (2^(b+l)*(b+l)) := by
  rw [scan_cost, rowCount, pow_add]; ring

open CursorBounds CursorRouting Filter PrimedStackRAM in
/-- At all sufficiently large input lengths the native initialization constructs the
complete Section 12 directory. The same threshold covers every partition of the virtual
address into a contiguous base block and lane block. -/
theorem eventually_initialize (B a pad : ℕ) (hB : 1 ≤ B) (hd : 2+pad = 2^a)
    {start : ℕ → ℕ} (hs : PolynomiallyBounded start) :
    ∀ᶠ n : ℕ in atTop, ∀ b l, b+l = virtualBits B n → ∃ hD : 1 < b+l,
      let w := wordBits B n
      let widths : RAMSystem (b+l) → ℕ := ramFieldBits (virtualBucket n) w
      let X := cursorState (cursorCoordinateLabels b l) hD hd widths
      let p := publicWords w b l a (initialWidth B n) (start n)
      let N := rowCount b l a
      let M := (template visit 0).instantiate w p
      let rs := scanReports p 0 N
      ∀ m : Memory w,
        runSegment M.program (1+visit.length) (some (encode w 0)) m (List.replicate N []) = some rs ∧
        (directory w b l a (start n)).Represents X (after m (eventLog rs)) ∧
        RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) rs =
          (7*2^a)*initialPositions B n ∧
        (∀ r ∈ probeRecords (start n) rs, RecordFitsWord r) := by
  filter_upwards [eventually_cursorCapacity B a hB hs] with n h
  intro b l he
  obtain ⟨hD, hroom, hw, hclock⟩ := h b l he
  refine ⟨hD, ?_⟩
  intro w widths X p N M rs m
  have hwidth : (∑ s, widths s) = initialWidth B n := by
    dsimp only [widths, w, initialWidth]
    rw [he]
  have hi := initialize_cursor hD hd widths hroom (hwidth ▸ hw) m
  dsimp only at hi
  rw [hwidth] at hi
  refine ⟨hi.1,hi.2.1,?_,fun _ hr ↦ scan_probeRecords_fitsWord p hclock hr⟩
  change RAMBuckets.cost _ (scanReports p 0 (rowCount b l a)) = _
  rw [scan_cost, rowCount_eq_positions he]
  ring

end CursorRAM

end CompressorRecords

end VPVNP
end Computability
end OAI
