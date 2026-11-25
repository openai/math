import OAI.Computability.NearSquareRoot.CRTControlledWord
import OAI.Computability.NearSquareRoot.CRTControlledBenesInput

/-! # Uniformly charged preparation of the Beneš switch tables

A switch is located by a depth, the bits above it and the remaining bits below it.
Descend along those upper bits, recomputing only the requested child subtable. Subtables
never grow. This bounds the complete traversal by one polynomial with fixed exponent,
independently of depth. Enumerating all addresses and depths then gives all switch
decisions in both halves of the network.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes
open IntegerMultiplication.Code

private abbrev Key := List Bool
private abbrev Row := Key × Key
private abbrev Table := Labels (Bool × Key)

private theorem pairKeyEq : Poly (fun t : (Bool × Key) × (Bool × Key) => decide (t.1 = t.2)) := by
  let bEq : Bool × Bool → Bool := fun t => decide (t.1 = t.2)
  have b := (show Poly (fun t : (Bool × Key) × (Bool × Key) => (t.1.1,t.2.1)) by fun_prop).compose
    (Easy.finite bEq).poly
  have w := (show Poly (fun t : (Bool × Key) × (Bool × Key) => (t.1.2,t.2.2)) by fun_prop).compose
    easyWordEq.poly
  convert (b.pair w).compose (Easy.finite (fun t : Bool × Bool => t.1 && t.2)).poly using 1
  funext x
  by_cases h : x.1.1 = x.2.1 <;> by_cases k : x.1.2 = x.2.2 <;> simp [Prod.ext_iff,bEq,h,k]

private theorem rawLabels_poly : Poly rawLabels := by
  have cut : Poly (fun w : Key => (w.headD false,w.tail)) := easyWordHead.poly.pair easyWordTail.poly
  have R : Poly unconsRow := (Easy.fst.poly.compose cut).pair (Easy.snd.poly.compose cut)
  exact (Poly.maps _ R).compose (prepareControls_poly [] easyWordEq.poly)

private def pick (t : (Table × Bool) × Row) : RawTable :=
  bif decide (((t.2.1.headD false) ^^ (label t.1.1 (false,t.2.1.tail)).2) = t.1.2)
  then [(t.2.1.tail,t.2.2.tail)] else []

private theorem pick_poly : Poly pick := by
  let T := (Table × Bool) × Row
  have headCost := (show Poly (fun t : T => t.2.1) by fun_prop).compose easyWordHead.poly
  have leftTail := (show Poly (fun t : T => t.2.1) by fun_prop).compose easyWordTail.poly
  have rightTail := (show Poly (fun t : T => t.2.2) by fun_prop).compose easyWordTail.poly
  have port := (IntegerMultiplication.Code.Poly.const false).pair leftTail
  have c := (port.pair (show Poly (fun t : T => t.1.1) by fun_prop)).compose
    (label_poly (false,[]) pairKeyEq)
  have outcome := (headCost.pair c.sndCompose).compose (Easy.finite (fun t : Bool × Bool => t.1 ^^ t.2)).poly
  have ok := (outcome.pair (show Poly (fun t : T => t.1.2) by fun_prop)).compose
    (Easy.finite (fun t : Bool × Bool => decide (t.1=t.2))).poly
  exact Poly.choose ok (((leftTail.pair rightTail).pair (IntegerMultiplication.Code.Poly.const [])).compose Poly.cons)
    (IntegerMultiplication.Code.Poly.const [])

theorem childTable_poly : Poly (fun t : RawTable × Bool => childTable t.1 t.2) := by
  have pre := ((Easy.fst (X:=RawTable) (Y:=Bool)).poly.compose rawLabels_poly).pair (Easy.snd (X:=RawTable) (Y:=Bool)).poly
  have rows := ((pre.pair Easy.fst.poly).compose (Poly.push ([],false) ([],[]) pick_poly)).compose Easy.flatten.poly
  convert rows using 1
  funext t
  unfold childTable polyPush
  generalize rawLabels t.1 = L
  induction t.1 with
  | nil => rfl
  | cons w l ih =>
    by_cases h : (w.1.headD false ^^ (label L (false,w.1.tail)).2) = t.2
    · simpa only [List.filter_cons,ite_true,Bool.false_eq_true,ite_false,List.map_cons,List.flatten_cons,pick,h,decide_true,Bool.cond_true,
        List.cons_append,List.nil_append,List.cons.injEq,true_and] using congrArg (List.cons (w.1.tail,w.2.tail)) ih
    · simpa only [List.filter_cons,ite_true,Bool.false_eq_true,ite_false,List.map_cons,List.flatten_cons,pick,decide_eq_false h,Bool.cond_false,
        List.nil_append] using ih

private theorem bytes_tail (x : Key) : size x.tail ≤ size x := by
  cases x with
  | nil => rfl
  | cons a l => simp; omega

theorem size_childTable_le (t : RawTable) (b : Bool) : size (childTable t b) ≤ size t := by
  unfold childTable
  generalize rawLabels t = L
  induction t with
  | nil => rfl
  | cons row t ih =>
    by_cases h : (row.1.headD false ^^ (label L (false,row.1.tail)).2) = b
    · simp only [List.filter_cons,h,decide_true,ite_true, List.map_cons,size_cons,size_prod]
      have := bytes_tail row.1
      have := bytes_tail row.2
      omega
    · simp only [List.filter_cons,decide_eq_false h,Bool.false_eq_true,ite_false,size_cons]
      exact ih.trans (by omega)

def descend (t : RawTable) (path : Key) := path.foldl childTable t

theorem size_descend_le (t : RawTable) (path : Key) : size (descend t path) ≤ size t := by
  induction path generalizing t with
  | nil => rfl
  | cons b bits ih => exact (ih (childTable t b)).trans (size_childTable_le t b)

theorem descend_poly : Poly (fun x : Key × RawTable => descend x.2 x.1) := by
  apply Poly.fold_left childTable_poly 1 1
  intro x l _
  simpa [descend] using (size_descend_le x.2 l).trans (show size x.2 ≤ size x+1 by simp; omega)

/-- At the requested depth, read the input-side and output-side switches. -/
def decisions (input : (RawTable × Key) × Key) : Bool × Bool :=
  let L := rawLabels (descend input.1.1 input.1.2)
  ((label L (false,input.2)).2, (label L (true,input.2)).2)

theorem decisions_poly : Poly decisions := by
  let X := (RawTable × Key) × Key
  have T := ((show Poly (fun x : X => (x.1.2,x.1.1)) by fun_prop).compose descend_poly).compose rawLabels_poly
  have side (b : Bool) : Poly (fun x : X => (label (rawLabels (descend x.1.1 x.1.2)) (b,x.2)).2) :=
    ((((IntegerMultiplication.Code.Poly.const b).pair (show Poly (fun x : (RawTable × Key) × Key => x.2) from Easy.snd.poly)).pair T).compose
      (label_poly (false,[]) pairKeyEq)).sndCompose
  exact (side false).pair (side true)

/-- Full-address lookup row: the target at index `j` is skipped on both sides. -/
def switchRow (q : (RawTable × Tally) × Key) : Key × Bool × Bool :=
  (q.2, decisions ((q.1.1,q.2.take q.1.2.length), (q.2.drop q.1.2.length).tail))

private theorem switchRow_poly : Poly switchRow := by
  let X := (RawTable × Tally) × Key
  have cuts := (show Poly (fun q : X => (q.1.2,q.2)) by fun_prop).compose (easy_cut Easy.identity).poly
  exact (show Poly (fun q : (RawTable × Tally) × Key => q.2) from Easy.snd.poly).pair
    ((((show Poly (fun q : X => q.1.1) by fun_prop).pair cuts.fstCompose).pair
      (cuts.sndCompose.compose easyWordTail.poly)).compose decisions_poly)

/-- Tables for the two stages on axis `j` as a single list of address-indexed rows. -/
def switchLayer (inpt : RawTable × Tally) : List (Key × Bool × Bool) :=
  inpt.1.map fun row => switchRow (inpt,row.1)

private theorem switchLayer_poly : Poly switchLayer := by
  have h : Poly (fun x : (RawTable × Tally) × Row => switchRow (x.1,x.2.1)) :=
    (show Poly (fun x : (RawTable × Tally) × Row => (x.1,x.2.1)) by fun_prop).compose switchRow_poly
  exact (Poly.identity.pair Easy.fst.poly).compose (Poly.push ([],[]) ([],[]) h)

/-- Entries are in depth order with each stage in the supplied table's input-address
order. The first switch column is used in ascending depth, the second in reverse. -/
def generateTables (inpt : Tally × RawTable) : List (List (Key × Bool × Bool)) :=
  (Iter.lineup inpt.1).map fun j => switchLayer (inpt.2,j)

theorem generateTables_poly : Poly generateTables :=
  (Easy.snd.poly.pair (Easy.fst.poly.compose Iter.poly_line)).compose
    (Poly.push [] [] switchLayer_poly)

/-- All table-generation work, including the path traversals, fits a uniform polynomial
in the full address width when the local block has logarithmically many bits. -/
theorem generateTables_task {I : Type} (d k : I → ℕ) (t : I → RawTable)
    (p : ∀ i, Equiv.Perm (Word (d i))) (C : ℕ)
    (hd : ∀ i, d i ≤ C * Nat.clog 2 (2*k i)) (ht : ∀ i, RawRepresents (p i) (t i)) :
    Task.BT k (fun i => send (tally (d i),t i))
      (fun i => send (generateTables (tally (d i),t i))) :=
  representedCompiler_param d k t p C hd ht generateTables_poly

@[simp] theorem generateTables_length (D : Tally) (t : RawTable) :
    (generateTables (D,t)).length = D.length := by simp [generateTables]

@[simp] theorem switchLayer_length (t : RawTable) (j : Tally) :
    (switchLayer (t,j)).length = t.length := by simp [switchLayer]

theorem generatedLayer (t : RawTable) {d j : ℕ} (hj : j < d) :
    (generateTables (tally d,t))[j]? = some (switchLayer (t,tally j)) := by
  simp [generateTables,Iter.lineup,hj]

private theorem lookup_generated_rows {t : RawTable} {j : Tally} (L : RawTable) (x : Key)
    (hx : x ∈ L.map Prod.fst) :
    (L.map (fun r => switchRow ((t,j),r.1))).lookup x = some (switchRow ((t,j),x)).2 := by
  induction L with
  | nil => simp at hx
  | cons r l ih =>
    by_cases h : x = r.1
    · subst x; simp [switchRow]
    · have hb : (x == r.1) = false := by simpa using h
      have hx' := (List.mem_cons.mp (show x ∈ r.1::l.map Prod.fst from hx)).resolve_left h
      simpa only [List.map_cons,switchRow,List.lookup_cons,hb] using ih hx'

/-- Reading the actual table at any depth and occupied input address returns exactly
the two switch decisions of the corresponding residual subproblem. -/
theorem generated_lookup (t : RawTable) {d j : ℕ} (hj : j < d) (x : Key) (hx : x ∈ t.map Prod.fst) :
    ((generateTables (tally d,t))[j]?.bind (fun rows => rows.lookup x)) =
      some (switchRow ((t,tally j),x)).2 := by
  rw [generatedLayer t hj]
  exact lookup_generated_rows t x hx

/-- Reverse a routing table by interchanging the columns; the recursive splitter accepts
any complete row order. -/
def inverseTable (t : RawTable) : RawTable := t.map Prod.swap

theorem inverseTable_represents {d : ℕ} {p : Equiv.Perm (Word d)} {t : RawTable}
    (h : RawRepresents p t) : RawRepresents p.symm (inverseTable t) := by
  obtain ⟨ks,hn,hall,rfl⟩ := h
  refine ⟨ks.map p,hn.map p.injective,?_,?_⟩
  · intro x
    exact List.mem_map.mpr ⟨p.symm x,hall _,p.apply_symm_apply _⟩
  · simp [inverseTable,List.map_map,Function.comp_def]

theorem inverseTable_poly : Poly inverseTable := Poly.maps _ Easy.exchange.poly

/-- A uniform control setting selects either the supplied table or its inverse. -/
def generateDirected (x : Bool × (Tally × RawTable)) :=
  generateTables (x.2.1, bif x.1 then inverseTable x.2.2 else x.2.2)

theorem generateDirected_poly : Poly generateDirected := by
  let X := Bool × Tally × RawTable
  have tab := (show Poly (fun x : X => x.2.2) by fun_prop)
  have choose := Poly.choose (show Poly (fun x : X => x.1) from Easy.fst.poly)
    (tab.compose inverseTable_poly) tab
  exact ((show Poly (fun x : X => x.2.1) by fun_prop).pair choose).compose generateTables_poly

theorem generateDirected_task {I : Type} (d k : I → ℕ) (t : I → RawTable) (rev : I → Bool)
    (p : ∀ i, Equiv.Perm (Word (d i))) (C : ℕ)
    (hd : ∀ i, d i ≤ C * Nat.clog 2 (2*k i)) (ht : ∀ i, RawRepresents (p i) (t i)) :
    Task.BT k (fun i => send (rev i,tally (d i),t i))
      (fun i => send (generateDirected (rev i,tally (d i),t i))) := by
  apply Task.BT.mono (p := k) (t := fun i => 2^(d i))
  · apply generateDirected_poly.on
    refine ⟨2,9,fun i => ?_⟩
    obtain ⟨hlen, hr⟩ := represented_bounds (ht i)
    have hs := rawInput_size_bound (d i) (t i) hlen.le (fun r h => ⟨(hr r h).1.le,(hr r h).2.le⟩)
    change 1 + size (tally (d i),t i) + 1 ≤ _
    nlinarith [Nat.zero_le (2^(d i))]
  · exact blockPorts_poly d k C hd

end Benes

end NearSquareRoot
end Computability
end OAI
