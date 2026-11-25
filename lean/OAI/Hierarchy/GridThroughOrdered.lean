import OAI.Hierarchy.GridThrough
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Numeric rail addresses and a single pass over the catalyst settings

The fixed address blocks depend only on the public lengths. The first block
contains the two port bits of every rail passage. The second contains two
center bits per rail. An idle rail's center bits are forced to zero. Thus
padding contributes one assignment over every field. -/

namespace Hierarchy.GridThrough.Ordered
open UniversalGrid
open scoped BigOperators

variable {k n p r : ℕ} {width : Fin k → ℕ}

/-- Low bit is the side of the rail. -/
def sides {a : ℕ} : (Fin a × Bool) ≃ Fin (a*2) :=
  ((Equiv.refl (Fin a)).prodCongr finTwoEquiv.symm).trans finProdFinEquiv

abbrev RawHidden (r n : ℕ) := (Fin r × Fin (n+1) × Bool) ⊕ (Fin r × Bool)
abbrev hiddenCount (r n : ℕ) := r*((n+1)*2) + r*2

/-- Rail-major, then longitudinal position, then side. The center block
follows all port bits and has the same order as the external endpoints. -/
def hiddenCode : RawHidden r n ≃ Fin (hiddenCount r n) :=
  (Equiv.sumCongr (((Equiv.refl (Fin r)).prodCongr sides).trans finProdFinEquiv) sides).trans
    finSumFinEquiv

theorem exterior_number (e : Fin r) (b : Bool) :
    (sides (e,b)).val = b.toNat + 2*e.val := by cases b <;> rfl

theorem port_number (e : Fin r) (t : Fin (n+1)) (b : Bool) :
    (hiddenCode (.inl (e,t,b))).val =
      (b.toNat + 2*t.val) + ((n+1)*2)*e.val := by cases b <;> rfl

theorem center_number (e : Fin r) (b : Bool) :
    (hiddenCode (n:=n) (.inr (e,b))).val =
      r*((n+1)*2) + (b.toNat + 2*e.val) := by cases b <;> rfl

abbrev Addr (r n : ℕ) := Address (Fin r) (hiddenCount r n)

def port (e : Fin r) (t : Fin (n+1)) (b : Bool) : Addr r n := .inl (hiddenCode (.inl (e,t,b)))
def center (e : Fin r) (b : Bool) : Addr r n := .inl (hiddenCode (.inr (e,b)))

/-- Iterate the actual catalyst wires, including directions of unequal width. -/
def wireList (w : Fin k → ℕ) : List (Catalyst.Wire w) :=
  (List.finRange k).flatMap fun j => List.ofFn (fun i : Fin (w j) => ⟨j,i⟩)

theorem wireList_mem (w : Fin k → ℕ) (z : Catalyst.Wire w) : z ∈ wireList w := by
  rcases z with ⟨j,i⟩
  exact List.mem_flatMap.mpr ⟨j,List.mem_finRange j,List.mem_ofFn.mpr ⟨i,rfl⟩⟩

@[simp] theorem wireList_length (w : Fin k → ℕ) : (wireList w).length = ∑ j, w j := by
  simp [wireList,List.length_flatMap,← List.ofFn_eq_map,List.sum_ofFn]

variable (P : Program (Fin r) n p width)

def passage (c : Cell k n) (w : Catalyst.Wire width) : Fin (r*(n+1)) :=
  finProdFinEquiv (P.pass c w,c (P.direction (P.pass c w)))

/-- Exactly one write request per selected catalyst wire of each cell. -/
def requests : List (Fin (r*(n+1))) :=
  let wires := wireList width
  (List.finRange ((n+1)^k)).flatMap fun i => wires.map (passage P (finFunctionFinEquiv.symm i))

theorem requests_length : (requests P).length = (n+1)^k * ∑ j, width j := by
  simp [requests,List.length_flatMap]

theorem mem_requests (e : Fin r) (t : Fin (n+1)) :
    finProdFinEquiv (e,t) ∈ requests P ↔ P.Selected e t := by
  constructor
  · intro entry
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp entry
    obtain ⟨w,_,hw⟩ := List.mem_map.mp hi
    let c : Cell k n := finFunctionFinEquiv.symm i
    have pair : (P.pass c w,c (P.direction (P.pass c w))) = (e,t) := finProdFinEquiv.injective hw
    have rail : P.pass c w = e := congrArg Prod.fst pair
    have axis : c (P.direction e) = t := by simpa [rail] using congrArg Prod.snd pair
    have onLine : P.railCell e t = c := by
      simpa only [Program.railCell,rail,axis] using P.pass_line c w
    exact ⟨w,by rw [onLine]; exact rail⟩
  · rintro ⟨w,hw⟩
    let c := P.railCell e t
    refine List.mem_flatMap.mpr ⟨finFunctionFinEquiv c,List.mem_finRange _,?_⟩
    refine List.mem_map.mpr ⟨w,wireList_mem _ _,?_⟩
    rw [Equiv.symm_apply_apply]
    change finProdFinEquiv (P.pass (P.railCell e t) w,
      P.railCell e t (P.direction (P.pass (P.railCell e t) w))) = _
    rw [hw]
    simp only [Program.railCell,GridLens.cellOnRail_axis]

/-- A mutable vector in the executable implementation. The fold consumes the
old vector at each write. Membership is used only in its specification. -/
def mark {m : ℕ} (zs : List (Fin m)) (v : Vector Bool m) : Vector Bool m :=
  zs.foldl (fun a i => a.set i.val true i.isLt) v

theorem mark_get {m : ℕ} (zs : List (Fin m)) (v : Vector Bool m) (i : Fin m) :
    (mark zs v)[i.val] = true ↔ i ∈ zs ∨ v[i.val] = true := by
  induction zs generalizing v with
  | nil => simp [mark]
  | cons j js ih =>
    change (mark js (v.set j.val true j.isLt))[i.val] = true ↔ _
    rw [ih]
    by_cases eq : j = i
    · subst j; simp
    · have ne : j.val ≠ i.val := fun h => eq (Fin.ext h)
      simp [ne,Ne.symm eq]

def marks := mark (requests P) (Vector.replicate (r*(n+1)) false)

theorem marked (e : Fin r) (t : Fin (n+1)) :
    (marks P)[(finProdFinEquiv (e,t)).val] = true ↔ P.Selected e t := by
  exact (mark_get (requests P) (Vector.replicate _ false) (finProdFinEquiv (e,t))).trans (by
    rw [mem_requests]; simp)

abbrev Candidate (r n : ℕ) :=
  (Fin r × Bool) ⊕ (Fin r × Fin n) ⊕ (Fin r × Fin (n+1)) ⊕ (Fin r × Bool)
abbrev edgeCount (r n : ℕ) := r*2 + (r*n + (r*(n+1) + r*2))

def addCode {A B : Type} {s t : ℕ} (a : A ≃ Fin s) (b : B ≃ Fin t) :
    (A ⊕ B) ≃ Fin (s+t) := (Equiv.sumCongr a b).trans finSumFinEquiv

def candidateCode : Candidate r n ≃ Fin (edgeCount r n) :=
  addCode sides (addCode finProdFinEquiv (addCode finProdFinEquiv sides))

def zeroAddr : Addr r n := .inr (.inr false)

/-- Test one catalog entry. Every candidate costs one vector lookup or one
touch lookup. Inactive through slots emit a trivial equality. A missing
touch instead uses its center test to pin the padded bit. -/
def edge (used : Vector Bool (r*(n+1))) : Candidate r n → Addr r n × Addr r n
  | .inl (e,false) => (.inr (.inl (e,false)),port e 0 false)
  | .inl (e,true) => (port e (Fin.last n) true,.inr (.inl (e,true)))
  | .inr (.inl (e,t)) => (port e t.castSucc true,port e t.succ false)
  | .inr (.inr (.inl (e,t))) =>
    if P.touch e = some t ∨ used[(finProdFinEquiv (e,t)).val] = true then (zeroAddr,zeroAddr)
    else (port e t false,port e t true)
  | .inr (.inr (.inr (e,b))) =>
    match P.touch e with
    | none => (center e b,zeroAddr)
    | some t => (port e t b,center e b)

def sourcePin (read : Cell k n → Fin p → (Touch P.touch × Bool) ⊕ Bool) (c : Cell k n) : Catalyst.Port p width → Addr r n
  | .inl i => (read c i).elim (fun u => center u.1.val.1 u.2) (fun b => .inr (.inr b))
  | .inr (w,b) => port (P.pass c w) (c (P.direction (P.pass c w))) b

/-- Fixed numeric program under any supplied selector setting. The compiler
builds the shared mark vector once before emitting its ordered test list. -/
def emit (read : Cell k n → Fin p → (Touch P.touch × Bool) ⊕ Bool) : Wiring (Fin r) (Catalyst.Port p width) ((n+1)^k) :=
  let used := marks P
  { internal := hiddenCount r n
    pin := fun i => sourcePin P read (finFunctionFinEquiv.symm i)
    equal := List.ofFn (fun i => edge P used (candidateCode.symm i)) }

abbrev pin := sourcePin P P.data
def wiring := emit P P.data

theorem emit_eq (read : Cell k n → Fin p → (Touch P.touch × Bool) ⊕ Bool)
    (correct : read = P.data) : emit P read = wiring P := by subst read; rfl

@[simp] theorem wiring_count : (wiring P).equal.length = edgeCount r n := List.length_ofFn

/-- Count the numeric operations that visit topology records: initialized flag
slots, writes, emitted test slots, data pins and the two ports of every
catalyst request. Counts are independent of tick table coefficients. -/
theorem topology_count :
    r*(n+1) + (requests P).length + (wiring P).equal.length +
        (n+1)^k*p + 2*(requests P).length =
      r*(3*(n+1)+3) + (n+1)^k*(p+3*∑ j, width j) := by
  rw [requests_length,wiring_count]
  unfold edgeCount
  ring

/-- A table of local pin assignments needs one entry per pin and two writes
per rail. This resolves the inverse of the assigned pin destination by its
numeric address without searching for the owner at read time. -/
def dataCode : (Cell k n × Fin p) ≃ Fin (((n+1)^k)*p) :=
  (finFunctionFinEquiv.prodCongr (Equiv.refl (Fin p))).trans finProdFinEquiv

variable {d q : ℕ}

def endpoints (A : PinAssignment (Fin r) k n q d) : List (Touch A.touch × Bool) :=
  List.ofFn (fun i : Fin (r*2) =>
    let z := sides.symm i
    (⟨(z.1,(A.tick z.1).1 (A.direction z.1)),rfl⟩,z.2))

private theorem endpoints_mem (A : PinAssignment (Fin r) k n q d) (u : Touch A.touch × Bool) :
    u ∈ endpoints A := by
  refine List.mem_ofFn.mpr ⟨sides (u.1.val.1,u.2),?_⟩
  simp only [Equiv.symm_apply_apply]
  exact Prod.ext (Subtype.ext (Prod.ext rfl (Option.some.inj u.1.property))) rfl

private def scatter {U : Type} {m : ℕ} (dest : U → Fin m) (us : List U) (v : Vector (Option U) m) :=
  us.foldl (fun table u => table.set (dest u).val (some u) (dest u).isLt) v

private theorem scatter_preserve {U : Type} {m : ℕ} (dest : U ↪ Fin m) (us : List U)
    (v : Vector (Option U) m) (u : U) (h : v[(dest u).val] = some u) :
    (scatter dest us v)[(dest u).val] = some u := by
  induction us generalizing v with
  | nil => exact h
  | cons z zs ih =>
    change (scatter dest zs (v.set (dest z).val (some z) (dest z).isLt))[(dest u).val] = some u
    apply ih
    by_cases same : z = u
    · subst z; simp
    · have ne : (dest z).val ≠ (dest u).val := fun eq => same (dest.injective (Fin.ext eq))
      simpa [Vector.getElem_set,ne] using h

private theorem scatter_fills {U : Type} {m : ℕ} (dest : U ↪ Fin m) (us : List U)
    (v : Vector (Option U) m) (u : U) (h : u ∈ us) :
    (scatter dest us v)[(dest u).val] = some u := by
  induction us generalizing v with
  | nil => simp at h
  | cons z zs ih =>
    change (scatter dest zs (v.set (dest z).val (some z) (dest z).isLt))[(dest u).val] = some u
    rcases List.mem_cons.mp h with rfl | tail
    · apply scatter_preserve
      simp
    · exact ih _ tail

private theorem scatter_sound {U : Type} {m : ℕ} (dest : U → Fin m) (us : List U)
    (v : Vector (Option U) m) (sound : ∀ i : Fin m, ∀ u, v[i.val] = some u → dest u = i)
    (i : Fin m) (u : U) (h : (scatter dest us v)[i.val] = some u) : dest u = i := by
  induction us generalizing v with
  | nil => exact sound i u h
  | cons z zs ih =>
    change (scatter dest zs (v.set (dest z).val (some z) (dest z).isLt))[i.val] = some u at h
    refine ih _ ?_ h
    intro j a ha
    by_cases eq : dest z = j
    · subst j
      have za : z = a := by simpa using ha
      rw [za]
    · have ne : (dest z).val ≠ j.val := fun hv => eq (Fin.ext hv)
      exact sound j a (by simpa [Vector.getElem_set,ne] using ha)

private def slotDest (A : PinAssignment (Fin r) k n q d) :
    (Touch A.touch × Bool) ↪ Fin (((n+1)^k)*(q*d)) where
  toFun u := dataCode ((A.tick u.1.val.1).1,
    finProdFinEquiv ((A.tick u.1.val.1).2,A.slot (u.1.val.1,u.2)))
  inj' _ _ eq := A.dest.injective (dataCode.injective eq)

def dataTable (A : PinAssignment (Fin r) k n q d) :=
  scatter (slotDest A) (endpoints A) (Vector.replicate (((n+1)^k)*(q*d)) none)

def sparseData (A : PinAssignment (Fin r) k n q d) :
    Cell k n → Fin (q*d) → (Touch A.touch × Bool) ⊕ Bool :=
  let table := dataTable A
  fun c i => (table[(dataCode (c,i)).val]).elim (.inr (A.literal (c,i))) Sum.inl

theorem sparseData_eq (A : PinAssignment (Fin r) k n q d) : sparseData A = A.data := by
  funext c i
  change ((dataTable A)[(dataCode (c,i)).val]).elim _ _ = pinSource A.dest A.literal (c,i)
  cases val : (dataTable A)[(dataCode (c,i)).val] with
  | none =>
    apply (pinSource_unused ..).symm
    intro u eq
    have full := scatter_fills (slotDest A) (endpoints A)
      (Vector.replicate (((n+1)^k)*(q*d)) none) u (endpoints_mem A u)
    have addr : slotDest A u = dataCode (c,i) := congrArg dataCode eq
    change (dataTable A)[(slotDest A u).val] = some u at full
    have transport := congrArg (fun j : Fin (((n+1)^k)*(q*d)) => (dataTable A)[j.val]'j.isLt) addr
    have impossible : some u = none := full.symm.trans (transport.trans val)
    cases impossible
  | some u =>
    apply ((pinSource_inl ..).2 ?_).symm
    apply dataCode.injective
    exact scatter_sound (slotDest A) (endpoints A)
      (Vector.replicate (((n+1)^k)*(q*d)) none) (by simp) _ _ val

theorem dataTable_visits (A : PinAssignment (Fin r) k n q d) :
    (dataTable A).toArray.size + (endpoints A).length = ((n+1)^k)*(q*d) + r*2 := by
  simp [endpoints]

private def unpad (v : Bits (hiddenCount r n)) : P.Hidden → Bool
  | .inl z => v (hiddenCode (.inl z))
  | .inr (u,b) => v (hiddenCode (.inr (u.val.1,b)))

private def Good (v : Bits (hiddenCount r n)) : Prop :=
  ∀ e b, P.touch e = none → v (hiddenCode (.inr (e,b))) = false

private def expand (h : P.Hidden → Bool) (i : Fin (hiddenCount r n)) : Bool :=
  (hiddenCode.symm i : RawHidden r n).elim (fun z => h (.inl z)) (fun z =>
    (P.touch z.1).pelim false (fun t ht => h (.inr (⟨(z.1,t),ht⟩,z.2))))

private theorem expand_center (h : P.Hidden → Bool) (e : Fin r) (b : Bool) :
    expand P h (hiddenCode (.inr (e,b))) =
      (P.touch e).pelim false (fun t ht => h (.inr (⟨(e,t),ht⟩,b))) := by simp [expand]

private theorem expand_good (h : P.Hidden → Bool) : Good P (expand P h) := by
  intro e b ht
  exact (expand_center P h e b).trans (Option.pelim_none' ht)

private def assignments : {v : Bits (hiddenCount r n) // Good P v} ≃ (P.Hidden → Bool) where
  toFun v := unpad P v.val
  invFun h := ⟨expand P h, expand_good P h⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    obtain ⟨raw,rfl⟩ := hiddenCode.surjective i
    rcases raw with z | ⟨e,b⟩
    · simp [expand,unpad]
    · change expand P (unpad P v.val) (hiddenCode (.inr (e,b))) = _
      rw [expand_center]
      rcases Option.eq_none_or_eq_some (P.touch e) with ht | ⟨t,ht⟩
      · exact (Option.pelim_none' ht).trans (v.property e b ht).symm
      · exact Option.pelim_some' ht
  right_inv h := by
    funext z
    rcases z with u | ⟨⟨⟨e,t⟩,ht⟩,b⟩
    · simp [unpad,expand]
    · change expand P h (hiddenCode (.inr (e,b))) = _
      rw [expand_center,Option.pelim_some' ht]

private def Test (x : GridDiagonal.Pins (Fin r)) (v : Bits (hiddenCount r n))
    (z : Candidate r n) := bit x v (edge P (marks P) z).1 = bit x v (edge P (marks P) z).2

private theorem all_tests (x : GridDiagonal.Pins (Fin r)) (v : Bits (hiddenCount r n)) :
    (∀ uv ∈ (wiring P).equal, bit x v uv.1 = bit x v uv.2) ↔
    Good P v ∧ ∀ z, P.typedEdge x (unpad P v) z := by
  have catalog : (∀ uv ∈ (wiring P).equal, bit x v uv.1 = bit x v uv.2) ↔ ∀ z, Test P x v z := by
    refine ⟨fun ok z => ok _ (List.mem_ofFn.mpr ⟨candidateCode z,congrArg (edge P (marks P)) (candidateCode.symm_apply_apply z)⟩), ?_⟩
    intro ok uv mem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    exact ok _
  rw [catalog]
  constructor
  · intro ok
    constructor
    · intro e b ht
      simpa [Test,edge,ht,center,zeroAddr,bit] using ok (.inr (.inr (.inr (e,b))))
    · rintro (⟨e,b⟩ | ⟨e,t⟩ | ⟨⟨e,t⟩,unt,sel⟩ | ⟨⟨⟨e,t⟩,ht⟩,b⟩)
      · cases b with
        | false => exact ok (.inl (e,false))
        | true => exact ok (.inl (e,true))
      · exact ok (.inr (.inl (e,t)))
      · have skip := mt (marked P e t).1 sel
        have no : ¬(P.touch e = some t ∨ (marks P)[(finProdFinEquiv (e,t)).val] = true) :=
          fun h => h.elim unt skip
        simpa only [Test,edge,ite_eq_right no,bit,port,Program.typedEdge,unpad,Sum.elim_inl] using
          ok (.inr (.inr (.inl (e,t))))
      · simpa [Test,edge,ht,bit,port,center,Program.typedEdge,unpad] using
          ok (.inr (.inr (.inr (e,b))))
  · rintro ⟨good,ok⟩ (⟨e,b⟩ | ⟨e,t⟩ | ⟨e,t⟩ | ⟨e,b⟩)
    · cases b with
      | false => exact ok (.inl (e,false))
      | true => exact ok (.inl (e,true))
    · exact ok (.inr (.inl (e,t)))
    · by_cases inactive : P.touch e = some t ∨ (marks P)[(finProdFinEquiv (e,t)).val] = true
      · simp only [Test,edge,ite_eq_left inactive]
      · have unt : P.touch e ≠ some t := fun h => inactive (.inl h)
        have sel : ¬P.Selected e t := fun h => inactive (.inr ((marked P e t).2 h))
        simpa only [Test,edge,ite_eq_right inactive,port,bit,Program.typedEdge,unpad,Sum.elim_inl] using
          ok (.inr (.inr (.inl ⟨(e,t),unt,sel⟩)))
    · cases ht : P.touch e with
      | none =>
        simpa [Test,edge,ht,center,zeroAddr,bit] using good e b ht
      | some t =>
        simpa [Test,edge,ht,port,center,bit,Program.typedEdge,unpad] using
          ok (.inr (.inr (.inr (⟨(e,t),ht⟩,b))))

private theorem bit_pin (x : GridDiagonal.Pins (Fin r)) (v : Bits (hiddenCount r n))
    (c : Cell k n) (j : Catalyst.Port p width) :
    bit x v (pin P c j) = P.typedPin (unpad P v) c j := by
  rcases j with i | ⟨w,b⟩
  · cases h : P.data c i <;> simp [pin,sourcePin,Program.typedPin,h,unpad,bit,center]
  · rfl

private theorem sum_good {A F : Type*} [Fintype A] [AddCommMonoid F]
    (keep : A → Prop) [DecidablePred keep] (f : A → F) :
    (∑ a, if keep a then f a else 0) = ∑ a : {a // keep a}, f a.val := by
  classical
  rw [←Finset.sum_subtype (Finset.univ.filter keep) (fun _ => by simp) f,Finset.sum_filter]

set_option maxHeartbeats 900000
open scoped Classical

private noncomputable def typedWeight {F : Type*} [Field F]
    (f : (Catalyst.Port p width → Bool) → F) (x : GridDiagonal.Pins (Fin r)) (h : P.Hidden → Bool) : F :=
  if ∀ z, P.typedEdge x h z then ∏ c, f (P.typedPin h c) else 0

private theorem summand {F : Type*} [Field F] (f : (Catalyst.Port p width → Bool) → F)
    (x : GridDiagonal.Pins (Fin r)) (v : Bits (hiddenCount r n)) :
    (@ite F (∀ uv ∈ (wiring P).equal, bit x v uv.1 = bit x v uv.2)
      (List.decidableBAll (fun uv => bit x v uv.1 = bit x v uv.2) (wiring P).equal)
      (∏ i : Fin ((n+1)^k), f (fun j => bit x v ((wiring P).pin i j))) 0) =
      if Good P v then typedWeight P f x (unpad P v) else 0 := by
  classical
  have checked := all_tests P x v
  by_cases good : Good P v
  · rw [ite_eq_left good,typedWeight]
    by_cases ok : ∀ z, P.typedEdge x (unpad P v) z
    · rw [ite_eq_left (checked.2 ⟨good,ok⟩),ite_eq_left ok]
      calc
        _ = ∏ i : Fin ((n+1)^k), f (P.typedPin (unpad P v) (finFunctionFinEquiv.symm i)) := by
          apply Finset.prod_congr rfl
          intro i _
          apply congrArg f
          funext j
          exact bit_pin P x v (finFunctionFinEquiv.symm i) j
        _ = _ := (finFunctionFinEquiv (m:=n+1) (n:=k)).symm.prod_comp
          (fun c : Cell k n => f (P.typedPin (unpad P v) c))
    · rw [ite_eq_right (fun h => ok (checked.1 h).2),ite_eq_right ok]
  · rw [ite_eq_right good,ite_eq_right (fun h => good (checked.1 h).1)]

private theorem typedWeight_sum {F : Type*} [Field F] (f : (Catalyst.Port p width → Bool) → F)
    (x : GridDiagonal.Pins (Fin r)) : (∑ h : P.Hidden → Bool, typedWeight P f x h) = P.typedEval f x := by
  unfold Program.typedEval
  apply Finset.sum_congr
  · ext h; simp only [Finset.mem_univ]
  · intro h _
    unfold typedWeight
    by_cases ok : ∀ z, P.typedEdge x h z
    · simp only [ite_eq_left ok]
    · simp only [ite_eq_right ok]

/-- Replacing every ideal table by the same arbitrary table preserves the
numeric implementation. Each center bit pinned to zero admits exactly one
extension of the typed assignment. -/
theorem eval {F : Type*} [Field F] (f : (Catalyst.Port p width → Bool) → F)
    (x : GridDiagonal.Pins (Fin r)) : (wiring P).eval f x = P.wiring.eval f x := by
  classical
  rw [P.eval_typed]
  calc
    (wiring P).eval f x = ∑ v : Bits (hiddenCount r n),
        if Good P v then typedWeight P f x (unpad P v) else 0 := Finset.sum_congr rfl (fun v _ => summand P f x v)
    _ = ∑ v : {v // Good P v}, typedWeight P f x (unpad P v.val) := sum_good _ _
    _ = ∑ h : P.Hidden → Bool, typedWeight P f x h := (assignments P).sum_comp (typedWeight P f x)
    _ = P.typedEval f x := typedWeight_sum P f x


end Hierarchy.GridThrough.Ordered

end OAI
