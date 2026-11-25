import Mathlib.Data.Fin.Tuple.Take
import OAI.ThreeFlat.Diagonal.HistoryAssembly
import OAI.ThreeFlat.Diagonal.MotifBinaryPacking

namespace OAI
/-! # Explicit boundary encoding and child wiring for a history stage

Each site keeps its externally owned input pins followed by the bits of its
incident half-ports in the actual bounded port order. At a join, the old
half-ports become private bits, concatenated by child. The parent half-ports
remain exposed. The local kernel consumes the two streams in that order.
-/

namespace ThreeFlat.Diagonal.HistoryContraction

open MotifBinaryPacking
open scoped BigOperators Classical

variable {S : Shape} {Pins F : Type*} [CommSemiring F]

structure PortLayout (S : Shape) (Pins : Type*) where
  count : S.Site → ℕ
  port : ∀ v, Fin (count v) ≃ S.graph.Port v
  width : S.Edge → ℕ
  binary : ∀ e, S.Label e ≃ (Fin (width e) → Bool)
  ext : S.Site → ℕ
  pin : ∀ v, Pins → Fin (ext v) → Bool

namespace PortLayout

variable (L : PortLayout S Pins)

def lengths (u : S.Site) (i : Fin (L.count u)) := L.width (L.port u i).1.1

def halfBits (u : S.Site) := ∑ i, L.lengths u i

def encode (u : S.Site) : S.Half u ≃ (Fin (L.halfBits u) → Bool) :=
  (Equiv.piCongrLeft (fun t : S.graph.Port u => S.Label t.1.1) (L.port u)).symm.trans <|
  (Equiv.piCongrRight (fun i => L.binary (L.port u i).1.1)).trans (flatten (L.lengths u))

def form : Form S Pins where
  width := fun v => L.ext v + L.halfBits v
  read := fun v pin b => Fin.append (L.pin v pin) (L.encode v b)

variable {R : Rewrite S F} {t : Fin R.count} (W : PortLayout (R.target t) Pins)
    (children : (R.target t).Site → ℕ) (ord : ∀ v, Fin (children v) ≃ {i // R.owner t i = v})

def oldWidths (v : (R.target t).Site) (i : Fin (children v)) := L.halfBits (ord v i).val

def hidden (v : (R.target t).Site) := ∑ i, L.oldWidths children ord v i

def decode (v : (R.target t).Site) : (Fin (L.hidden children ord v) → Bool) ≃
    ((i : {i // R.owner t i = v}) → S.Half i) :=
  (flatten (L.oldWidths children ord v)).symm.trans <|
  (Equiv.piCongrRight (fun i => (L.encode (ord v i).val).symm)).trans
    (Equiv.piCongrLeft (fun i : {i // R.owner t i = v} => S.Half i) (ord v))

private theorem decoded_at (v : (R.target t).Site) (g : Fin (L.hidden children ord v) → Bool)
    (i : Fin (children v)) (j : Fin (L.halfBits (ord v i).val)) :
    L.encode (ord v i).val (L.decode children ord v g (ord v i)) j = g (finSigmaFinEquiv ⟨i,j⟩) := by
  let f := (Equiv.piCongrLeft (fun a : {i // R.owner t i = v} => S.Half a) (ord v))
  let old (i : Fin (children v)) := (L.encode (ord v i).val).symm ((flatten (L.oldWidths children ord v)).symm g i)
  have hi := congrArg (fun q => q i) (f.symm_apply_apply old)
  change (L.decode children ord v g (ord v i)) = old i at hi
  rw [hi]
  unfold old
  exact congrFun ((L.encode (ord v i).val).apply_symm_apply ((flatten (L.oldWidths children ord v)).symm g i)) j

def kernelWire (v : (R.target t).Site) : Fin (L.hidden children ord v + W.halfBits v) →
    BitSource (L.hidden children ord v) (W.form.width v) :=
  Fin.append BitSource.hidden (fun i => .pin (Fin.natAdd (W.ext v) i))

def previousWire (v : (R.target t).Site) (i : Fin (children v))
    (lift : Fin (L.ext (ord v i).val) → Fin (W.ext v)) : Fin (L.form.width (ord v i).val) →
    BitSource (L.hidden children ord v) (W.form.width v) :=
  Fin.append (fun j => .pin ((lift j).castAdd (W.halfBits v)))
    (fun j => .hidden (finSigmaFinEquiv (n := L.oldWidths children ord v) ⟨i,j⟩))

private theorem kernel_read (v : (R.target t).Site) (g : Fin (L.hidden children ord v) → Bool)
    (pin : Pins) (b : (R.target t).Half v) :
    (fun j => (L.kernelWire W children ord v j).read g (W.form.read v pin b)) = Fin.append g (W.encode v b) := by
  funext j
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j <;>
    simp only [kernelWire,Fin.append_left,Fin.append_right,form,BitSource.read]

/-- Construct the full assembler with explicit pointer translation. The
caller supplies only a local kernel on its actual old and new boundary
words and the relocation of inherited external pins. -/
def stage (lift : ∀ v i, Fin (L.ext (ord v i).val) → Fin (W.ext v))
    (correct : ∀ v i j pin, W.pin v pin (lift v i j) = L.pin (ord v i).val pin j)
    (kernel : ∀ v, Tree F (L.hidden children ord v + W.halfBits v))
    (hK : ∀ v g b, (kernel v).compile.eval (Fin.append g (W.encode v b)) = R.kernel t v (L.decode children ord v g) b) :
    Stage R t L.form W.form where
  count := children
  child := ord
  hidden := L.hidden children ord
  decode := L.decode children ord
  rootWidth := fun v => L.hidden children ord v + W.halfBits v
  root := kernel
  rootWire := L.kernelWire W children ord
  childWire := fun v i => L.previousWire W children ord v i (lift v i)
  root_eq := by intro v g pin b; rw [kernel_read]; exact hK v g b
  read_eq := by
    intro v i g pin b j
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j
    · simp only [previousWire,form,Fin.append_left,BitSource.read,correct]
    · simp only [previousWire,form,Fin.append_right,BitSource.read,decoded_at]

/-- The inherited external pins occupy contiguous intervals in child order.
The interval of one child has length exactly its external support. -/
def inherit (L : PortLayout S Pins) (W : PortLayout (R.target t) Pins)
    (children : (R.target t).Site → ℕ) (ord : ∀ v, Fin (children v) ≃ {i // R.owner t i = v}) :
    PortLayout (R.target t) Pins :=
  {W with
    ext := fun v => ∑ i, L.ext (ord v i).val
    pin := fun v data => flatten (fun i => L.ext (ord v i).val) (fun i => L.pin (ord v i).val data)}

def inheritedIndex (v : (R.target t).Site) (i : Fin (children v)) (j : Fin (L.ext (ord v i).val)) :
    Fin ((L.inherit W children ord).ext v) := finSigmaFinEquiv ⟨i,j⟩

theorem inherited_pin (v : (R.target t).Site) (i : Fin (children v)) (j : Fin (L.ext (ord v i).val)) (data : Pins) :
    (L.inherit W children ord).pin v data (L.inheritedIndex W children ord v i j) = L.pin (ord v i).val data j := by
  let f (a : (i : Fin (children v)) × Fin (L.ext (ord v i).val)) := L.pin (ord v a.1).val data a.2
  exact congrArg f (finSigmaFinEquiv.symm_apply_apply ⟨i,j⟩)

theorem inherited_offset (v : (R.target t).Site) (i : Fin (children v)) (j : Fin (L.ext (ord v i).val)) :
    (L.inheritedIndex W children ord v i j).val =
      (∑ a : Fin i.val, L.ext (ord v (Fin.castLE i.isLt.le a)).val) + j.val := finSigmaFinEquiv_apply _

end PortLayout

/-- The numeric ordering of the dependent finite sum is precisely concatenation
of the children in ordinal order, including empty child pin arrays. -/
theorem flatten_finSigma_order {d : ℕ} {α : Type*} (n : Fin d→ℕ) (f : (i : Fin d)→Fin (n i)→α) :
    List.ofFn (fun k : Fin (∑ i,n i)=>let z:=finSigmaFinEquiv.symm k; f z.1 z.2)=
      (List.ofFn (fun i=>List.ofFn (f i))).flatten := by
  let rows:=List.ofFn (fun i=>List.ofFn (f i))
  have len : rows.flatten.length=∑ i,n i := by
    simp only [rows,List.length_flatten,List.map_ofFn,Function.comp_def,List.length_ofFn,List.sum_ofFn]
  have read (i : Fin d) (j : Fin (n i)) (h : (finSigmaFinEquiv ⟨i,j⟩).val<rows.flatten.length) :
      rows.flatten[(finSigmaFinEquiv ⟨i,j⟩).val]'h=f i j := by
    have rowFits : i.val<rows.length := by simp [rows]
    have split := congrArg List.flatten (List.take_append_drop i.val rows).symm
    rw [List.drop_eq_getElem_cons rowFits,List.flatten_append,List.flatten_cons] at split
    have atRow : rows[i.val]=List.ofFn (f i) := by simp [rows]
    rw [atRow] at split
    have offset : (rows.take i.val).flatten.length=∑ k : Fin i.val,n (Fin.castLE i.isLt.le k) := by
      rw [show rows.take i.val=List.ofFn (Fin.take i.val i.isLt.le (fun q=>List.ofFn (f q))) from
        (Fin.ofFn_take_eq_take_ofFn i.isLt.le _).symm]
      simp only [List.length_flatten,List.map_ofFn,Function.comp_def,Fin.take_apply,List.length_ofFn,List.sum_ofFn]
    have address : (finSigmaFinEquiv (n := n) ⟨i,j⟩).val = (rows.take i.val).flatten.length + j.val :=
      (finSigmaFinEquiv_apply ⟨i,j⟩).trans (congrArg (· + j.val) offset.symm)
    rw [List.getElem_of_eq split,List.getElem_append_right (by rw [address]; exact Nat.le_add_right ..)]
    have withinRow : (finSigmaFinEquiv (n := n) ⟨i,j⟩).val - (rows.take i.val).flatten.length = j.val := by
      rw [address,Nat.add_sub_cancel_left]
    simp only [withinRow]
    rw [List.getElem_append_left (by simp),List.getElem_ofFn]
  apply List.ext_getElem (by simpa only [List.length_ofFn] using len.symm)
  intro k hk hk'
  have hk₀ : k<∑ i,n i := by simpa only [List.length_ofFn] using hk
  let t : Fin (∑ i,n i) := ⟨k,hk₀⟩
  obtain ⟨⟨i,j⟩,eq⟩:=finSigmaFinEquiv.surjective t
  have pos : (finSigmaFinEquiv ⟨i,j⟩).val=k := congrArg Fin.val eq
  have val := read i j (pos.symm ▸ hk')
  have readAt : rows.flatten[k]'hk'=f i j := (getElem_congr_idx (c:=rows.flatten) (w:=hk') pos.symm).trans val
  have inv : finSigmaFinEquiv.symm t=⟨i,j⟩ := by rw [←eq,Equiv.symm_apply_apply]
  rw [List.getElem_ofFn]
  change f (finSigmaFinEquiv.symm t).1 (finSigmaFinEquiv.symm t).2=_
  exact (congrArg (fun a : (i : Fin d) × Fin (n i) => f a.1 a.2) inv).trans readAt.symm

end ThreeFlat.Diagonal.HistoryContraction

end OAI
