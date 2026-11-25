import OAI.Hierarchy.DescentSIMDLookup
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import Mathlib.Data.Finset.Sort

namespace OAI
/-! # Short shared serial numbers for actual cable grains

A resident contains one entry per incident cable grain in physical cable
order. Both ends compute the same serial by counting earlier occurrences of
their own short neighbor slot. A loop appears once in this directory, while
its two signed incidence slots remain distinct in the census.
-/
namespace Hierarchy.DescentSharedCableNames
open DescentSIMDLookup
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {H : Type} [DecidableEq H] {n D cap : ℕ}

structure Ends (H : Type) (n : ℕ) where
  src : Fin n→H
  dst : Fin n→H

namespace Ends
variable (B : Ends H n)

def incident (h : H) := Finset.univ.filter fun e=>B.src e=h ∨ B.dst e=h
def parallel (h v : H) := Finset.univ.filter fun e=>
  (B.src e=h ∧ B.dst e=v) ∨ (B.dst e=h ∧ B.src e=v)
def peer (h : H) (e : Fin n) := if B.src e=h then B.dst e else B.src e

theorem parallel_symm (h v : H) : B.parallel h v=B.parallel v h := by
  ext q
  simp only [parallel,Finset.mem_filter,Finset.mem_univ,true_and]
  tauto

theorem mem_parallel (h v : H) (e : Fin n) : e∈B.parallel h v ↔ e∈B.incident h ∧ B.peer h e=v := by
  simp only [parallel,incident,Finset.mem_filter,Finset.mem_univ,true_and,peer]
  by_cases isSrc : B.src e=h <;> simp [isSrc]; grind

def earlier (h v : H) (e : Fin n) := (B.parallel h v).filter (·<e)
def serial (h v : H) (e : Fin n) := (B.earlier h v e).card

theorem both_ends (e : Fin n) : B.serial (B.src e) (B.dst e) e = B.serial (B.dst e) (B.src e) e := by
  simp only [serial,earlier,B.parallel_symm (B.src e) (B.dst e)]

theorem strict {h v : H} {e f : Fin n} (same : e∈B.parallel h v) (less : e<f) :
    B.serial h v e<B.serial h v f := by
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (show B.earlier h v e⊆B.earlier h v f from fun j hj=>by
    obtain ⟨old,early⟩:=Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨old,early.trans less⟩)).2
  exact ⟨e,Finset.mem_filter.mpr ⟨same,less⟩,by simp [earlier]⟩

theorem distinguish {h v : H} {e f : Fin n} (ep : e∈B.parallel h v) (fp : f∈B.parallel h v)
    (s : B.serial h v e=B.serial h v f) : e=f := by
  rcases lt_trichotomy e f with le|eq|ge
  · exact False.elim ((B.strict ep le).ne s)
  · exact eq
  · exact False.elim ((B.strict fp ge).ne s.symm)

/-- The physical resident row only transports the number of the neighbor in
its own actually purchased roster. Distinct present neighbors have distinct
short values. -/
structure Neighbors (D : ℕ) where
  slot : ∀h, ↥(B.incident h)→Fin D
  same : ∀h e f,slot h e=slot h f ↔ B.peer h e.val=B.peer h f.val

/-- Sorted local position, also a compact address for rewrites which must
preserve old cable chronology. -/
def ordinal (h : H) := ((B.incident h).orderIsoOfFin rfl).symm

def position (fit : ∀h,(B.incident h).card≤cap) (h : H) : ↥(B.incident h) ↪ Fin cap :=
  (B.ordinal h).toEquiv.toEmbedding.trans (Fin.castLEEmb (fit h))

theorem position_lt (fit : ∀h,(B.incident h).card≤cap) (h : H) (e f : ↥(B.incident h)) :
    B.position fit h e<B.position fit h f ↔ e.val<f.val := (B.ordinal h).lt_iff_lt

/-- Each live record is one short roster slot plus a presence bit. The actual
global cable ordinal has no field in this packed table. -/
def panel (N : B.Neighbors D) (_fit : ∀h,(B.incident h).card≤cap) (h : H) (i : Fin cap) : Option (Fin D) :=
  if live : i.val<(B.incident h).card then some (N.slot h ((B.ordinal h).symm ⟨i.val,live⟩)) else none

theorem panel_at (N : B.Neighbors D) (fit : ∀h,(B.incident h).card≤cap) (h : H) (e : ↥(B.incident h)) :
    B.panel N fit h (B.position fit h e)=some (N.slot h e) := by
  have k : (B.position fit h e).val=(B.ordinal h e).val := rfl
  simp only [panel,k,dite_eq_left (B.ordinal h e).isLt]
  exact congrArg (fun x=>some (N.slot h x)) ((B.ordinal h).symm_apply_apply e)

/-- The finite local lookup only compares short resident fields. -/
def localSerial (row : Fin cap→Option (Fin D)) (s : Fin cap) :=
  (Finset.univ.filter fun i=>i<s ∧ row i=row s).card

theorem local_read (N : B.Neighbors D) (fit : ∀h,(B.incident h).card≤cap) (h : H) (e : ↥(B.incident h)) :
    localSerial (B.panel N fit h) (B.position fit h e)=B.serial h (B.peer h e.val) e.val := by
  let rows := Finset.univ.filter (fun j : ↥(B.incident h)=> j.val<e.val ∧ B.peer h j.val=B.peer h e.val)
  have bySlot : rows.map (B.position fit h)=Finset.univ.filter (fun i=>i<B.position fit h e ∧
      B.panel N fit h i=B.panel N fit h (B.position fit h e)) := by
    ext i
    simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,rows]
    constructor
    · rintro ⟨j,⟨old,peer⟩,rfl⟩
      exact ⟨(B.position_lt ..).2 old,by rw [B.panel_at,B.panel_at,(N.same h j e).2 peer]⟩
    · rintro ⟨early,eqn⟩
      have low : i.val<(B.ordinal h e).val := early
      have live : i.val<(B.incident h).card := low.trans (B.ordinal h e).isLt
      let j : ↥(B.incident h):=(B.ordinal h).symm ⟨i.val,live⟩
      have pos : B.position fit h j=i := Fin.ext (congrArg (fun z:Fin (B.incident h).card=>z.val) ((B.ordinal h).apply_symm_apply ⟨i.val,live⟩))
      rw [←pos,B.panel_at,B.panel_at] at eqn
      exact ⟨j,⟨(B.position_lt fit h j e).1 (by simpa only [pos] using early),(N.same h j e).1 (Option.some.inj eqn)⟩,pos⟩
  have byEdge : rows.map (Function.Embedding.subtype (·∈B.incident h))=B.earlier h (B.peer h e.val) e.val := by
    ext f
    simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,rows,earlier,B.mem_parallel]
    constructor
    · rintro ⟨j,⟨early,same⟩,rfl⟩
      exact ⟨⟨j.property,same⟩,early⟩
    · rintro ⟨⟨present,same⟩,early⟩
      exact ⟨⟨f,present⟩,⟨early,same⟩,rfl⟩
  unfold localSerial serial
  rw [←bySlot,←byEdge,Finset.card_map,Finset.card_map]

theorem serial_lt (fit : ∀h,(B.incident h).card≤cap) (h v : H) (q : Fin n) (present : q∈B.parallel h v) :
    B.serial h v q<cap := by
  apply lt_of_lt_of_le _ (fit h)
  apply Finset.card_lt_card
  have small : B.earlier h v q⊆B.incident h := fun _ hm=>((B.mem_parallel ..).1 (Finset.mem_filter.mp hm).1).1
  apply (Finset.ssubset_iff_of_subset small).2
  exact ⟨q,((B.mem_parallel ..).1 present).1,by simp [earlier]⟩
end Ends

namespace Ends
variable (B : Ends H n) (roster : H→Finset H) (names : H↪ℕ) (room : ∀h,(roster h).card≤D)
  (connected : ∀q,B.dst q∈roster (B.src q) ∧ B.src q∈roster (B.dst q))

include connected in
theorem peer_mem (h : H) (q : ↥(B.incident h)) : B.peer h q.val∈roster h := by
  obtain ⟨j,hj⟩:=q
  simp only [incident,Finset.mem_filter,Finset.mem_univ,true_and] at hj
  change B.peer h j∈roster h
  by_cases l : B.src j=h
  · rw [peer,ite_eq_left l];simpa only [l] using (connected j).1
  · have r:=hj.resolve_left l
    rw [peer,ite_eq_right l];simpa only [r] using (connected j).2

def neighborOrder (h : H) : ↥(roster h) ↪ Fin D :=
  let f : ↥(roster h) ↪ ↥((roster h).map names) :=
    ⟨fun a=>⟨names a.val,Finset.mem_map.mpr ⟨a.val,a.property,rfl⟩⟩,
      fun a b eq=>Subtype.ext (names.injective (congrArg Subtype.val eq))⟩
  (f.trans (((roster h).map names).orderIsoOfFin rfl).symm.toEquiv.toEmbedding).trans
    (Fin.castLEEmb (by rw [Finset.card_map];exact room h))

/-- The public names only order a single adjacency list. Its ordinal occupies
`clog 2 (D+1)` bits on the data pins. -/
def neighbors : B.Neighbors D where
  slot h q := neighborOrder roster names room h ⟨B.peer h q.val,B.peer_mem roster connected h q⟩
  same h q f := by
    rw [Function.Embedding.apply_eq_iff_eq,Subtype.ext_iff]
end Ends

namespace Packed
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM

/-- Zero is the unoccupied token. A live token carries its one-based small
ordinal; the high digits of the last physical word are cleared by `masked`. -/
def bits (D : ℕ) := Nat.clog 2 (D+1)
def token {D : ℕ} : Option (Fin D)→Cell (bits D)
  | none=>0
  | some j=>⟨j.val+1,(Nat.succ_lt_succ j.isLt).trans_le (Nat.le_pow_clog (by decide : 1<2) _)⟩

def readToken (D : ℕ) (x : Cell (bits D)) : Option (Fin D) :=
  if live : 0<x.val ∧ x.val≤D then some ⟨x.val-1,by omega⟩ else none
@[simp] theorem token_back {D : ℕ} (x : Option (Fin D)) : readToken D (token x)=x := by
  cases x with
  | none=>simp [readToken,token]
  | some j=>simp [readToken,token,j.isLt]

def source (row : Fin cap→Option (Fin D)) : Cell (bits D*cap) := encode _ _ (token ∘ row)

def serialAt (row : Fin cap→Option (Fin D)) (s : Fin cap) : Option (Fin cap) :=
  (row s).map fun _=>⟨Ends.localSerial row s,by
    have smaller : Finset.univ.filter (fun i=>i<s ∧ row i=row s) ⊆ Finset.Iio s :=fun _ hi=>Finset.mem_Iio.mpr (Finset.mem_filter.mp hi).2.1
    exact (Finset.card_le_card smaller).trans_lt (by simp)⟩

def lookup (D cap : ℕ) (x : Cell (bits D*cap)) : Cell (bits cap*cap) :=
  let row := readToken D ∘ (encode (bits D) cap).symm x
  encode _ _ (fun i=>token (serialAt row i))

@[simp] theorem lookup_source (row : Fin cap→Option (Fin D)) :
    lookup D cap (source row)=encode _ _ (fun i=>token (serialAt row i)) := by
  have same : readToken D ∘ (token ∘ row) = row := funext fun i=>token_back _
  simp only [lookup,source,Equiv.symm_apply_apply,same]

/-- One native lookup instruction path per purchased batch. The genuine
multigroup row reads preserve the incompletely filled final word. -/
theorem publish {H r M w : ℕ} (L : Banks) (out : ℕ) (fit : Fits L (bits D*cap) (bits cap*cap) M H r w out)
    (rows : Fin H→Fin r→Fin cap→Option (Fin D)) (m : Memory w)
    (input : PinFrame (M:=M) L (lookup D cap) (fun v g=>source (rows v g)) m) (positive : 0<M) :
    let result := image out (H*chunks r M) (DescentSIMDLookup.lookup L) m
    (DescentSIMDLookup.program L out H r M w).Exec m result (4+44*(H*chunks r M)) ∧
    (∀v g i,digit (bits cap) i.val (digit (bits cap*cap) (lane g positive).val
       (result (out+(row H r M (DescentSIMDLookup.position v g positive)).val)).val)=(token (serialAt (rows v g) i)).val) ∧
    CheapCode (DescentSIMDLookup.program L out H r M w) := by
  intro result
  let x:=fun v g=>source (rows v g)
  have native : (DescentSIMDLookup.program L out H r M w).Exec m result (4+(H*chunks r M)*(2*(DescentSIMDLookup.lookup L).work+4)) :=
    scan_exec out (H*chunks r M) (DescentSIMDLookup.lookup L) m
      (by simp [DescentSIMDLookup.lookup,Expr.Fits,fit.source,fit.mask,fit.dictionary]) fit.output
  have stored (p : Row H r M) : result (out+(row H r M p).val)=((masked (lookup D cap) x p:ℕ):Word w) :=
    (ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row H r M p)).trans (lookup_read L out fit (lookup D cap) x m input p)
  rw [Nat.mul_comm 44]
  refine ⟨@native,?_,
    (spec L out fit (lookup D cap) x).2⟩
  intro v g i
  rw [physical_read L out fit (lookup D cap) x result stored v g positive]
  change digit (bits cap) i.val ((lookup D cap (source (rows v g))).val)=_
  rw [lookup_source,digit_encode]
end Packed


end
end Hierarchy.DescentSharedCableNames

end OAI
