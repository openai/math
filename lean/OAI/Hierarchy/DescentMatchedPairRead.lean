import OAI.Hierarchy.DescentMatchedPairRecord
import OAI.Hierarchy.DescentMatchedPairOrdinal

namespace OAI
/-! # Numeric incidence and selector readback for an accepted matched pair -/

namespace Hierarchy.DescentPacking.PairRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing Classical BigOperators
noncomputable section
variable {w n : ℕ} {s : Inputs} {z bins dest dead scratch : ℕ}

def table (b : Bank) (m : Memory w) (value : ℕ→ℕ) := ∀i<b.size,m (b.base+i)=(value i:Word w)

private theorem bankAt {b : Bank} {m : Memory w} {value : ℕ→ℕ} (read : table b m value)
    {i cut : ℕ} (fit : b.Fits w cut) (small : i < b.size) :
    b.read m (i:Word w)=(value i:Word w) := by
  simpa only [Bank.read,Fin.val_cast_of_lt (small.trans fit.2.1),Nat.mod_eq_of_lt small] using read i small

/-- Each of the large tables records the original old edge or site ordinals.
The prefix and remaining-capacity words come from the chronological packing passes. -/
structure Contents where
  choice : ℕ
  need : ℕ
  denseBefore : ℕ
  rawBefore : ℕ
  binStart : ℕ→ℕ
  capacity : ℕ→ℕ
  remaining : ℕ→ℕ
  thinEdge : ℕ→ℕ
  thickEdge : ℕ→ℕ
  src : ℕ→ℕ
  dst : ℕ→ℕ
  profile : ℕ→ℕ

structure Loaded (s : Inputs) (h : Contents) (m : Memory w) : Prop where
  choice : (m s.choice).val=h.choice
  amount : (m s.amount).val=h.need
  dense : (m s.acceptedBefore).val=h.denseBefore
  raw : (m s.thinBefore).val=h.rawBefore
  binStart : table s.binStart m h.binStart
  capacity : table s.initialCapacity m h.capacity
  remaining : table s.remainingBefore m h.remaining
  thin : table s.thinEdges m h.thinEdge
  thick : table s.thickEdges m h.thickEdge
  src : table s.oldSource m h.src
  dst : table s.oldTarget m h.dst
  profile : table s.profiles m h.profile

/-- Decode every scalar and old directory at its literal word address. -/
def contents (s : Inputs) (m : Memory w) : Contents :=
  let col (b : Bank) := fun i=>(m (b.base+i)).val
  ⟨(m s.choice).val,(m s.amount).val,(m s.acceptedBefore).val,(m s.thinBefore).val,
    col s.binStart,col s.initialCapacity,col s.remainingBefore,col s.thinEdges,col s.thickEdges,
    col s.oldSource,col s.oldTarget,col s.profiles⟩

theorem contents_loaded (s : Inputs) (m : Memory w) : Loaded s (contents s m) m := by
  have read (b : Bank) : table b m (fun i=>(m (b.base+i)).val) := fun i _=>(Fin.cast_val_eq_self _).symm
  exact ⟨rfl,rfl,rfl,rfl,read _,read _,read _,read _,read _,read _,read _,read _⟩

def thinIndex (h : Contents) (q : ℕ) := h.rawBefore+q
def thickIndex (h : Contents) (q : ℕ) :=
  h.binStart h.choice+(h.capacity h.choice-h.remaining h.choice+q)

def values (h : Contents) (z q : ℕ) : Fin 9→ℕ :=
  let t := h.thickEdge (thickIndex h q)
  let u := h.thinEdge (thinIndex h q)
  ![h.denseBefore+q,t,u,h.src t,h.dst t,h.src u,h.dst u,z,h.profile (h.denseBefore+q)]

structure InRange (s : Inputs) (h : Contents) (q : ℕ) : Prop where
  bin : h.choice < s.binStart.size
  initial : h.choice < s.initialCapacity.size
  remaining : h.choice < s.remainingBefore.size
  balance : h.remaining h.choice≤h.capacity h.choice
  thin : thinIndex h q < s.thinEdges.size
  thick : thickIndex h q < s.thickEdges.size
  thSrc : h.thickEdge (thickIndex h q) < s.oldSource.size
  thDst : h.thickEdge (thickIndex h q) < s.oldTarget.size
  tnSrc : h.thinEdge (thinIndex h q) < s.oldSource.size
  tnDst : h.thinEdge (thinIndex h q) < s.oldTarget.size
  prof : h.denseBefore+q < s.profiles.size

theorem field_values {m : Memory w} {h : Contents} {cut : ℕ} (b : Early w s cut) (d : Loaded s h m)
    (q : ℕ) (r : InRange s h q) (f : Fin 9) :
    (field s z f).eval m (q:Word w)=(values h z q f:Word w) := by
  have castWord {a v : ℕ} (e : (m a).val=v) : m a=(v:Word w) := by rw [←e,Fin.cast_val_eq_self]
  have idx : (ordinal s).eval m (q:Word w)=((h.denseBefore+q:ℕ):Word w) := by
    simp [ordinal,Expr.eval,castWord d.dense]
  have tu : (thin s).eval m (q:Word w)=(h.thinEdge (thinIndex h q):Word w) := by
    change s.thinEdges.read m (m s.thinBefore+(q:Word w))=_
    rw [castWord d.raw,←Nat.cast_add]
    exact bankAt d.thin b.thinEdges r.thin
  have sel : m s.choice=(h.choice:Word w) := castWord d.choice
  have tv : (thick s).eval m (q:Word w)=(h.thickEdge (thickIndex h q):Word w) := by
    change s.thickEdges.read m (s.binStart.read m (m s.choice)+
      (s.initialCapacity.read m (m s.choice)-s.remainingBefore.read m (m s.choice)+(q:Word w)))=_
    rw [sel,bankAt d.binStart b.binStart r.bin,bankAt d.capacity b.initialCapacity r.initial,
      bankAt d.remaining b.remainingBefore r.remaining,←Nat.cast_sub r.balance,←Nat.cast_add,←Nat.cast_add]
    exact bankAt d.thick b.thickEdges r.thick
  fin_cases f
  · exact idx
  · exact tv
  · exact tu
  · change s.oldSource.read m ((thick s).eval m _)=_
    rw [tv];exact bankAt d.src b.oldSource r.thSrc
  · change s.oldTarget.read m ((thick s).eval m _)=_
    rw [tv];exact bankAt d.dst b.oldTarget r.thDst
  · change s.oldSource.read m ((thin s).eval m _)=_
    rw [tu];exact bankAt d.src b.oldSource r.tnSrc
  · change s.oldTarget.read m ((thin s).eval m _)=_
    rw [tu];exact bankAt d.dst b.oldTarget r.tnDst
  · rfl
  · change s.profiles.read m ((ordinal s).eval m _)=_
    rw [idx];exact bankAt d.profile b.profiles r.prof

theorem nine_values {h : Contents} (m : Memory w) (b : Space w n s bins dest dead scratch m)
    (d : Loaded s h m) (q : Fin n) (eligible : h.choice < bins) (live : q.val < h.need)
    (r : InRange s h q.val) (f : Fin 9) :
    result n s z bins dest dead scratch (List.finRange 9) m (dest+9*(h.denseBefore+q.val)+f.val)=
      (values h z q.val f:Word w) := by
  rw [←d.dense]
  exact (nine_fields m b f q (d.choice.trans_lt eligible) (by simpa only [d.amount] using live)).trans
    (field_values b.toEarly d q.val r f)

end
end Hierarchy.DescentPacking.PairRAM

end OAI
