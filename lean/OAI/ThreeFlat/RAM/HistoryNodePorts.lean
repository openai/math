import OAI.ThreeFlat.RAM.HistoryStageRoot
import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.HeaderScanProcedure

namespace OAI
/-! # Indexed old half-ports of a selected chronology node -/

namespace ThreeFlat.RAM.HistoryNodePorts

open Computability.VPVNP.BurstRAM PhysicalPinsExpr PhysicalProcedure
open scoped BigOperators Fin.CommRing

/-- The root cache indexed by global chronological ID contains the physical
pin count followed by the extent of the external pin subsequence. -/
structure Layout where
  cursor : ℕ
  nodes : ℕ
  cache : ℕ
  starts : ℕ

variable {n : ℕ}
private abbrev E := Formula 1
private def l (x : ℕ) : E := .lit x
private def rd (a : E) (j : ℕ) : E := .load (add a (l j))

def id (A : Layout) : E := .cut (.load (l A.cursor)) (l 1)
def node (A : Layout) : E := add (l A.nodes) (mul (l 8) (id A))
def childCount (A : Layout) : E := rd (node A) 4
def childList (A : Layout) : E := rd (node A) 3
def halves (A : Layout) : E := rd (node A) 6
def kernel (A : Layout) : E := rd (node A) 5
def topPins (A : Layout) : E := rd (node A) 7
def child (A : Layout) (i : E) : E :=
  add (l A.cache) (mul (l 8) (.load (add (childList A) i)))

def oldAt (A : Layout) (i : E) : E := .cut (rd (child A i) 1) (rd (child A i) 5)

def fresh (A : Layout) : E :=
  let cnt : E := .load (halves A)
  let last := add (rd (halves A) 1) (mul (l 4) (.cut cnt (l 1)))
  eqz cnt (l 0) (l 0) (add (rd last 3) (rd last 2))

def «prefix» (A : Layout) (i : E) : ℕ → E
  | 0 => l 0
  | k+1 => add («prefix» A i k) (lt (l k) i (oldAt A (l k)) (l 0))

def sum (A : Layout) (m : ℕ→ℕ) (i : ℕ) :=
  let cur := m A.cursor-1
  let childBase := m (A.nodes+8*cur+3)
  ∑ t ∈ Finset.range i,
    let p := A.cache+8*m (childBase+t)
    m (p+1)-m (p+5)

theorem prefix_value (A : Layout) (cap W : ℕ) (pub : Param→ℕ) (m : ℕ→ℕ) (vs : Fin 1→ℕ) (i : E)
    (bound : i.natural W pub m vs≤cap) : («prefix» A i cap).natural W pub m vs=sum A m (i.natural W pub m vs) := by
  have truncated (k : ℕ) :
      («prefix» A i k).natural W pub m vs =
        ∑ t∈Finset.range k,if t< i.natural W pub m vs then (oldAt A (l t)).natural W pub m vs else 0 := by
    induction k with
    | zero => simp [«prefix»,l,Formula.natural]
    | succ k ih =>
      by_cases live : k < i.natural W pub m vs <;>
        simp [«prefix»,l,add,lt,Formula.natural,natOp,natTest,Finset.sum_range_succ,ih,live]
  rw [truncated,← Finset.sum_filter]
  have same : (Finset.range cap).filter (fun t => t< i.natural W pub m vs)=Finset.range (i.natural W pub m vs) := by
    ext t
    simp [Finset.mem_range]; omega
  rw [same]
  rfl

def clipped (A : Layout) (cap : ℕ) : E :=
  let i : E := .cut (.reg 0) (.lit A.starts)
  «prefix» A (lt i (childCount A) i (childCount A)) cap

theorem clipped_word (A : Layout) (cap W : ℕ) (m : ℕ→ℕ) (j : ℕ)
    (count : m (A.nodes+8*(m A.cursor-1)+4)≤cap) :
    (clipped A cap).natural W (fun _=>0) m (fun _=>j) =
      sum A m (min (j-A.starts) (m (A.nodes+8*(m A.cursor-1)+4))) := by
  have index :
      (lt (.cut (.reg 0) (.lit A.starts)) (childCount A)
        (.cut (.reg 0) (.lit A.starts)) (childCount A)).natural W (fun _=>0) m (fun _=>j)=
        min (j-A.starts) (m (A.nodes+8*(m A.cursor-1)+4)) := by
    simp [childCount,node,id,rd,l,Formula.natural,add,mul,natOp,natTest,min_def]
   ; split <;> split <;> omega
  unfold clipped
  rw [prefix_value A cap W _ _ _ _ (by rw [index];omega),index]

/-- Finite-word arithmetic for all issued prefix positions. Every probed child
and cache field is indexed by the actual vector ordinal in this scan. -/
theorem clipped_fits {W : ℕ} (A : Layout) (cap : ℕ) (m : Memory W)
    (cursor : A.cursor<2^W) (room : A.starts+(cap+1)<2^W)
    (nodeRoom : A.nodes+8*((m A.cursor).val-1)+4<2^W)
    (listRoom : ∀ k : Fin cap,(m (A.nodes+8*((m A.cursor).val-1)+3)).val+k.val<2^W)
    (cacheRoom : ∀ k : Fin cap,A.cache+8*(m ((m (A.nodes+8*((m A.cursor).val-1)+3)).val+k.val)).val+5<2^W)
    (i : Fin (cap+1)) :
    (clipped A cap).Fits W (fun _=>0) (fun a=>(m a).val) (fun _=>A.starts+i.val) := by
  let num:=fun a=>(m a).val
  let vs:=fun _ : Fin 1=>A.starts+i.val
  let ok:=fun e : E=>e.Fits W (fun _=>0) num vs
  let val:=fun e : E=>e.natural W (fun _=>0) num vs
  let delta : E:=.cut (.reg 0) (l A.starts)
  let ix:=lt delta (childCount A) delta (childCount A)
  have vsRoom : A.starts+i.val<2^W:=by have h:=i.isLt;omega
  have dfit : ok delta:=⟨trivial,trivial,vsRoom,by change A.starts<2^W; omega⟩
  have nfit : ok (node A):=⟨trivial,⟨trivial,⟨⟨trivial,cursor⟩,trivial,(m A.cursor).isLt,by
    change 1<2^W;omega⟩,trivial⟩,trivial⟩
  have nrd (k : ℕ) (small : k≤4) : ok (rd (node A) k):=
    ⟨⟨nfit,trivial,trivial⟩,by change A.nodes+8*((m A.cursor).val-1)+k<2^W;omega⟩
  have dRoom : val delta<2^W:=by change A.starts+i.val-A.starts<2^W;omega
  have cnt : val (childCount A)<2^W:=(m _).isLt
  have ixFit : ok ix:=⟨dfit,nrd 4 le_rfl,dRoom,cnt,by split <;> first | exact dfit | exact nrd 4 le_rfl⟩
  have ixRoom : val ix<2^W:=by
    change (if _ then val delta else val (childCount A))<2^W
    split <;> assumption
  have oldFit (k : Fin cap) : ok (oldAt A (l k.val)) := by
    have cr : ok (child A (l k.val)):=
      ⟨trivial,⟨trivial,⟨⟨nrd 3 (by decide),trivial,trivial⟩,listRoom k⟩,trivial⟩,trivial⟩
    have rr (q : ℕ) (small : q≤5) : ok (rd (child A (l k.val)) q):=
      ⟨⟨cr,trivial,trivial⟩,by
        change A.cache+8*(m ((m (A.nodes+8*((m A.cursor).val-1)+3)).val+k.val)).val+q<2^W
        have h:=cacheRoom k;omega⟩
    exact ⟨rr 1 (by decide),rr 5 le_rfl,(m _).isLt,(m _).isLt⟩
  have pf (k : ℕ) (bound : k≤cap) : ok («prefix» A ix k) := by
    induction k with
    | zero => trivial
    | succ k ih =>
      exact ⟨ih (by omega),⟨trivial,ixFit,by change k<2^W;omega,ixRoom,by
        split
        · exact oldFit ⟨k,by omega⟩
        · trivial⟩,trivial⟩
  exact pf cap le_rfl

def phase (W : ℕ) (A : Layout) (cap : ℕ) : Procedure W :=
  let n : E := .cut (.reg 0) (l A.starts)
  let clipped := lt n (childCount A) n (childCount A)
  PhysicalInputPhases.writing (HeaderScan.closed («prefix» A clipped cap)) Fin.elim0 A.starts (cap+1)

theorem prefix_work (A B : Layout) {q r : Formula 1} (same : q.work=r.work) (cap : ℕ) :
    («prefix» A q cap).work=(«prefix» B r cap).work := by
  induction cap with
  | zero => rfl
  | succ n ih =>
    simp only [«prefix»,add,lt,Formula.work,same,ih,oldAt,rd,child,childList,node,id,l,mul]



/-- The per-node native prefix scan has fixed work at a fixed family cap. -/
def phaseCost (cap : ℕ) : ℕ :=
  4+(cap+1)*(2*(clipped ⟨0,0,0,0⟩ cap).work+4)

theorem phase_ticks (W : ℕ) (A : Layout) (cap : ℕ) :
    4+(cap+1)*(2*(HeaderScan.closed (w:=W) (clipped A cap)).binds+4)=phaseCost cap := by
  have hw : (clipped A cap).work=(clipped ⟨0,0,0,0⟩ cap).work := by
    unfold clipped
    apply prefix_work
    rfl
  simp only [phaseCost,HeaderScan.binds_closed,hw]


end ThreeFlat.RAM.HistoryNodePorts

end OAI
