import OAI.Hierarchy.ProtocolRAMTurnItinerary

namespace OAI
/-! # Readback of genuine past and future links in the field-major turn tape -/

namespace Hierarchy.ProtocolRAMTurnItinerary

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM
open scoped Fin.CommRing

/-- Position is the boundary between two adjacent occurrences. There is a single
old-to-old turn when a commodity's route is empty. -/
structure Turn where
  item : ℕ
  origin : ℕ
  length : ℕ
  position : ℕ
  reverse : Bool
  width : ℕ
  site : ℕ
  seat : ℕ

def Turn.boundary (t : Turn) (right : Bool) := t.position = (if right then t.length else 0)

def Turn.occurrence (t : Turn) (right : Bool) : ℕ :=
  t.origin+(if t.reverse then (t.length-t.position)-right.toNat else t.position-(!right).toNat)

structure Values where
  oldSource : ℕ → ℕ
  oldTarget : ℕ → ℕ
  edge : ℕ → ℕ
  tailSite : ℕ → ℕ
  tailRole : ℕ → ℕ
  headRole : ℕ → ℕ
  starts : ℕ → ℕ

noncomputable def Turn.role (t : Turn) (v : Values) (right : Bool) : ℕ := by
  classical
  exact if t.boundary right then (if right then v.oldTarget else v.oldSource) t.item else
    let e := v.edge (t.occurrence right)
    if v.tailSite e=t.site then v.tailRole e else v.headRole e

noncomputable def Turn.start (t : Turn) (v : Values) (right : Bool) : ℕ := by
  classical
  exact if t.boundary right then 0 else v.starts (t.occurrence right)

noncomputable def Turn.field (t : Turn) (v : Values) : Fin 7 → ℕ :=
  ![t.role v false,t.role v true,t.start v false,t.start v true,
    (if t.length < t.position then 0 else t.width),t.site,t.seat]

variable {W N edges history occ : ℕ}

structure Chart.Reads (p : Chart) (record : Fin N → Turn) (m : Memory W) : Prop where
  item : ∀ i,p.item.eval m (i.val:Word W)=((record i).item:Word W)
  origin : ∀ i,p.origin.eval m (i.val:Word W)=((record i).origin:Word W)
  length : ∀ i,p.length.eval m (i.val:Word W)=((record i).length:Word W)
  position : ∀ i,p.position.eval m (i.val:Word W)=((record i).position:Word W)
  reverse : ∀ i,p.reverse.eval m (i.val:Word W)=((record i).reverse.toNat:Word W)
  width : ∀ i,p.width.eval m (i.val:Word W)=((record i).width:Word W)
  site : ∀ i,p.site.eval m (i.val:Word W)=((record i).site:Word W)
  seat : ∀ i,p.seat.eval m (i.val:Word W)=((record i).seat:Word W)

structure Banks.Reads (b : Banks) (v : Values) (history occ edges : ℕ) (m : Memory W) : Prop where
  oldSource : ∀ i < history,b.oldSource.read m (i:Word W)=(v.oldSource i:Word W)
  oldTarget : ∀ i < history,b.oldTarget.read m (i:Word W)=(v.oldTarget i:Word W)
  edge : ∀ i < occ,b.edge.read m (i:Word W)=(v.edge i:Word W)
  tailSite : ∀ i < edges,b.tailSite.read m (i:Word W)=(v.tailSite i:Word W)
  tailRole : ∀ i < edges,b.tailRole.read m (i:Word W)=(v.tailRole i:Word W)
  headRole : ∀ i < edges,b.headRole.read m (i:Word W)=(v.headRole i:Word W)
  starts : ∀ i < occ,b.starts.read m ((4*i:ℕ):Word W)=(v.starts i:Word W)

structure Turn.Fits (t : Turn) (v : Values) (W history occ edges : ℕ) : Prop where
  item : t.item < history
  posFits : t.position < 2^W
  lenFits : t.length < 2^W
  siteFits : t.site < 2^W
  occFits : ∀ b,t.position ≤ t.length → ¬t.boundary b → t.occurrence b < occ
  edgeFits : ∀ i < occ,v.edge i < edges
  tailFits : ∀ i < edges,v.tailSite i < 2^W

private theorem word_eq {x y : ℕ} (hx : x < 2^W) (hy : y < 2^W) :
    ((x:Word W)=(y:Word W)) ↔ x=y := by
  rw [Fin.ext_iff,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy]

private theorem eval_boundary (p : Chart) (t : Fin N → Turn) (m : Memory W) (read : p.Reads t m)
    (i : Fin N) (b : Bool) (yes no : Expr)
    (posFits : (t i).position < 2^W) (lenFits : (t i).length < 2^W) :
    (onEnd p b yes no).eval m (i.val:Word W)=
      (if (t i).position=(if b then (t i).length else 0) then yes.eval m (i.val:Word W)
        else no.eval m (i.val:Word W)) := by
  have zd : 2^W ∣ (t i).position ↔ (t i).position=0 :=
    ⟨fun h=>Nat.eq_zero_of_dvd_of_lt h posFits,fun h=>h ▸ dvd_zero _⟩
  cases b <;> simp [onEnd,Expr.eval,Comparison.test,read.position,read.length,word_eq posFits lenFits,zd]

theorem eval_occurrence (p : Chart) (t : Fin N → Turn) (m : Memory W) (read : p.Reads t m)
    (i : Fin N) (b : Bool) (one : 1 < 2^W) (inside : (t i).position ≤ (t i).length)
    (hop : ¬(t i).boundary b) :
    (occurrence p b).eval m (i.val:Word W)=((t i).occurrence b:Word W) := by
  have nz : (1:Word W)≠0 := by
    intro same
    exact Nat.one_ne_zero ((word_eq one (Nat.two_pow_pos W)).mp same)
  cases b <;> cases h : (t i).reverse <;>
    simp (disch := omega) [occurrence,Turn.occurrence,Turn.boundary,plus,minus,Expr.eval,RowOp.opcode,
      BinaryOp.eval,Comparison.test,read.origin,read.position,read.length,read.reverse,h,nz,
      Nat.cast_add,Nat.cast_sub] at hop ⊢
  · rw [Nat.cast_sub (by omega : 1 ≤ (t i).position),Nat.cast_one]
  · rw [Nat.cast_sub (by omega : 1 ≤ (t i).length-(t i).position),Nat.cast_sub inside,Nat.cast_one]

theorem eval_four (x : Expr) (m : Memory W) (i : Word W) :
    (four x).eval m i = 4*x.eval m i := by
  simp only [four,plus,Expr.eval,RowOp.opcode,BinaryOp.eval]
  ring

theorem eval_role (p : Chart) (b : Banks) (record : Fin N → Turn) (v : Values) (m : Memory W)
    (rd : p.Reads record m) (banks : b.Reads v history occ edges m) (i : Fin N) (side : Bool)
    (fit : (record i).Fits v W history occ edges) (one : 1 < 2^W)
    (inside : (record i).position ≤ (record i).length) :
    (role p b side).eval m (i.val:Word W)=((record i).role v side:Word W) := by
  classical
  rw [role,eval_boundary p record m rd i side _ _ fit.posFits fit.lenFits]
  by_cases bound : (record i).boundary side
  · have hp : (record i).position=(if side then (record i).length else 0) := bound
    simp only [Turn.role,bound,hp,ite_true]
    cases side <;> simp [Expr.eval,rd.item,banks.oldSource _ fit.item,banks.oldTarget _ fit.item]
  · have hp : ¬(record i).position=(if side then (record i).length else 0) := bound
    simp only [Turn.role,bound,hp,ite_false]
    have atRow := eval_occurrence p record m rd i side one inside bound
    have inTape := fit.occFits side inside bound
    have inEdge := fit.edgeFits _ inTape
    simp only [Expr.eval,Comparison.test,atRow,banks.edge _ inTape,banks.tailSite _ inEdge,
      banks.tailRole _ inEdge,banks.headRole _ inEdge,rd.site,beq_iff_eq,
      word_eq (fit.tailFits _ inEdge) fit.siteFits]
    by_cases same : v.tailSite (v.edge ((record i).occurrence side))=(record i).site <;> simp [same]

theorem eval_start (p : Chart) (b : Banks) (record : Fin N → Turn) (v : Values) (m : Memory W)
    (rd : p.Reads record m) (banks : b.Reads v history occ edges m) (i : Fin N) (side : Bool)
    (fit : (record i).Fits v W history occ edges) (one : 1 < 2^W)
    (inside : (record i).position ≤ (record i).length) :
    (start p b side).eval m (i.val:Word W)=((record i).start v side:Word W) := by
  classical
  rw [start,eval_boundary p record m rd i side _ _ fit.posFits fit.lenFits]
  by_cases bound : (record i).boundary side
  · have hp : (record i).position=(if side then (record i).length else 0) := bound
    simp only [Turn.start,bound,hp,ite_true,Expr.eval,Nat.cast_zero]
  · have hp : ¬(record i).position=(if side then (record i).length else 0) := bound
    simp only [Turn.start,bound,hp,ite_false]
    change b.starts.read m ((four _).eval m (i.val:Word W))=_
    rw [eval_four,eval_occurrence p record m rd i side one inside bound]
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using banks.starts _ (fit.occFits side inside bound)

theorem eval_live (p : Chart) (record : Fin N → Turn) (m : Memory W) (rd : p.Reads record m)
    (i : Fin N) (posFits : (record i).position < 2^W) (lenFits : (record i).length < 2^W) :
    (live p).eval m (i.val:Word W)=
      ((if (record i).length < (record i).position then 0 else (record i).width:ℕ):Word W) := by
  have lt : (((record i).length:Word W)<((record i).position:Word W)) ↔
      (record i).length < (record i).position := by
    change ((record i).length:Word W).val < ((record i).position:Word W).val ↔ _
    rw [Fin.val_cast_of_lt lenFits,Fin.val_cast_of_lt posFits]
  by_cases short : (record i).length < (record i).position
  · have ltW := lt.mpr short
    simp [live,Expr.eval,Comparison.test,rd.position,rd.length,short,ltW]
  · have no : ¬(((record i).length:Word W)<((record i).position:Word W)) := fun h=>short (lt.mp h)
    simp [live,Expr.eval,Comparison.test,rd.position,rd.length,rd.width,short,no]

/-- Live turns, including both path endpoints, have all seven exact fields.
Potential padding past the last turn always exports zero live-width. -/
theorem observed {base : ℕ} (p : Chart) (b : Banks) (record : Fin N → Turn) (v : Values) (m : Memory W)
    (rd : p.Reads record m) (banks : b.Reads v history occ edges m) (fit : ∀ i,(record i).Fits v W history occ edges)
    (one : 1 < 2^W) (inputs : ∀ j,(field p b j).Fits W base) (room : base+7*N < 2^W) :
    ∃ out,(program W base N p b).Exec m out (ticks base N p b) ∧
      (∀ (i : Fin N) (f : Fin 7),(record i).position ≤ (record i).length →
        out (base+f.val*N+i.val)=((record i).field v f:Word W)) ∧
      (∀ i : Fin N,out (base+4*N+i.val)=
        ((if (record i).length < (record i).position then 0 else (record i).width:ℕ):Word W)) ∧
      ∀ a,a < base ∨ base+7*N ≤ a → out a=m a := by
  obtain ⟨out,exec,read,frame⟩ := run base p b m inputs room
  refine ⟨out,exec,?_,?_,frame⟩
  · intro i f inside
    rw [read]
    fin_cases f
    · exact eval_role p b record v m rd banks i false (fit i) one inside
    · exact eval_role p b record v m rd banks i true (fit i) one inside
    · exact eval_start p b record v m rd banks i false (fit i) one inside
    · exact eval_start p b record v m rd banks i true (fit i) one inside
    · exact eval_live p record m rd i (fit i).posFits (fit i).lenFits
    · exact rd.site i
    · exact rd.seat i
  · intro i
    exact (read 4 i).trans (eval_live p record m rd i (fit i).posFits (fit i).lenFits)

end Hierarchy.ProtocolRAMTurnItinerary

end OAI
