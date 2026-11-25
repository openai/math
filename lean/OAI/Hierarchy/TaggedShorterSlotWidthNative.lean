import OAI.Hierarchy.TaggedShorterSlotWidth
import OAI.Hierarchy.TaggedShorterEmitMachine

namespace OAI
/-! # Computing and replaying the original link width for both fixed endpoints -/

noncomputable section
namespace Hierarchy.TaggedShorterSlotWidth
open ThreeFlat RAM RAM.DescriptorExpr RAM.PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM TaggedShorterEmitMachine
open scoped Fin.CommRing Classical
variable {W : ℕ}

def slotWord {R : ℕ} (s : Fin R) (j : Fin 5) (k : Fin 2) : Word W :=
  ((2*(finProdFinEquiv (s,j)).val+k.val:ℕ):Word W)

private abbrev add (a b : Expr) := Expr.op .add a b

def term (A : Tables) (origins : Bank) (D γ sink : ℕ) : Expr :=
  let r := Expr.lookup A.owner .row
  let z := Expr.lookup A.subslot .row
  let stride := add (add r r) r
  let origin := Expr.lookup origins (.lookup A.gateGroup stride)
  let offset := Expr.branch .lt (.lookup A.column .row) (.lit 2)
    (.lookup A.left r) (add (.lit D) (.lookup A.right r))
  let address := add origin (add offset z)
  let width := Expr.lookup A.metricWidth stride
  let even := Expr.op .mask .row (.lit 1)
  TaggedShorterEmitMachine.select A γ
    (.branch .eq even (.lit 0) address width)
    (.branch .eq even (.lit 0) (.lit sink) (.lit 0))

set_option maxHeartbeats 1200000 in
theorem work (A : Tables) (origins : Bank) (D γ sink : ℕ) :
    (term A origins D γ sink).work=203 := by
  simp [term,TaggedShorterEmitMachine.select,Expr.work,add]

/-- Exact execution and memory footprint of the physical scalar gather followed by
the existing sparse address/value replay. -/
def procedure (W base groups D src R γ sink : ℕ) (A : Tables) (origins : Bank) : Procedure W :=
  (scan W base (2*groups*D) (.lit 0)).seq
    ((scan W src (10*R) (term A origins D γ sink)).seq (EffectSeed.scatter W src (5*R)))

private theorem scans_cheap (W base n src rows count : ℕ) (e : Expr) :
    CheapCode ((scan W base n (.lit 0)).seq ((scan W src rows e).seq (EffectSeed.scatter W src count))) :=
  @cheap_seq W (scan W base n (.lit 0)) ((scan W src rows e).seq (EffectSeed.scatter W src count))
    (scan_cheap W base n (.lit 0)) (TaggedShorterEmitMachine.scanReplay_cheap W src rows count e)

theorem cheap (W base groups D src R γ sink : ℕ) (A : Tables) (origins : Bank) :
    CheapCode (procedure W base groups D src R γ sink A origins) :=
  @scans_cheap W base (2*groups*D) src (10*R) (5*R) (term A origins D γ sink)

theorem procedure_size (W base groups D src R γ sink : ℕ) (A : Tables) (origins : Bank) :
    let p := procedure W base groups D src R γ sink A origins
    p.labels=635 ∧ p.registers=217 ∧ p.slots=2 := by
  have ⟨el,er,es⟩ := scan_size W src (10*R) (term A origins D γ sink)
  have ⟨cl,cr,cs⟩ := scan_size W base (2*groups*D) (.lit 0)
  change _+(_+9)=635 ∧ _+(_+5)=217 ∧ _+(_+2)=2
  simp [cl,cr,cs,el,er,es,work,Expr.work]

theorem term_read (A : Tables) (origins : Bank) (D γ sink base i z bits g actual pieces cr l r : ℕ)
    (m : Memory W) (a : Word W) (j : Fin 5) (k : Fin 2)
    (s : Source A m a i z (finProdFinEquiv (j,k)).val bits g actual pieces cr l r)
    (origin : actual=γ ∧ z<pieces → origins.read m (g:Word W)=((base+2*g*D : ℕ):Word W))
    (classFits : γ<2^W) (slotFits : z<2^W) (small : 2<2^W)
    (parity : (BinaryOp.bitAnd.eval a (1:Word W)).val=k.val) :
    (term A origins D γ sink).eval m a =
      if actual=γ ∧ z<pieces then
        if k.val=0 then
          (slotAddress base D g (side j) ((if side j then r else l)+z):Word W)
        else (bits:Word W)
      else if k.val=0 then (sink:Word W) else 0 := by
  have triple : ((i:Word W)+(i:Word W))+(i:Word W)=((3*i:ℕ):Word W) := by
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    ring
  have cls : A.widthClass.read m (bits:Word W)=(γ:Word W) ↔ actual=γ := by
    rw [Fin.ext_iff,s.widthClass,Fin.val_cast_of_lt classFits]
  have live : (z:Word W)<A.widthPieces.read m (bits:Word W) ↔ z<pieces := by
    rw [Fin.lt_def,Fin.val_cast_of_lt slotFits,s.widthPieces]
  have even : BinaryOp.bitAnd.eval a (1:Word W)=0 ↔ k.val=0 := by rw [Fin.ext_iff,parity];rfl
  have isLeft : A.column.read m a < (2:Word W) ↔ j.val=0 := by
    rw [Fin.lt_def,s.column]
    have two : (2 : Word W).val=2 := Fin.val_cast_of_lt (a:=2) small
    rw [two]
    have form : (finProdFinEquiv (j,k)).val=k.val+2*j.val := by fin_cases j <;> fin_cases k <;> decide
    rw [form]
    have := k.isLt
    omega
  simp only [term,TaggedShorterEmitMachine.select,Expr.eval,RowOp.opcode,
    show (BinaryOp.add.eval : Word W → Word W → Word W)=(·+·) from rfl,
    Comparison.test,beq_iff_eq,decide_eq_true_eq,s.owner,s.subslot,triple,s.width,cls,live,
    s.group,s.left,s.right]
  by_cases c : actual=γ <;> by_cases z' : z<pieces <;> by_cases k' : k.val=0 <;>
    by_cases j' : j.val=0 <;> simp [c,z',k',j',even,isLeft,origin,side,slotAddress,Nat.add_mul,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]; ring

theorem exec {groups D R : ℕ} {c : Fin groups→ℕ}
    (pl : ∀ g,Bool → Fin (c g) ↪ Fin D) (bits : Transport c→ℕ)
    (sel : Fin R→Option (Transport c)) (covers : ∀u,∃s,sel s=some u)
    (m : Memory W) (A : Tables) (origins : Bank) (base src γ sink : ℕ)
    (ordered : base+2*groups*D≤ src) (room : src+10*R<2^W) (sinkLow : sink<src)
    (apart : ∀x : Slot groups D,sink≠index base x)
    (inputs : (term A origins D γ sink).Fits W src) (low : (term A origins D γ sink).Fits W base)
    (words : ∀ (s : Fin R) (j : Fin 5) (k : Fin 2),
      let av := record (W:=W) pl bits base sink sel (finProdFinEquiv (s,j))
      (term A origins D γ sink).eval m (slotWord s j k)=(if k.val=0 then av.1 else av.2)) :
    ∃ out,(procedure W base groups D src R γ sink A origins).Exec m out
          ((4+6*(2*groups*D))+(8+4130*R)) ∧
      (∀x : Slot groups D,out (index base x)=(value pl bits x:Word W)) ∧
      ∀t, (t<base ∨ base+2*groups*D≤t) → (t<src ∨ src+10*R≤t) → t≠sink → out t=m t := by
  let e := term A origins D γ sink
  let n := 2*groups*D
  let zero := image base n (.lit 0) m
  let filled := image src (10*R) e zero
  let es := List.ofFn (record (W:=W) pl bits base sink sel)
  have erased : (scan W base n (.lit 0)).Exec m zero (4+6*n) := by
    have before : base+n<2^W := by dsimp [n];omega
    have time : 4+n*(2*Expr.work (.lit 0)+4)=4+6*n := by simp [Expr.work,Nat.mul_comm]
    rw [←time]
    intro P R' K M pc reg pub exit installed publicData cfg mem start eq
    exact scan_exec base n (.lit 0) m trivial before M pc reg pub exit installed publicData cfg mem start eq
  have zeroFrame (t : ℕ) (away : t<base ∨ base+n≤t) : zero t=m t := by
    rcases away with h|h <;> simp [zero,image,fillSegment,show ¬(base≤t ∧ t<base+n) by omega]
  have scanRun : (scan W src (10*R) e).Exec zero filled (4+10*R*(2*e.work+4)) :=
    scan_exec src (10*R) e zero inputs room
  have fillFrame (t : ℕ) (away : t<src ∨ src+10*R≤t) : filled t=zero t := by
    simp [filled,image,fillSegment,show ¬(src≤t ∧ t<src+10*R) by omega]
  have len : es.length=R*5 := List.length_ofFn
  have loaded : EffectStream.Loaded filled src es := by
    rw [EffectStream.loaded_iff]
    intro i
    obtain ⟨⟨s,j⟩,hk⟩ := finProdFinEquiv.surjective (Fin.cast len i)
    have eqn : (finProdFinEquiv (s,j)).val=i.val := congrArg Fin.val hk
    have atW (k : Fin 2) :
        filled (src+(2*i.val+k.val))=
          if k.val=0 then (es.get i).1 else (es.get i).2 := by
      have hi := i.isLt
      have hk' := k.isLt
      have range : 2*i.val+k.val<10*R := by omega
      have read := eval_below e (slotWord s j k) m zero low (fun t h=>zeroFrame t (.inl h))
      have staged : filled (src+(2*i.val+k.val))=e.eval zero (slotWord s j k) := by
        simp [filled,image,fillSegment,slotWord,eqn,show src+(2*i.val+k.val)<src+10*R by omega]
      refine staged.trans (read.trans ?_)
      have atIndex : es.get i=record (W:=W) pl bits base sink sel (finProdFinEquiv (s,j)) := by
        change (List.ofFn _).get i=_
        rw [List.get_ofFn]
        apply congrArg (record (W:=W) pl bits base sink sel)
        exact Fin.ext ((Fin.val_cast _ _).trans eqn.symm)
      rw [atIndex]
      exact words s j k
    exact ⟨by simpa using atW 0,by simpa [Nat.add_assoc] using atW 1⟩
  have dest (p : Fin (R*5)) := record_where pl bits base sink sel
    (W:=W) (by omega : base+2*groups*D≤2^W) (by omega : sink<2^W) p
  have safe : EffectStream.Safe src es := by
    intro av hav
    obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hav
    exact Or.inl (by rcases dest p with h|h <;> omega)
  have replay : (EffectSeed.scatter W src es.length).Exec filled
      (after filled (EffectStream.events es)) (4+6*es.length) :=
    Procedure.Spec.exec (EffectSeed.scatter_spec src es (by omega) safe) filled loaded
  rw [len,Nat.mul_comm R 5] at replay
  have ran : (procedure W base groups D src R γ sink A origins).Exec m
      (after filled (EffectStream.events es)) ((4+6*n)+((4+10*R*(2*e.work+4))+(4+6*(5*R)))) :=
    Procedure.Exec.then erased (Procedure.Exec.then scanRun replay)
  have budget : (4+6*n)+((4+10*R*(2*e.work+4))+(4+6*(5*R)))=(4+6*n)+(8+4130*R) := by
    rw [show e.work=203 from work ..]
    omega
  rw [budget] at ran
  refine ⟨_,ran,?_,?_⟩
  · intro x
    apply read pl bits base sink sel covers (by omega) (by omega) apart
    intro x
    obtain ⟨l,h⟩ := index_bounds base x
    rw [fillFrame _ (.inl (by omega))]
    simp [zero,image,fillSegment,n,Expr.eval,l,h]
  · intro t clearArea tapeArea other
    apply EffectStream.after_at es filled t _ _ (Or.inl ((fillFrame t tapeArea).trans (zeroFrame t clearArea)))
    intro av hav atT
    obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hav
    rcases dest p with h|h <;> omega

end Hierarchy.TaggedShorterSlotWidth

end
end OAI
