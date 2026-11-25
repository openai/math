import OAI.ThreeFlat.Diagonal.CompressorHalfPorts
import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily
import OAI.ThreeFlat.Diagonal.PhysicalChargeArray
import OAI.ThreeFlat.Diagonal.PhysicalRunRecasts
import OAI.ThreeFlat.Diagonal.HistoryChartPointers

namespace OAI
/-! # Assembling a physical run from the actual stages in its vertex charts -/

noncomputable section
namespace ThreeFlat.Diagonal
open LinearAlgebra.SpectralBooks HistoryContraction
open scoped BigOperators Classical

namespace HistoryRelabel
variable {V E U D Pins : Type} [Fintype V] [Fintype E] [Fintype U] [Fintype D]
variable {G : PortGraph V E} {H : PortGraph U D} {w : E→ℕ} {b : D→ℕ}
variable (I : Iso (WordLayout.shape G w) (WordLayout.shape H b)) (L : WordLayout G w Pins)

/-- Reindex one site's entire old half order along the chart equivalence. This
preserves its numerical outgoing and incoming ordinals. -/
def Iso.pushWord : WordLayout H b Pins where
  count v := L.count (I.site.symm v)
  order v := ((L.order (I.site.symm v)).trans (I.port (I.site.symm v))).trans
    (Equiv.cast (congrArg H.Port (I.site.apply_symm_apply v)))
  ext v := L.ext (I.site.symm v)
  pin v := L.pin (I.site.symm v)

def Iso.pushExternal (u : V) : Fin (L.ext u)→Fin ((I.pushWord L).ext (I.site u)) :=
  Fin.cast (congrArg L.ext (I.site.symm_apply_apply u)).symm

theorem Iso.pushExternal_pin (u : V) (x : Pins) (a : Fin (L.ext u)) :
    (I.pushWord L).pin (I.site u) x (I.pushExternal L u a)=L.pin u x a := by
  have pinCast {v u : V} (e : v = u) (i : Fin (L.ext u)) :
      L.pin v x (Fin.cast (congrArg L.ext e).symm i) = L.pin u x i := by cases e; rfl
  exact pinCast (I.site.symm_apply_apply u) a

omit [Fintype U] [Fintype D] in
/-- Equality of site indices transports the port membership proof with its edge and side intact. -/
private theorem port_cast_val {u v : U} (e : u=v) (q : H.Port u) :
    (Equiv.cast (congrArg H.Port e) q).val=q.val := by cases e;rfl

theorem push_order_val (v : U) {u : V} (e : I.site.symm v=u) (i : Fin (L.count u)) :
    ((I.pushWord L).order v (i.cast (congrArg L.count e).symm)).val=
      (I.edge (L.order u i).val.1,(L.order u i).val.2) := by
  subst u
  exact port_cast_val (I.site.apply_symm_apply v) _

theorem push_order_lengths (hw : ∀ e,w e=b (I.edge e)) (u : V) (i : Fin (L.count u)) :
    (I.pushWord L).ports.lengths (I.site u) (i.cast (congrArg L.count (I.site.symm_apply_apply u)).symm)=
      L.ports.lengths u i := by
  change b ((I.pushWord L).order (I.site u) _).val.1=w (L.order u i).val.1
  exact (congrArg (fun p : D × Bool => b p.1)
    (push_order_val I L (I.site u) (I.site.symm_apply_apply u) i)).trans (hw _).symm

theorem Iso.pushWord_halfBits (hw : ∀ e,w e=b (I.edge e)) (u : V) :
    (I.pushWord L).ports.halfBits (I.site u)=L.ports.halfBits u := by
  symm
  exact Fintype.sum_equiv (finCongr (congrArg L.count (I.site.symm_apply_apply u)).symm)
    _ _ (fun i=>(push_order_lengths I L hw u i).symm)

theorem Iso.pushWord_halfBits_at (hw : ∀ e,w e=b (I.edge e)) (z : U) :
    (I.pushWord L).ports.halfBits z=L.ports.halfBits (I.site.symm z) := by
  have h:=I.pushWord_halfBits L hw (I.site.symm z)
  exact (congrArg (I.pushWord L).ports.halfBits (I.site.apply_symm_apply z)).symm.trans h

private theorem flattened_cast_val {n m : ℕ} (e : n=m) (f : Fin n→ℕ) (g : Fin m→ℕ)
    (same : ∀ i,g (i.cast e)=f i) (i : Fin n) (i' : Fin m) (indices : i'.val=i.val)
    (j : Fin (f i)) (j' : Fin (g i')) (bits : j'.val=j.val) :
    (finSigmaFinEquiv (n:=g) ⟨i',j'⟩).val=(finSigmaFinEquiv (n:=f) ⟨i,j⟩).val := by
  subst m
  have gf : g=f:=funext (fun z=>same z)
  subst g
  have ii : i'=i:=Fin.ext indices
  subst i'
  have jj : j'=j:=Fin.ext bits
  subst j'
  rfl

theorem Iso.pushWord_halfPointer_val (hw : ∀ e,w e=b (I.edge e)) (u : V) (j : Fin (L.ports.halfBits u)) :
    (halfPointer I L.ports (I.pushWord L).ports hw u j).val=j.val := by
  obtain ⟨⟨i,k⟩,rfl⟩:=(finSigmaFinEquiv (n:=L.ports.lengths u)).surjective j
  let e:=(congrArg L.count (I.site.symm_apply_apply u)).symm
  have ord : (I.pushWord L).order (I.site u) (i.cast e)=I.port u (L.order u i) :=
    Subtype.ext (push_order_val I L (I.site u) (I.site.symm_apply_apply u) i)
  have inv : ((I.pushWord L).order (I.site u)).symm (I.port u (L.order u i))=i.cast e :=
    ((I.pushWord L).order (I.site u)).symm_apply_eq.mpr ord.symm
  simp only [halfPointer,PortLayout.portBit]
  apply flattened_cast_val e (L.ports.lengths u) ((I.pushWord L).ports.lengths (I.site u))
    (push_order_lengths I L hw u)
  · let ordVal (p : (o : Fin (L.ports.count u)) × Fin (L.ports.lengths u o)) :=
      ((I.pushWord L).ports.port (I.site u)).symm (I.port u (L.ports.port u p.1))
    exact (congrArg (fun p => (ordVal p).val) (finSigmaFinEquiv.symm_apply_apply ⟨i,k⟩)).trans
      (congrArg Fin.val inv)
  · exact congrArg (fun p : (o : Fin (L.ports.count u)) × Fin (L.ports.lengths u o) => p.2.val)
      (finSigmaFinEquiv.symm_apply_apply ⟨i,k⟩)

theorem Iso.pushWord_pointer_val (hw : ∀ e,w e=b (I.edge e)) (u : V) (j : Fin (L.ports.form.width u)) :
    (pointer I L.ports (I.pushWord L).ports hw (I.pushExternal L) u j).val=j.val := by
  let B := (I.pushWord L).ports
  let left := fun i : Fin (L.ports.ext u) => (I.pushExternal L u i).castAdd (B.halfBits (I.site u))
  let right := fun i : Fin (L.ports.halfBits u) => Fin.natAdd (B.ext (I.site u)) (halfPointer I L.ports B hw u i)
  refine Fin.addCases (fun i=>?_) (fun i=>?_) j
  · exact congrArg Fin.val (Fin.append_left left right i)
  · refine (congrArg Fin.val (Fin.append_right left right i)).trans ?_
    exact congrArg₂ Nat.add (congrArg L.ext (I.site.symm_apply_apply u)) (I.pushWord_halfPointer_val L hw u i)

def Iso.onStage {F : Type} [Field F] {R : Rewrite (WordLayout.shape H b) F} {idx : Fin R.count}
    {next : Form (R.target idx) Pins} (stage : Stage R idx (I.pushWord L).ports.form next)
    (hw : ∀ e,w e=b (I.edge e)) (hv : ∀ e z,(I.label e z).val=z.val) :
    Stage (I.rewrite R) idx L.ports.form next :=
  chartStage I L.ports (I.pushWord L).ports hw (wordBits I L (I.pushWord L) hw hv) stage
    (I.pushExternal L) (I.pushExternal_pin L)
end HistoryRelabel

namespace HistoryContraction.WordLayout
variable {V E U D Pins F : Type} [Fintype V] [Fintype E] [Fintype U] [Fintype D] [Field F]
variable {G : PortGraph V E} {H : PortGraph U D} {w : E→ℕ} {b : D→ℕ}
variable (L : WordLayout G w Pins) (fresh : WordLayout H b Pins)

def inherited (own : V→U)
    (count : U→ℕ) (child : ∀ v, Fin (count v)≃{i // own i=v}) : WordLayout H b Pins where
  count := fresh.count
  order := fresh.order
  ext v := ∑ i,L.ext (child v i).val
  pin v x := MotifBinaryPacking.flatten (fun i=>L.ext (child v i).val) (fun i=>L.pin (child v i).val x)

end HistoryContraction.WordLayout

namespace PhysicalStage
variable {F Pins : Type} [Field F] {d l D m : ℕ} {A : State d l}

abbrev State.Words (A : State d l) (Pins : Type) := WordLayout A.shape.graph A.width Pins

/-- The physical scheduler enumerates every site's outgoing halves first,
then its incoming halves in the same numbered slots. -/
structure State.OrderedHalves (A : State d l) (K : A.Words Pins) : Prop where
  count : ∀ z,K.count z=2*d
  edge : ∀ z (i : Fin (K.count z)), (K.order z i).val.1=
    CompressorPacking.Native.ShrinkStage.Halves.sourceHalf A.graph (A.chart.symm z) (i.cast (count z))

theorem State.OrderedHalves.start {A : State d l} {K : A.Words Pins} (o : A.OrderedHalves K)
    (v : A.Site) (b : Fin (K.count v)) :
    CompressorPacking.Native.ShrinkStage.Halves.prefixValue A.graph A.width (A.chart.symm v) (b.cast (o.count v)) =
      ∑ k : Fin b.val, K.ports.lengths v (Fin.castLE b.isLt.le k) := by
  let f:=fun i : Fin (2*d)=>A.width (CompressorPacking.Native.ShrinkStage.Halves.sourceHalf A.graph (A.chart.symm v) i)
  let e : Fin b.val ≃ {k : Fin (2*d) // k.val<b.val} :=
    ⟨fun k=>⟨⟨k.val,k.isLt.trans (b.isLt.trans_eq (o.count v))⟩,k.isLt⟩,fun k=>⟨k.val.val,k.property⟩,
      fun _=>rfl,fun _=>rfl⟩
  change (∑ i : Fin (2*d), if i.val<b.val then f i else 0)=_
  rw [←Finset.sum_filter,←Finset.sum_subtype_eq_sum_filter,Finset.subtype_univ]
  calc
    _ = ∑ k : Fin b.val, f (e k).val := (e.sum_comp (fun i=>f i.val)).symm
    _ = _ := Finset.sum_congr rfl (fun k _=>congrArg A.width (o.edge v (Fin.castLE b.isLt.le k)).symm)

/-- The same child order that builds the target external word prefix also
identifies the old site and position for each one of its bits. -/
structure Move.WordStep (R : Move F A D m) (Pins : Type) (L : A.Words Pins) (i : Fin R.rules.count) where
  words : (R.next i).Words Pins
  stage : Stage R.rules i L.ports.form ((R.target_eq i).symm ▸ words.ports.form)
  halves : (R.next i).OrderedHalves words
  origin : ∀ z,Fin (words.ext z)→Σ u : {u // R.parent i u=z},Fin (L.ext u.val)
  read : ∀ z j pin,words.pin z pin j=L.pin (origin z j).1.val pin (origin z j).2
  originOrder : ∀ v,
    let z := (Equiv.cast (congrArg Shape.Site (R.target_eq i))).symm v
    let n := fun k : Fin (stage.count z) => L.ext (stage.child z k).val
    ∃ eqn : words.ext v=∑ k,n k, ∀ j : Fin (words.ext v),
      let p : Σ k,Fin (n k) := finSigmaFinEquiv.symm (j.cast eqn)
      ((origin v j).1.val,(origin v j).2.val)=((stage.child z p.1).val,p.2.val)

def Move.Assembler (R : Move F A D m) (Pins : Type) :=
  ∀ (L : A.Words Pins) (i : Fin R.rules.count),R.WordStep Pins L i

def Move.castAssembler {D' : ℕ} (e : D=D') (R : Move F A D m) (J : R.Assembler Pins) :
    (e ▸ R : Move F A D' m).Assembler Pins := by cases e; exact J

def Move.inputAssembler {l' : ℕ} (e : l=l') (A : State d l)
    (R : Move F (e ▸ A : State d l') D m) (J : R.Assembler Pins) :
    (Move.recastInputLanes e A R).Assembler Pins := by cases e; exact J

def Run.WordSteps (Pins : Type) : {d l : ℕ} → {A : State d l} → Run F A → Type 1
  | _,_,_,.done _ => PUnit
  | _,_,_,.step R next => R.Assembler Pins × (∀ i,WordSteps Pins (next i))

structure Run.Assembler (R : Run F A) (Pins : Type) where
  steps : Run.WordSteps Pins R

private def castAssembly {X Y : Shape} (e : X=Y) (P : Plan F X) (L : Form X Pins) (J : P.Assembly L) :
    (e ▸ P : Plan F Y).Assembly (e ▸ L) := by cases e; exact J

def Run.wordAssembly : {d l : ℕ} → {A : State d l} → (r : Run F A) → Run.WordSteps Pins r →
    (L : A.Words Pins) → r.plan.Assembly L.ports.form
  | _,_,_,.done _,_,_ => PUnit.unit
  | _,_,_,.step R next,J,L => fun i=>
    let step:=J.1 L i
    ⟨(R.target_eq i).symm ▸ step.words.ports.form,step.stage,
      castAssembly (R.target_eq i).symm _ _ ((next i).wordAssembly (J.2 i) step.words)⟩

instance {r : Run F A} : CoeFun (r.Assembler Pins)
    (fun _ => ∀ L : A.Words Pins, r.plan.Assembly (L.ports.form)) where
  coe J:=r.wordAssembly J.steps

def Run.assembleStep (R : Move F A D m) (next : ∀ i,Run F (R.next i))
    (J : R.Assembler Pins) (K : ∀ i,(next i).Assembler Pins) : (Run.step R next).Assembler Pins :=
  ⟨J,fun i=>(K i).steps⟩

def Run.endWords : {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) →
    Run.WordSteps Pins r → A.Words Pins → (r.terminalLayer h).state.Words Pins
  | _,_,_,.done _,_,_,L => L
  | _,_,_,.step R next,h,J,L => (next h.1).endWords (tailHistory R next h) (J.2 h.1) (J.1 L h.1).words

theorem Run.endWords_halves (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r) (L : A.Words Pins)
    (initial : A.OrderedHalves L) : (r.terminalLayer h).state.OrderedHalves (r.endWords h J L) := by
  induction r with
  | done A=>exact initial
  | step R next ih=>exact ih h.1 (tailHistory R next h) (J.2 h.1) (J.1 L h.1).words (J.1 L h.1).halves

def Run.extAncestor : {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) →
    (J : Run.WordSteps Pins r) → (L : A.Words Pins) → (z : (r.terminalLayer h).state.Site) →
      Fin ((r.endWords h J L).ext z) → Σ u,Fin (L.ext u)
  | _,_,_,.done _,_,_,_,z,j=>⟨z,j⟩
  | _,_,_,.step R next,h,J,L,z,j=>
    let step:=J.1 L h.1
    let child:=(next h.1).extAncestor (tailHistory R next h) (J.2 h.1) step.words z j
    let q:=step.origin child.1 child.2
    ⟨q.1.val,q.2⟩

theorem Run.extAncestor_read (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (z : (r.terminalLayer h).state.Site) (j : Fin ((r.endWords h J L).ext z)) (pin : Pins) :
    (r.endWords h J L).pin z pin j=L.pin (r.extAncestor h J L z j).1 pin (r.extAncestor h J L z j).2 := by
  induction r with
  | done A=>rfl
  | step R next ih=>
    let step:=J.1 L h.1
    exact (ih h.1 (tailHistory R next h) (J.2 h.1) step.words z j).trans (step.read _ _ pin)

private theorem cast_destination {X Y : Shape} (e : X=Y) (P : Plan F X)
    (h : (e ▸ P : Plan F Y).History) (u : Y.Site) :
    HEq ((e ▸ P : Plan F Y).destination h u)
      (P.destination (Run.historyOfCast e P h) ((congrArg Shape.Site e.symm) ▸ u)) := by cases e;rfl

theorem Run.extAncestor_destination (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (z : (r.terminalLayer h).state.Site) (j : Fin ((r.endWords h J L).ext z)) :
    HEq (r.plan.destination h (r.extAncestor h J L z j).1) z := by
  induction r with
  | done A=>rfl
  | step R next ih=>
    let s:=J.1 L h.1
    let y:=(next h.1).extAncestor (tailHistory R next h) (J.2 h.1) s.words z j
    let x:=s.origin y.1 y.2
    have home : R.parent h.1 x.1.val=y.1:=x.1.property
    apply (cast_destination (R.target_eq h.1).symm (next h.1).plan h.2 (R.rules.owner h.1 x.1.val)).trans
    change HEq ((next h.1).plan.destination (tailHistory R next h) (R.parent h.1 x.1.val)) z
    rw [home]
    exact ih h.1 (tailHistory R next h) (J.2 h.1) s.words z j

private def forestUncast {X Y : Shape} (e : X=Y) (V : Form X Pins) (N : Forest F (e ▸ V : Form Y Pins)) :
    Forest F V := by cases e;exact N

private theorem cast_assembled {X Y : Shape} (e : X=Y) (P : Plan F X) (V : Form X Pins) (J : P.Assembly V)
    (h : (e ▸ P : Plan F Y).History) (N : Forest F (e ▸ V : Form Y Pins)) :
    HEq ((e ▸ P : Plan F Y).assemble h (castAssembly e P V J) N).1
      (P.assemble (Run.historyOfCast e P h) J (forestUncast e V N)).1 := by
  cases e
  rfl

theorem Run.endWords_form (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (N : Forest F L.ports.form) :
    HEq (r.plan.assemble h (r.wordAssembly J L) N).1 (r.endWords h J L).ports.form := by
  induction r with
  | done A=>rfl
  | step R next ih=>
    let x:=J.1 L h.1
    exact (cast_assembled (R.target_eq h.1).symm (next h.1).plan x.words.ports.form
      ((next h.1).wordAssembly (J.2 h.1) x.words) h.2 (x.stage.assemble N)).trans
      (ih h.1 (tailHistory R next h) (J.2 h.1) x.words _)

def Run.inputAssembler {l' : ℕ} (e : l=l') (A : State d l)
    (R : Run F (e ▸ A : State d l')) (J : R.Assembler Pins) : (Program.recast e A R).Assembler Pins := by
  cases e; exact J

def Move.outputAssembler {D' : ℕ} (e : D=D') (R : Move F A D m) (J : R.Assembler Pins) :
    (Program.recastMove e R).Assembler Pins := by cases e; exact J
end PhysicalStage
end ThreeFlat.Diagonal

namespace ThreeFlat.Diagonal.PhysicalStage
open HistoryContraction
noncomputable section
variable {F Pins : Type} [Field F] {d l D m : ℕ} {A : State d l}

omit [Field F] in
private theorem uncast_tree_price {X Y : Shape} (e : X=Y) (L : Form X Pins)
    (N : Forest F (e ▸ L : Form Y Pins)) (v : X.Site) (price : ∀ {p},Tree F p→ℕ) :
    price (forestUncast e L N v)=price (N (cast (congrArg Shape.Site e) v)) := by cases e;rfl

private theorem cast_tail_price {X Y : Shape} (e : X=Y) (P : Plan F X) (L : Form X Pins) (J : P.Assembly L)
    (h : (e ▸ P : Plan F Y).History) (N : Forest F (e ▸ L : Form Y Pins))
    (v : ((e ▸ P : Plan F Y).finish h).Site) (w : (P.finish (Run.historyOfCast e P h)).Site)
    (same : HEq v w) (price : ∀ {p},Tree F p→ℕ) :
    price ((((e ▸ P : Plan F Y).assemble h (castAssembly e P L J) N).2) v)=
      price ((P.assemble (Run.historyOfCast e P h) J (forestUncast e L N)).2 w) := by
  cases e
  cases eq_of_heq same
  rfl

/-- Transfer any numerical property through the lane cast between the real stage
and the rest of the assembled program. -/
theorem Run.step_tree_price {R : Move F A D m} {next : ∀ i,Run F (R.next i)}
    (h : (Run.step R next).plan.History) (J : Run.WordSteps Pins (Run.step R next)) (L : A.Words Pins)
    (N : Forest F L.ports.form) (v : ((Run.step R next).plan.finish h).Site)
    (w : ((next h.1).plan.finish (tailHistory R next h)).Site) (same : HEq v w)
    (price : ∀ {p},Tree F p→ℕ) (P : ℕ→Prop)
    (tail : let s:=J.1 L h.1
      ∀ N' : Forest F s.words.ports.form,
        (∀ x,price (N' x)=price (s.stage.assemble N (cast (congrArg Shape.Site (R.target_eq h.1).symm) x))) →
        P (price (((next h.1).plan.assemble (tailHistory R next h)
          ((next h.1).wordAssembly (J.2 h.1) s.words) N').2 w))) :
    P (price (((Run.step R next).plan.assemble h ((Run.step R next).wordAssembly J L) N).2 v)) := by
  let s:=J.1 L h.1
  let K:=s.words.ports.form
  rw [show price (((Run.step R next).plan.assemble h ((Run.step R next).wordAssembly J L) N).2 v)=_ from
    cast_tail_price (R.target_eq h.1).symm (next h.1).plan K ((next h.1).wordAssembly (J.2 h.1) s.words)
      h.2 (s.stage.assemble N) v w same price]
  exact tail _ (fun x=>uncast_tree_price (R.target_eq h.1).symm K (s.stage.assemble N) x price)

end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage
open HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F Pins : Type} [Field F] {d l D m : ℕ} {A : State d l}

/-- The site's physical port list accounts for every incoming and outgoing wire. -/
theorem State.OrderedHalves.halfBits_eq_incident {K : A.Words Pins} (ordered : A.OrderedHalves K)
    (z : A.Site) : K.ports.halfBits z=A.incidentWidth z := by
  let e := finCongr (ordered.count z)
  let extent (i : Fin (2*d)) := A.width (CompressorPacking.Native.ShrinkStage.Halves.sourceHalf A.graph (A.chart.symm z) i)
  calc
    K.ports.halfBits z = ∑ i : Fin (K.count z), extent (e i) :=
      Finset.sum_congr rfl (fun i _=>congrArg A.width (ordered.edge z i))
    _ = ∑ i,extent i := e.sum_comp extent
    _ = _ := half_total A.graph A.width (A.chart.symm z)

theorem Move.WordStep.child_sum {R : Move F A D m} {L : A.Words Pins} {i : Fin R.rules.count}
    (s : R.WordStep Pins L i) (v : (R.next i).Site) (weights : A.Site→ℕ) :
    let z:=(Equiv.cast (congrArg Shape.Site (R.target_eq i))).symm v
    (∑ k, weights (s.stage.child z k).val)=∑ x : {x // R.parent i x=v},weights x.val := by
  let e := Equiv.cast (congrArg Shape.Site (R.target_eq i))
  let iso : {x // R.parent i x=v} ≃ {x // R.rules.owner i x=e.symm v} :=
    Equiv.subtypeEquivRight fun x => by
      change (e (R.rules.owner i x)=v) ↔ _
      constructor
      · intro h
        simpa only [Equiv.symm_apply_apply] using congrArg e.symm h
      · intro h
        exact (congrArg e h).trans (e.apply_symm_apply v)
  exact ((s.stage.child (e.symm v)).sum_comp (fun x=>weights x.val)).trans
    (iso.sum_comp (fun x=>weights x.val)).symm

theorem Move.WordStep.ext_fiber {R : Move F A D m} {L : A.Words Pins} {i : Fin R.rules.count}
    (s : R.WordStep Pins L i) (v : (R.next i).Site) :
    s.words.ext v=∑ x : {x // R.parent i x=v},L.ext x.val := by
  obtain ⟨eqn,_⟩:=s.originOrder v
  exact eqn.trans (s.child_sum v L.ext)

theorem Move.WordStep.width_push {R : Move F A D m} {L : A.Words Pins} {i : Fin R.rules.count}
    (s : R.WordStep Pins L i) (prior : A.Site→ℕ) (localCost : (R.next i).Site→ℕ)
    (width : ∀ x,L.ports.form.width x≤2*prior x) (floor : ∀ x,1+(R.next i).incidentWidth x≤localCost x)
    (x : (R.next i).Site) : s.words.ports.form.width x≤2*R.push i localCost prior x := by
  have smaller (y : A.Site) : L.ext y≤2*prior y:=(Nat.le_add_right _ (L.ports.halfBits y)).trans (width y)
  have words:=Finset.sum_le_sum (s:=Finset.univ) (fun (y : {y // R.parent i y=x}) _=>smaller y.val)
  rw [←Finset.mul_sum,←s.ext_fiber x] at words
  have half:=s.halves.halfBits_eq_incident x
  have room:=floor x
  change s.words.ext x+s.words.ports.halfBits x≤2*(localCost x+_)
  omega

end
end ThreeFlat.Diagonal.PhysicalStage

end
end OAI
