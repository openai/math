import OAI.Hierarchy.DescentOldOccurrenceRAM
import OAI.Hierarchy.DescentCensusFields

namespace OAI
/-! # Two stable source streams from actual old cable, color and occupied-site words -/

namespace Hierarchy.DescentOldOccurrenceRAM
open DescentSixParty DescentSixParty.MarkedCensus DescentColonies
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {F P V A C : Type} [Field F] [Fintype V] [DecidableEq V]
  {d k n t g H w : ℕ} {bits : P→ℕ}

def src (f : Fields) := Expr.lookup f.source .row
def dst (f : Fields) := Expr.lookup f.target .row

/-- Regular edges are sorted by (source colony, source site, destination colony)
on the thin side, and by (source colony, destination colony, source site) on the thick side.
Both use physical original edge order to resolve ties. -/
def fields (f : Fields) (name paint : Bank) (g : ℕ) (thick : Bool) : Fin 3→Expr :=
  let target := Expr.lookup name (dst f)
  let eligible := Expr.branch .eq (.lookup f.core .row) (.lit 1)
    (.branch .eq (.lookup paint (src f)) (.lit (if thick then 1 else 0))
      (.lookup name (src f)) (.lit g)) (.lit g)
  ![eligible,if thick then target else src f,if thick then src f else target]

theorem fields_fits (f : Fields) (name paint : Bank) (g base : ℕ) (thick : Bool)
    (hf : f.Fits w base) (hn : name.Fits w base) (hp : paint.Fits w base) :
    ∀j,(fields f name paint g thick j).Fits w base := by
  have s : (src f).Fits w base := ⟨hf.1,trivial⟩
  have dst_ : (Expr.lookup name (dst f)).Fits w base := ⟨hn,hf.2.1,trivial⟩
  intro j
  fin_cases j
  · exact ⟨⟨hf.2.2.2.1,trivial⟩,trivial,⟨⟨hp,s⟩,trivial,⟨hn,s⟩,trivial⟩,trivial⟩
  · cases thick <;> first | exact s | exact dst_
  · cases thick <;> first | exact s | exact dst_

theorem fields_work (f : Fields) (name paint : Bank) (g : ℕ) (thick : Bool) (j : Fin 3) :
    (fields f name paint g thick j).work ≤ 40 := by
  fin_cases j <;> cases thick <;>
    first | exact (by decide : 37≤40) | exact (by decide : 7≤40) | exact (by decide : 12≤40)

variable (W : MarkedWorld F d P bits) (edges : Fin n ≃ W.graph.Edge) (sites : Fin t ≃ W.graph.Site)
    (home : W.graph.Site→C) (code : C↪Fin g) (color : W.graph.Site→Bool)

def origin (thick : Bool) (i : Fin n) : Fin (g+1) :=
  if edges i ∈ W.core ∧ color (W.graph.src (edges i))=thick then
    (code (home (W.graph.src (edges i)))).castSucc else Fin.last g

def sourceKey (i : Fin n) : Fin (max t g) :=
  (sites.symm (W.graph.src (edges i))).castLE (Nat.le_max_left ..)

def targetKey (i : Fin n) : Fin (max t g) :=
  (code (home (W.graph.dst (edges i)))).castLE (Nat.le_max_right ..)

def middle (thick : Bool) := if thick then targetKey (t:=t) W edges home code else sourceKey (g:=g) W edges sites
def lower (thick : Bool) := if thick then sourceKey (g:=g) W edges sites else targetKey (t:=t) W edges home code

variable (pos : W.graph.Site→V) (block : W.graph.Site→Block k) (idx : V≃Fin H)
    (hub : W.graph.Site→Bool) (records : W.graph.Site→List A)

omit [Field F] [Fintype V] [DecidableEq V] in
theorem field_reads (f : Fields) (name paint : Bank) (thick : Bool) (m : Memory w)
    (raw : SourceRows W pos block idx edges sites hub records f m)
    (readName : ∀u,name.read m ((sites.symm u).val:Word w)=((code (home u)).val:Word w))
    (readPaint : ∀i : Fin n,edges i∈W.core → paint.read m ((sites.symm (W.graph.src (edges i))).val:Word w)=
      ((if color (W.graph.src (edges i)) then 1 else 0:ℕ):Word w))
    (wide : 1 < 2^w) (i : Fin n) (j : Fin 3) :
    (fields f name paint g thick j).eval m (i.val:Word w) =
      ((![ (origin W edges home code color thick i).val,
          (middle W edges sites home code thick i).val,
          (lower W edges sites home code thick i).val ] j:ℕ):Word w) := by
  have one : (1:Word w)≠0 := by
    intro eqn
    have z := congrArg Fin.val eqn
    simp [Nat.mod_eq_of_lt wide] at z
  fin_cases j
  · cases thick <;> cases shade : color (W.graph.src (edges i)) <;> by_cases keep : edges i∈W.core <;>
      simp [fields,src,Expr.eval,raw.core,marked,keep,raw.source,readPaint,shade,readName,
        origin,Comparison.test,one,Ne.symm one]
  · cases thick <;> simp [fields,src,dst,Expr.eval,raw.target,raw.source,readName,middle,targetKey,sourceKey]
  · cases thick <;> simp [fields,src,dst,Expr.eval,raw.target,raw.source,readName,lower,targetKey,sourceKey]

omit [Field F] [Fintype V] [DecidableEq V] in
theorem native (f : Fields) (name paint : Bank) (thick : Bool) (base digit : ℕ) (m : Memory w)
    (raw : SourceRows W pos block idx edges sites hub records f m)
    (readName : ∀u,name.read m ((sites.symm u).val:Word w)=((code (home u)).val:Word w))
    (readPaint : ∀i : Fin n,edges i∈W.core → paint.read m ((sites.symm (W.graph.src (edges i))).val:Word w)=
      ((if color (W.graph.src (edges i)) then 1 else 0:ℕ):Word w))
    (hf : f.Fits w base) (hn : name.Fits w base) (hp : paint.Fits w base) (wide : 1 < 2^w)
    (fits : n≤2^digit) (room : finish base n g (max t g) digit<2^w) :
    ∃o, (program w base n g (max t g) digit (fields f name paint g thick)).Exec m o
        (ticks base n g (max t g) (fields f name paint g thick)) ∧
      (∀ j : Fin n,(output base n g (max t g) digit).read o (j.val:Word w)=
        ((DescentTerminalSortRAM.order (origin W edges home code color thick)
          (middle W edges sites home code thick) (lower W edges sites home code thick) j).val : Word w)) ∧
      ∀x < base,o x=m x := by
  exact ⟨_,run base digit _ _ _ _ m (fields_fits f name paint g base thick hf hn hp)
    (field_reads W edges sites home code color pos block idx hub records f name paint thick m raw readName readPaint wide)
    fits room⟩

end
end Hierarchy.DescentOldOccurrenceRAM

end OAI
