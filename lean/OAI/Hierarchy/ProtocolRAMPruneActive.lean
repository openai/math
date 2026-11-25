import OAI.Hierarchy.ProtocolRAMPruneFlag

namespace OAI
/-! # Pruning when only the positive-width endpoints are stored in the layer directory -/

noncomputable section
namespace Hierarchy.ProtocolRAM.PruneFlag
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open ProtocolRAMEmit TaggedPrune CorrectionFrame
open scoped Classical BigOperators Fin.CommRing
variable {W n h w k M den : ℕ} {b : Fin k → ℕ}

/-- A zero-width row costs zero for any pair of native layer lookup results. -/
theorem reads_active (D : Layout h w b) (rows : Fin n → Row) (m : Memory W)
    (dst maxCode : ℕ) (endpoints metrics layers : Bank)
    (ep : endpoints.base=dst) (mt : metrics.base=dst+3*n)
    (es : 3*n≤endpoints.size) (ms : 3*n≤ metrics.size) (room : 3*n<2^W)
    (cap : maxCode<2^W) (codes : ∀i,(rows i).lengthCode≤ maxCode)
    (space : Fintype.card (Location k)<2^W)
    (advice : ∀ i, 0 < (rows i).width → ∀ s ∈ [ (rows i).endpoint, (rows i).opposite ],
      layers.read (emitted dst rows m) (s:Word W)=(layerCode D s:Word W)) :
    SumScores.Reads (emitted dst rows m) (term endpoints metrics layers maxCode) (fun i=>charge D (rows i)) := by
  intro i
  let mem := emitted dst rows m
  let r := rows i
  have fields (j : Fin 3) :
      (field endpoints j).eval mem (i.val:Word W)=(r.field (endpointFields j):Word W) ∧
      (field metrics j).eval mem (i.val:Word W)=(r.field (metricFields j):Word W) := by
    rw [field_read endpoints j _ i es room,field_read metrics j _ i ms room,ep,mt]
    exact ⟨(emitted_read dst rows m i j).1,(emitted_read dst rows m i j).2.1⟩
  have e0 : (field endpoints 0).eval mem (i.val:Word W)=(r.endpoint:Word W) := (fields 0).1
  have e1 : (field endpoints 1).eval mem (i.val:Word W)=(r.opposite:Word W) := (fields 1).1
  have w1 : (field metrics 1).eval mem (i.val:Word W)=(r.width:Word W) := (fields 1).2
  have l2 : (field metrics 2).eval mem (i.val:Word W)=(r.lengthCode:Word W) := (fields 2).2
  have code : ((field metrics 2).eval mem (i.val:Word W)).val ≤ maxCode := by
    rw [l2,Fin.val_cast_of_lt ((codes i).trans_lt cap)]
    exact codes i
  change (term endpoints metrics layers maxCode).eval mem (i.val:Word W) = (charge D r:Word W)
  by_cases live : 0 < r.width
  · have word_lt (s : ℕ) : layerCode D s<2^W := by
      unfold layerCode
      split
      · exact (Fin.isLt _).trans space
      · exact Nat.two_pow_pos _
    have left : layers.read mem (r.endpoint:Word W)=(layerCode D r.endpoint:Word W) := advice i live _ (by simp [r])
    have right : layers.read mem (r.opposite:Word W)=(layerCode D r.opposite:Word W) := advice i live _ (by simp [r])
    have equal : ((layerCode D r.endpoint:Word W)=(layerCode D r.opposite:Word W)) ↔
        layerCode D r.endpoint=layerCode D r.opposite := by
      rw [Fin.ext_iff,Fin.val_cast_of_lt (word_lt _),Fin.val_cast_of_lt (word_lt _)]
    simp only [term,Expr.eval,e0,e1,left,right,Comparison.test,beq_iff_eq,equal,
      eval_boundedMul _ _ _ _ _ code cap,w1,l2,charge]
    split <;> simp_all [mul_comm]
  · have zero : r.width=0 := by omega
    have blank : charge D r=0 := by simp [charge,zero]
    simp [term,Expr.eval,blank,eval_boundedMul _ _ _ _ _ code cap,w1,zero]

/-- The original pruning CPU computes the exact keep bit from its physical positive rows. -/
theorem run_exact_active {D : Layout h w b} {rows : Fin n → Row} (G : Geometry D M den rows)
    (m : Memory W) (dst maxCode out ticks : ℕ) (endpoints metrics layers : Bank)
    (hw : 0<w) (hd : 0<den)
    (ep : endpoints.base=dst) (mt : metrics.base=dst+3*n)
    (es : 3*n≤endpoints.size) (ms : 3*n≤ metrics.size) (inputRoom : 3*n<2^W)
    (cap : maxCode<2^W) (codes : ∀i,(rows i).lengthCode≤ maxCode)
    (space : Fintype.card (Location k)<2^W)
    (advice : ∀ i, 0 < (rows i).width → ∀ s ∈ [(rows i).endpoint,(rows i).opposite],
      layers.read (emitted dst rows m) (s:Word W)=(layerCode D s:Word W))
    (fit : (term endpoints metrics layers maxCode).Fits W out) (room : out+(n+1)<2^W)
    (threshold : 2*M*(∑ j,b j)*den-ticks*w*den<2^W)
    (sumroom : (∑ i, charge D (rows i))<2^W) :
    let bound := 2*M*(∑ j,b j)*den-ticks*w*den
    let e := term endpoints metrics layers maxCode
    let result := output D rows out bound (emitted dst rows m)
    (SumScores.procedure W out n bound e).Exec (emitted dst rows m) result
      (4+(n+1)*(42+2*e.work)) ∧ result (out+n) = if G.links.Keep ticks then 1 else 0 := by
  let bound := 2*M*(∑ j,b j)*den-ticks*w*den
  let e := term endpoints metrics layers maxCode
  let q (i : Fin n) := charge D (rows i)
  let start := emitted dst rows m
  have score := reads_active D rows m dst maxCode endpoints metrics layers ep mt es ms inputRoom cap codes space advice
  have execution : (SumScores.procedure W out n bound e).Exec start
      (fillSegment out (n+1) (SumScores.word out bound q) start) (4+(n+1)*(42+2*e.work)) :=
    by
      have spec : (SumScores.procedure W out n bound e).Spec (fun a=>SumScores.Reads a e q)
          (fun a result=>result=fillSegment out (n+1) (SumScores.word out bound q) a) (4+(n+1)*(42+2*e.work)) :=
        SumScores.run out bound e q fit room threshold sumroom
      intro P R K machine pc reg pub exit instr data cfg mem entry same
      subst mem
      exact spec machine pc reg pub exit instr data cfg start entry score
  refine ⟨execution,?_⟩
  change fillSegment out (n+1) (SumScores.word out bound q) start (out+n)=_
  simp only [SumScores.read_flag,keep_iff G ticks hw hd,bound,q]

end Hierarchy.ProtocolRAM.PruneFlag
end

end OAI
