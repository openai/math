import OAI.Hierarchy.ProbeCoreCode
import OAI.Hierarchy.ProbeReportLabels
import OAI.Hierarchy.ProbeCoreGeometry
import OAI.Hierarchy.TaggedWireBoardLayout
import OAI.Hierarchy.ProtocolRAMPrune

namespace OAI
/-! # Global pruning geometry of the actual core and activated positive links -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open AdaptiveProbe ReportSockets ProtocolRAMEmit
open scoped Classical

variable {h W k attempts : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : Marks h W k attempts)

abbrev Catalogue := Edges S h (2^W) k ⊕ Bought S π depth marked

def actualEnds : Catalogue S π depth marked → Site h (2^W) k × Site h (2^W) k
  | .inl e => ends π e
  | .inr e => (geometry S π depth marked (.inr e) false,geometry S π depth marked (.inr e) true)

def scaleOf : Catalogue S π depth marked → ℝ := Sum.elim (coreScale (dyadicScale W)) (fun _=>dyadicScale W)

def lenCode (M : ℕ) : Catalogue S π depth marked → ℕ := Sum.elim (coreCode S M) (fun _=>1)

theorem actual_distinct (e : Catalogue S π depth marked) :
    (actualEnds S π depth marked e).1 ≠ (actualEnds S π depth marked e).2 := by
  rcases e with e|⟨a,p⟩
  · rcases e with f|⟨⟨p,t⟩,l⟩
    · rcases f with ⟨c,j,s⟩|⟨c,ax,s,u⟩|⟨f,l⟩|⟨⟨t,g,o,i⟩,l⟩
      · simp [actualEnds,ends,freeEnds]
      · intro eq
        have axis := congrArg Prod.fst (Option.some.inj (congrArg Prod.snd eq))
        exact (ne_of_lt ax.property) axis
      · intro eq
        have cols : f.val.1=f.val.2 := congrArg Prod.fst eq
        exact (ne_of_lt f.property.2) (congrArg _ cols)
      · simp [actualEnds,ends,freeEnds,inputCol,outputCol]
    · simp [actualEnds,ends,inputCol,outputCol]
  · intro eq
    have cols := congrArg Prod.fst eq
    have same := Sum.inl.inj (Sum.inr.inj cols)
    have sockets := (stripPlace S π depth (marked a) p).injective same
    exact Bool.false_ne_true ((probeEnds depth).injective sockets)

theorem scaleOf_nonneg (e : Catalogue S π depth marked) : 0 ≤ scaleOf S π depth marked e := by
  have nn : 0≤dyadicScale W := by unfold dyadicScale; positivity
  rcases e with (f|x)|b <;> first | exact nn | exact le_rfl

theorem layers (M : ℕ) (e : Catalogue S π depth marked) :
    let z := actualEnds S π depth marked e
    (z.1.2 ≠ z.2.2 → scaleOf S π depth marked e=0) ∧
      M*dist (CorrectionFrame.point z.1.2) (CorrectionFrame.point z.2.2)≤(lenCode S π depth marked M e:ℝ) := by
  rcases e with e | ⟨a,p⟩
  · exact ⟨cross_scale_zero π _ e, (layer_distance π M e).trans_eq (coreCode_read S M e).symm⟩
  · simp [actualEnds,ReportSockets.geometry,lenCode]

/-- The physical emitter may order its rows and orient their endpoints
either way. Its three observed integer words suffice to obtain every
pruning condition for the concrete public layout. -/
def pruning {n : ℕ} (w R M : ℕ) (rows : Fin n → ProtocolRAMEmit.Row)
    (edge : ActiveRows rows → Catalogue S π depth marked) (flip : ActiveRows rows → Bool)
    (endsRead : ∀ i,let z := actualEnds S π depth marked (edge i)
      (rows i.val).endpoint=(siteNumber h (2^W) k (if flip i then z.2 else z.1)).val ∧
      (rows i.val).opposite=(siteNumber h (2^W) k (if flip i then z.1 else z.2)).val)
    (lengthRead : ∀ i,(rows i.val).lengthCode=lenCode S π depth marked M (edge i)) :
    Geometry (boardLayout h (2^W) k w R) M 1 rows := by
  let D := boardLayout h (2^W) k w R
  let e := actualEnds S π depth marked
  let a (i : ActiveRows rows) := if flip i then (e (edge i)).2 else (e (edge i)).1
  let b (i : ActiveRows rows) := if flip i then (e (edge i)).1 else (e (edge i)).2
  let number := siteNumber h (2^W) k
  have reads (i : ActiveRows rows) : (rows i.val).endpoint=(number (a i)).val ∧
      (rows i.val).opposite=(number (b i)).val := endsRead i
  have distinct (i : ActiveRows rows) : (rows i.val).endpoint ≠ (rows i.val).opposite := by
    rw [(reads i).1,(reads i).2]
    intro eq
    have ne := actual_distinct S π depth marked (edge i)
    have ident := number.injective (Fin.ext eq)
    cases hflip : flip i <;> simp [a,b,hflip,e] at ident <;> tauto
  have fits (i : ActiveRows rows) : (rows i.val).endpoint≤D.last ∧ (rows i.val).opposite≤D.last := by
    rw [(reads i).1,(reads i).2]
    exact ⟨Nat.le_of_lt_succ (number (a i)).isLt,Nat.le_of_lt_succ (number (b i)).isLt⟩
  have left (i : ActiveRows rows) : D.layer ((rows i.val).leftSite (fits i))=(a i).2 := by
    rw [show (rows i.val).leftSite (fits i)=number (a i) from Fin.ext (reads i).1]
    exact boardLayer ..
  have right (i : ActiveRows rows) : D.layer ((rows i.val).rightSite (fits i))=(b i).2 := by
    rw [show (rows i.val).rightSite (fits i)=number (b i) from Fin.ext (reads i).2]
    exact boardLayer ..
  refine ⟨distinct,fits,fun i=>scaleOf S π depth marked (edge i),
    fun i=>scaleOf_nonneg S π depth marked _,?_,?_⟩
  · intro i
    dsimp only
    intro different
    rw [left,right] at different
    apply (layers S π depth marked M (edge i)).1
    cases hflip : flip i <;> simpa [a,b,hflip,e,ne_comm] using different
  · intro i
    dsimp only
    intro _
    rw [left,right,lengthRead]
    have price := (layers S π depth marked M (edge i)).2
    cases hflip : flip i <;> simpa [a,b,hflip,e,dist_comm] using price

end Hierarchy.ProbeStage.CoreBoard

end
end OAI
