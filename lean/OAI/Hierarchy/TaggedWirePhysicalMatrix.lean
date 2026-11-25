import OAI.Hierarchy.TaggedWireSiteMatrix
import OAI.Hierarchy.ProbeArbitraryPlacement

namespace OAI
/-! # The same signed packet matrix on its actual physical sites -/

noncomputable section
set_option maxHeartbeats 1200000
namespace Hierarchy.WireTelescope.PhysicalMatrix
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Probe
open scoped Classical BigOperators

variable {k S : ℕ} (place : Fin k ↪ Fin S) {F : Type*} [Field F]

private theorem orient (e : Chord k) :
    (physicalChord place e).val=(place e.1.1,place e.1.2) ∨
      (physicalChord place e).val=(place e.1.2,place e.1.1) := by
  unfold physicalChord orderedEnds
  split <;> simp

theorem edge_injective : Function.Injective (physicalChord place) := by
  intro a b h
  have eqn := congrArg Subtype.val h
  rcases orient place a with ax|ax <;> rcases orient place b with bx|bx <;>
    rw [ax,bx] at eqn <;>
    have lo := place.injective (congrArg Prod.fst eqn) <;>
    have hi := place.injective (congrArg Prod.snd eqn)
  · exact Subtype.ext (Prod.ext lo hi)
  · exact False.elim (not_lt_of_ge (by simpa only [lo,hi] using a.property.le) b.property)
  · exact False.elim (not_lt_of_ge (by simpa only [←lo,←hi] using b.property.le) a.property)
  · exact Subtype.ext (Prod.ext hi lo)

@[simp] theorem width_at (U : Widths k) (e : Chord k) :
    placeWidths place U (physicalChord place e)=U e :=
  Finsupp.mapDomain_apply_of_injective (edge_injective place) _ _

theorem width_away (U : Widths k) {a : Chord S} (absent : a ∉ Set.range (physicalChord place)) :
    placeWidths place U a=0 :=
  Finsupp.mapDomain_of_not_mem_image_support (fun ⟨e,_,eq⟩=>absent ⟨e,eq⟩)

def side (e : Chord k) (s : Bool) := if place e.1.1<place e.1.2 then s else !s

theorem incident (e : Chord k) (s : Bool) :
    (portGraph S).vertex (physicalChord place e) (side place e s)=place ((portGraph k).vertex e s) := by
  by_cases h:place e.1.1<place e.1.2 <;> cases s <;>
    simp [physicalChord,orderedEnds,side,h,portGraph,PortGraph.vertex]

def port (i : Fin k) (p : (portGraph k).Port i) : (portGraph S).Port (place i) :=
  ⟨(physicalChord place p.1.1,side place p.1.1 p.1.2),
    (incident place p.1.1 p.1.2).trans (congrArg place p.2)⟩

def read (U : Widths k) (i : Fin k) (x : State (placeWidths place U) (place i)) : State U i :=
  fun p=>finCongr (congrArg (2^·) (width_at place U p.1.1)) (x (port place i p))

def words (U : Widths k) : (∀a,Index (placeWidths place U) a) ≃ (∀e,Index U e) where
  toFun z e := finCongr (congrArg (2^·) (width_at place U e)) (z (physicalChord place e))
  invFun z a := if h : ∃e,physicalChord place e=a then
    Fin.cast (congrArg (2^·) ((width_at place U h.choose).symm.trans (congrArg (placeWidths place U) h.choose_spec))) (z h.choose)
    else 0
  left_inv z := by
    funext a
    by_cases h : ∃e,physicalChord place e=a
    · apply Fin.ext
      simp only [dite_eq_left h,Fin.val_cast,finCongr_apply]
      exact congrArg (fun a=>(z a).val) h.choose_spec
    · have tiny := width_away place U h
      have hz := (z a).isLt
      change (z a).val<2^(placeWidths place U a) at hz
      have bound : (z a).val<1 := hz.trans_le (by rw [tiny,pow_zero])
      apply Fin.ext
      simp only [dite_eq_right h,Fin.val_zero]
      omega
  right_inv z := by
    funext e
    let h : ∃b,physicalChord place b=physicalChord place e := ⟨e,rfl⟩
    have same := edge_injective place h.choose_spec
    apply Fin.ext
    simp only [h,dite_eq_left,Fin.val_cast,finCongr_apply]
    exact congrArg (fun e=>(z e).val) same

@[simp] theorem read_words (U : Widths k) (z : ∀a,Index (placeWidths place U) a) (i : Fin k) :
    read place U i ((portGraph S).atVertex z (place i))=
      (portGraph k).atVertex (words place U z) i := rfl

private theorem half_value {G : PortGraph (Fin S) (Chord S)} {A : Chord S→Type}
    (x : ∀v,G.State A v) (e : Chord S) (b : Bool) (v : Fin S) (h : G.vertex e b=v) :
    x v ⟨(e,b),h⟩=x (G.vertex e b) ⟨(e,b),rfl⟩ := by
  cases h
  rfl

/-- Moving a half-port may exchange the two sorted endpoints. Equality
of its two words is invariant under the exchange. -/
theorem checks_at (U : Widths k) (x : ∀s,State (placeWidths place U) s) (e : Chord k) :
    (read place U e.1.1 (x (place e.1.1)) ⟨(e,false),rfl⟩=
      read place U e.1.2 (x (place e.1.2)) ⟨(e,true),rfl⟩) ↔
    x (physicalChord place e).1.1 ⟨(physicalChord place e,false),rfl⟩=
      x (physicalChord place e).1.2 ⟨(physicalChord place e,true),rfl⟩ := by
  let a := physicalChord place e
  let half (b : Bool) := (x ((portGraph S).vertex a b) ⟨(a,b),rfl⟩).val
  have get (b : Bool) :
      (read place U ((portGraph k).vertex e b) (x (place ((portGraph k).vertex e b))) ⟨(e,b),rfl⟩).val=
        half (side place e b) := by
    exact congrArg Fin.val (half_value x a (side place e b) _ (incident place e b))
  refine Fin.ext_iff.trans (Iff.trans ?_ Fin.ext_iff.symm)
  refine ((congrArg₂ (fun l r : ℕ => l=r) (get false) (get true)).to_iff).trans ?_
  change half (side place e false)=half (side place e true) ↔ half false=half true
  by_cases h:place e.1.1<place e.1.2
  · simp only [side,ite_eq_left h]
  · simp only [side,ite_eq_right h,Bool.not_false,Bool.not_true]
    exact eq_comm

theorem raw_read (U : Widths k) (x : ∀s,State (placeWidths place U) s) :
    (raw F (placeWidths place U)).coeff x=(raw F U).coeff (fun i=>read place U i (x (place i))) := by
  dsimp only [raw,PortGraph.wiring]
  congr 1
  apply propext
  constructor
  · intro all e
    exact (checks_at place U x e).mpr (all _)
  · intro all a
    by_cases h:∃e,physicalChord place e=a
    · obtain ⟨e,rfl⟩ := h
      exact (checks_at place U x e).mp (all e)
    · have tiny := width_away place U h
      have unique : Subsingleton (Index (placeWidths place U) a) := by
        change Subsingleton (Fin (2^(placeWidths place U a)))
        rw [tiny,pow_zero]
        infer_instance
      exact unique.elim _ _

/-- A global party contributes the product of the given local entries at
its own site. Empty fibers contribute 1 and no hidden site table. -/
def matrix {U V : Widths k} (M : SiteMatrix (State U) (State V) F) :
    SiteMatrix (State (placeWidths place U)) (State (placeWidths place V)) F :=
  fun s x y=>∏i : {i // place i=s},
    M i.1 (read place U i.1 (i.2.symm ▸ x)) (read place V i.1 (i.2.symm ▸ y))

private theorem sum_all {A : Type*} (left right : Fintype A) (f : A→F) :
    (@Finset.univ A left).sum f=(@Finset.univ A right).sum f := by
  cases Subsingleton.elim left right
  rfl

private theorem sum_each {A : Type*} (left right : Fintype A) (f g : A→F) (point : ∀a,f a=g a) :
    (@Finset.univ A left).sum f=(@Finset.univ A right).sum g := by
  rw [funext point]
  exact sum_all left right g

theorem action {U V : Widths k} (M : SiteMatrix (State U) (State V) F)
    (x : ∀s,State (placeWidths place U) s) :
    SiteMatrix.act (matrix place M) (raw F (placeWidths place V)).coeff x=
      SiteMatrix.act M (raw F V).coeff (fun i=>read place U i (x (place i))) := by
  let f := fun z : ∀e,Index V e=>∏i,M i (read place U i (x (place i))) ((portGraph k).atVertex z i)
  have rhs := (portGraph k).contraction_eq_wiring (Index V)
    (fun i y=>M i (read place U i (x (place i))) y)
  have lhs := (portGraph S).contraction_eq_wiring (Index (placeWidths place V)) (fun s y=>matrix place M s (x s) y)
  have contraction : (portGraph S).contraction (fun s y=>matrix place M s (x s) y) =
      (portGraph k).contraction (fun i y=>M i (read place U i (x (place i))) y) := by
    unfold PortGraph.contraction
    refine (sum_each _ _ _ (fun z=>f (words place V z)) ?_).trans
      (((words place V).sum_comp f).trans (sum_all _ _ f))
    intro z
    change (∏s,∏i : {i // place i=s},_) = ∏j,M j (read place U j (x (place j))) ((portGraph k).atVertex (words place V z) j)
    rw [←Fintype.prod_fiberwise place (fun i=>M i (read place U i (x (place i))) ((portGraph k).atVertex (words place V z) i))]
    apply Finset.prod_congr rfl
    intro s _
    apply Finset.prod_congr rfl
    rintro ⟨i,rfl⟩ _
    rfl
  exact (sum_all _ _ _).trans (lhs.symm.trans (contraction.trans (rhs.trans (sum_all _ _ _))))

theorem place_sum {J : Type*} [Fintype J] {U : Widths k} {V : J→Widths k}
    (M : ∀j,SiteMatrix (State U) (State (V j)) F)
    (tileLaw : ∀z,(raw F U).coeff z=∑j,SiteMatrix.act (M j) (raw F (V j)).coeff z)
    (x : ∀s,State (placeWidths place U) s) :
    (raw F (placeWidths place U)).coeff x=
      ∑j,SiteMatrix.act (matrix place (M j)) (raw F (placeWidths place (V j))).coeff x := by
  simp only [action,raw_read]
  exact tileLaw _

end Hierarchy.WireTelescope.PhysicalMatrix

end
end OAI
