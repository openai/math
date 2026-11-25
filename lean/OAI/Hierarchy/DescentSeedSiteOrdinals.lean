import OAI.Hierarchy.DescentSeedSiteIndex
import OAI.Hierarchy.DescentInitialPackage

namespace OAI
/-! Finite order and trivalent incidence bounds on the immutable augmented input graph. -/
namespace Hierarchy.DescentPackedSeed.Signed
open DescentSeedRoot DescentInitialHost Computability.BorderVNP.Crossing Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {k n : ℕ} (X : Approximation F k n)
local notation "N" => X.network.copyGraph

def present (v : Vertex X) (e : Cable X) := source N e=v ∨ target N e=v

/-- A loop uses one cable name; the attached open port has its own cable name. -/
theorem incident_bound (v : Vertex X) : (Finset.univ.filter (present X v)).card≤3 := by
  classical
  rcases v with u|p
  · let deck:=Finset.univ.filter (present X (.inl u))
    let sockets:=Finset.univ.filter (fun z : OldPort N=>owner N z=u)
    let port : Wire N → OldPort N := Sum.elim (fun e=>.inr (e,decide ((N).src e≠u))) Sum.inl
    let erase : OldPort N → Wire N := Sum.elim Sum.inr (fun eb=>Sum.inl eb.1)
    have ownerAt (e : Cable X) (valid : present X (.inl u) e) : owner N (port e)=u := by
      rcases e with e|q
      · have here : (N).src e=u ∨ (N).dst e=u := by simpa [present,source,target] using valid
        by_cases src : (N).src e=u
        · simp [port,owner,src]
        · simpa [port,owner,src] using here.resolve_left src
      · simpa [port,present,source,target,owner] using valid
    have undo (e : Wire N) : erase (port e)=e := by cases e <;> rfl
    let map (a : ↥deck) : ↥sockets :=
      ⟨port a.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ownerAt a.val (Finset.mem_filter.mp a.property).2⟩⟩
    have inject : Function.Injective map := fun a b h=>Subtype.ext <|
      (undo a.val).symm.trans ((congrArg (fun z : ↥sockets=>erase z.val) h).trans (undo b.val))
    have bound:=Fintype.card_le_of_injective map inject
    rw [Fintype.card_coe,Fintype.card_coe] at bound
    exact bound.trans ((CorrectionBatch.physical_output X).1.2 u)
  · have sole {e : Cable X} (h : present X (.inr p) e) : e=.inr p := by
      rcases e with e|q
      · simp [present,source,target] at h
      · exact congrArg Sum.inr (by simpa [present,source,target] using h)
    have one : (Finset.univ.filter (present X (.inr p))).card≤1 :=
      Finset.card_le_one.mpr (fun _ he _ hf=>(sole (Finset.mem_filter.mp he).2).trans (sole (Finset.mem_filter.mp hf).2).symm)
    exact one.trans (by decide)

def other (v : Vertex X) (e : Cable X) := if source N e=v then target N e else source N e

def seedPeer (v : Vertex X) (e : Cable X) :=
  ((near N v).filter (fun u=>index u< index (other X v e))).card

def earlier (v t : Vertex X) (e : Cable X) := Finset.univ.filter fun f : Cable X=>
  ((source N f=v ∧ target N f=t) ∨ (target N f=v ∧ source N f=t)) ∧ index f< index e

def seedParallel (v : Vertex X) (e : Cable X) := (earlier X v (other X v e) e).card

def seedPort {v : Vertex X} (p : {t : Fin (Fintype.card (Port n X.width)) // Sum.inr t=v}) := p.val.val

theorem peer_room (v : Vertex X) (e : Cable X) : seedPeer X v e≤3 :=
  (Finset.card_le_card (Finset.filter_subset ..)).trans ((«initialize» X).1 v)

def localPort {v : Vertex X} (_ : {t : Fin (Fintype.card (Port n X.width)) // Sum.inr t=v}) : Fin 1 := 0

omit [Field F] in
theorem external_unique (v : Vertex X) (a b : {t : Fin (Fintype.card (Port n X.width)) // Sum.inr t=v}) : a=b :=
  Subtype.ext (Sum.inr.inj (a.property.trans b.property.symm))

theorem parallel_short (v : Vertex X) (e : Cable X) : seedParallel X v e≤3 := by
  apply (Finset.card_le_card _).trans (incident_bound X v)
  intro f hf
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp hf).2.1).imp And.left And.left⟩

def earlierAt (v : Vertex X) (e : Cable X) :=
  Finset.univ.filter (fun f : Cable X=>present X v f ∧ index f< index e)

def position (v : Vertex X) (e : Cable X) := (earlierAt X v e).card

theorem position_short (v : Vertex X) (e : Cable X) (here : present X v e) : position X v e<3 := by
  let deck:=Finset.univ.filter (present X v)
  have subset : earlierAt X v e⊆deck := by
    intro f hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hf).2.1⟩
  have strict : earlierAt X v e⊂deck := (Finset.ssubset_iff_of_subset subset).2
    ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,here⟩,by simp [earlierAt]⟩
  exact (Finset.card_lt_card strict).trans_le (incident_bound X v)

omit [Field F] in
theorem position_lt (v : Vertex X) {e f : Cable X} (here : present X v e) (lt : index e< index f) :
    position X v e<position X v f := by
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (show earlierAt X v e⊆earlierAt X v f from fun z hz=>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2.1,((Finset.mem_filter.mp hz).2.2).trans lt⟩)).2
  exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,here,lt⟩,by simp [earlierAt]⟩

omit [Field F] in
theorem position_unique (v : Vertex X) (e f : Cable X) (ep : present X v e) (fp : present X v f)
    (same : position X v e=position X v f) : e=f := by
  rcases lt_trichotomy (index e) (index f) with lt|eq|lt
  · exact False.elim ((position_lt X v ep lt).ne same)
  · exact (Fintype.equivFin _).injective (Fin.ext eq)
  · exact False.elim ((position_lt X v fp lt).ne same.symm)

end
end Hierarchy.DescentPackedSeed.Signed

end OAI
