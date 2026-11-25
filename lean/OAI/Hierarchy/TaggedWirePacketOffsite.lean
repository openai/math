import OAI.Hierarchy.TaggedWireShortWalkWords
import OAI.Hierarchy.TaggedWireRoutedPackets
import OAI.Hierarchy.TaggedWireStripPaths

namespace OAI
/-! # Outside its physical ball a routed packet accepts every pair of states -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Tagged AdaptiveProbe Probe
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical

namespace ShortWalk
variable {S n m : ℕ} {old : Fin n→Chord S} {edge : Fin m→Chord S}
  {route : Fin n→List (Fin m)} {bits : Fin n→ℕ}

theorem away {s a b : Fin S} (xs : List (Fin m)) (j : ℕ)
    (lo : a≠s) (hi : b≠s) (outside : ∀e∈xs,(edge e).1.1≠s ∧ (edge e).1.2≠s) :
    site (rowGraph edge) a b xs j ≠ s := by
  unfold site
  split
  · exact lo
  split
  · exact hi
  split
  next has=>
    have both:=outside (xs[0]'has) (List.getElem_mem has)
    dsimp only
    split
    · exact both.2
    · exact both.1
  · exact lo

theorem matrix_away {h : ℕ} (F : Type) [Field F] (rank : Fin h≃Σi,Fin (route i).length)
    (walk : ∀i,Traverses (rowGraph edge) (old i).1.1 (route i) (old i).1.2)
    (short : ∀i,(route i).length≤2) (s : Fin S)
    (outside : ∀i,0<bits i→(old i).1.1≠s ∧ (old i).1.2≠s ∧
      ∀e∈route i,(edge e).1.1≠s ∧ (edge e).1.2≠s)
    (a : State (installedWidths old bits) s) (b : State (installedWidths edge (routeLoad route bits)) s) :
    chordRouter old edge route bits rank walk s a b=(1:F) := by
  unfold chordRouter chordRouterWith bitMatrix
  apply ite_eq_left
  apply (word_turns_iff (rowGraph edge) (rowGraph old) route bits
    (NativeSlot.allocation route bits rank) (NativeSlot.allocation_edge route bits rank)
    walk (fun j=>(edge j).property.ne) s (rowBits old bits a) (rowBits edge _ b)).mpr
  intro i pair occ j
  let sp:=(Spine.exists_of_walk (walk i)).some
  have law := sp.in_wordTurns (.inl false) (.inl true) 0 s pair
  rw [sp.itinerary_eq (fun e=>(edge e).property.ne)] at law
  obtain ⟨pos,atSite,_⟩:=law.mp occ
  have clear:=outside i (Nat.zero_lt_of_lt j.isLt)
  exact False.elim (away (route i) pos.val clear.1 clear.2.1 clear.2.2 ((site_eq _ sp (short i) pos).trans atSite))
end ShortWalk

namespace ChosenPackets.RowRouting
variable {S H N copies : ℕ} {F : Type} [Field F] {row : Row F S H copies} {phys : Fin N→Chord S}
    (R : RowRouting row phys) (c : Histogram (Fin H) copies) (s : Fin S)

private theorem transport_one {U U' V V' : Widths S} (hu : U=U') (hv : V=V')
    (M : SiteMatrix (State U) (State V) F) (one : ∀a b,M s a b=1) :
    ∀a b,Installs.transport hu hv M s a b=1 := by subst U';subst V';exact one

theorem install_off_site (short : ∀r,(R.install.route r).length≤2)
    (away : ∀r,0<R.bits c r→(R.source r).1.1≠s ∧ (R.source r).1.2≠s ∧
      ∀e∈R.install.route r,(phys e).1.1≠s ∧ (phys e).1.2≠s) :
    ∀a b,Installs.transport (R.shape c) rfl (R.install.operator (F:=F) R.order (R.bits c) R.ordinal) s a b=1 := by
  apply transport_one
  unfold Installs.operator
  apply transport_one
  exact ShortWalk.matrix_away F R.ordinal (fun i=>R.install.path (R.order i))
    (fun i=>short (R.order i)) s (fun i=>away (R.order i))

end ChosenPackets.RowRouting

namespace StripPaths
open AdaptiveProbe.Strip
variable {K N k : ℕ} {C H E Ball : Type} (edge : Fin N→Chord K) (horizontal : H→DistinctPair C)
    (extra : E→DistinctPair (ColumnSite C k)) (place : Ball×ColumnSite C k↪Fin K) (u : Ball)
local notation "R" => ColumnWires.Role C H E k

theorem reported_away {X I : Type} {ball : Ball} (put : Ball×X↪Fin K) (ends : I→DistinctPair X)
    (r : I) (s : Fin K) (away : ∀x,put (ball,x)≠s) :
    (reportedRole put ends ball r).1.1≠s ∧ (reportedRole put ends ball r).1.2≠s := by
  unfold reportedRole orderedEnds
  split <;> exact ⟨away _,away _⟩

theorem links_away (primary : R→Fin N) (mate : C→Fin k→Fin N)
    (first : ∀r,edge (primary r)=reportedRole place (ColumnWires.ends horizontal extra) u (firstRole r))
    (second : ∀c j,edge (mate c j)=reportedRole place (ColumnWires.ends horizontal extra) u (.radius c j true))
    (s : Fin K) (away : ∀x,place (u,x)≠s) (r : R) :
    ∀e∈links horizontal extra place u primary mate r,(edge e).1.1≠s ∧ (edge e).1.2≠s := by
  have single (r : R) : (edge (primary r)).1.1≠s ∧ (edge (primary r)).1.2≠s := by
    rw [first];exact reported_away place _ _ s away
  have other (c : C) (j : Fin k) : (edge (mate c j)).1.1≠s ∧ (edge (mate c j)).1.2≠s := by
    rw [second];exact reported_away place _ _ s away
  intro e mem
  have seen : e∈forward primary mate r := by dsimp only [links] at mem;split at mem <;> simpa using mem
  cases r <;> simp only [forward,List.mem_cons,List.not_mem_nil,or_false] at seen
  all_goals first | (subst e;exact single _) | (rcases seen with rfl|rfl;exact single _;exact other _ _)

end StripPaths
end Hierarchy.WireTelescope

end
end OAI
