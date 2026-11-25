import OAI.Hierarchy.DescentSortedRoster

namespace OAI
/-! # Sorting the measured four neighbors commutes with compacting occupied hosts -/
namespace Hierarchy.DescentSortedRoster.Compact
noncomputable section
open scoped Classical
variable {P H N D : ℕ} (names : Fin N ↪ Fin P) (size : N≤H)
  (raw : Fin P→Fin D→Option (Fin P))

def restore (y : Fin P) : Option (Fin H) :=
  if h : ∃v,names v=y then some (h.choose.castLE size) else none

theorem restore_name (v : Fin N) : restore names size (names v)=some (v.castLE size):=by
  have hit : ∃a,names a=names v:=⟨v,rfl⟩
  rw [restore,dite_eq_left hit,names.injective hit.choose_spec]

private theorem restore_eq {y : Fin P} {x : Fin H} :
    restore names size y=some x ↔ ∃v,names v=y ∧ v.castLE size=x:=by
  constructor
  · unfold restore
    split
    next h=>exact fun eq=>⟨h.choose,h.choose_spec,Option.some.inj eq⟩
    next=>simp
  · rintro ⟨v,rfl,rfl⟩
    exact restore_name names size v

def pull (x : Fin H) (j : Fin D) : Option (Fin H):=
  if h : x.val<N then (raw (names ⟨x,h⟩) j).bind (restore names size) else none

theorem pull_live (v : Fin N) (j : Fin D) :
    pull names size raw (v.castLE size) j=(raw (names v) j).bind (restore names size):=
  dite_eq_left v.isLt

theorem pull_missing {x : Fin H} (h : N≤x.val) (j : Fin D) : pull names size raw x j=none:=
  dite_eq_right (Nat.not_lt.mpr h)

theorem current_set (v : Fin N) :
    present (pull names size raw) (v.castLE size)=
      (Finset.univ.filter (fun a : Fin N=>names a∈present raw (names v))).map (Fin.castLEEmb size):=by
  classical
  ext x
  simp only [present,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
  constructor
  · rintro ⟨j,hit⟩
    rw [pull_live] at hit
    obtain ⟨y,tag,same⟩:=Option.bind_eq_some_iff.mp hit
    obtain ⟨z,rfl,rfl⟩:=(restore_eq names size).mp same
    exact ⟨z,⟨j,tag⟩,rfl⟩
  · rintro ⟨z,⟨j,tag⟩,rfl⟩
    exact ⟨j,by rw [pull_live,tag];exact restore_name names size z⟩

theorem ordered_set (v : Fin N) (closed : ∀y∈present raw (names v),∃z,names z=y) :
    present raw (names v)=
      (Finset.univ.filter (fun a : Fin N=>names a∈present raw (names v))).map names:=by
  classical
  ext y
  simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun hy=>by obtain ⟨z,rfl⟩:=closed y hy;exact ⟨z,hy,rfl⟩,by rintro ⟨z,hz,rfl⟩;exact hz⟩

theorem same_before (v u : Fin N) (inc : StrictMono names)
    (closed : ∀y∈present raw (names v),∃z,names z=y) :
    before (pull names size raw) (v.castLE size) (u.castLE size)=before raw (names v) (names u):=by
  classical
  unfold before
  conv_rhs => rw [ordered_set names raw v closed]
  rw [current_set]
  simp only [Finset.filter_map,Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro i hi
  exact inc.lt_iff_lt.symm

theorem indexed_live (v : Fin N) (j : Fin D) (inc : StrictMono names)
    (closed : ∀y∈present raw (names v),∃z,names z=y) :
    indexed (pull names size raw) (v.castLE size) j=
      (indexed raw (names v) j).bind (restore names size):=by
  classical
  apply Option.ext
  intro x
  rw [indexed_iff,Option.bind_eq_some_iff]
  constructor
  · rintro ⟨mem,score⟩
    rw [current_set,Finset.mem_map] at mem
    obtain ⟨z,member,rfl⟩:=mem
    exact ⟨names z,(indexed_iff ..).mpr ⟨(Finset.mem_filter.mp member).2,
       (same_before names size raw v z inc closed).symm.trans score⟩,restore_name names size z⟩
  · rintro ⟨y,byIndex,atX⟩
    obtain ⟨z,rfl,rfl⟩:=(restore_eq names size).mp atX
    obtain ⟨mem,score⟩:=(indexed_iff ..).mp byIndex
    exact ⟨by rw [current_set,Finset.mem_map];exact ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,mem⟩,rfl⟩,
      (same_before names size raw v z inc closed).trans score⟩

theorem indexed_missing {x : Fin H} (h : N≤x.val) (j : Fin D) :
    indexed (pull names size raw) x j=none:=by
  classical
  cases eq:indexed (pull names size raw) x j with
  | none=>rfl
  | some y=>
    obtain ⟨mem,_⟩:=(indexed_iff ..).mp eq
    obtain ⟨j,atJ⟩:=(Finset.mem_filter.mp mem).2
    rw [pull_missing names size raw h] at atJ
    contradiction

end
end Hierarchy.DescentSortedRoster.Compact

end OAI
