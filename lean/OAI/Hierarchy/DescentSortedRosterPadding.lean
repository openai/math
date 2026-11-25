import OAI.Hierarchy.DescentSortedRoster

namespace OAI
/-! Padding a physical host prefix preserves the stable unique ordering of its actual neighbors. -/
namespace Hierarchy.DescentSortedRoster
noncomputable section

theorem indexed_pad {H H' paths : ℕ} (wide : H ≤ H')
    (small : Fin H → Fin paths → Option (Fin H)) (large : Fin H' → Fin paths → Option (Fin H'))
    (v : Fin H) (same : ∀ s, large ((Fin.castLEEmb wide) v) s = (small v s).map (Fin.castLEEmb wide))
    (s : Fin paths) :
    indexed large ((Fin.castLEEmb wide) v) s = (indexed small v s).map (Fin.castLEEmb wide) := by
  classical
  let up := Fin.castLEEmb wide
  have actual : present large (up v) = (present small v).map up := by
    ext z
    simp only [present,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨j,hj⟩
      rw [same j] at hj
      cases hit : small v j with
      | none => simp [hit] at hj
      | some t =>
        have eqn : up t = z := by simpa [hit,up] using hj
        exact ⟨t,⟨j,hit⟩,eqn⟩
    · rintro ⟨t,⟨j,hit⟩,rfl⟩
      exact ⟨j,by rw [same j,hit]; rfl⟩
  have order (t : Fin H) : before large (up v) (up t) = before small v t := by
    unfold before
    rw [actual]
    have map_ : (((present small v).map up).filter (· < up t)) =
        ((present small v).filter (· < t)).map up := by
      ext z
      simp only [Finset.mem_filter,Finset.mem_map]
      constructor
      · rintro ⟨⟨a,ha,rfl⟩,lt⟩
        exact ⟨a,⟨ha,lt⟩,rfl⟩
      · rintro ⟨a,⟨ha,lt⟩,rfl⟩
        exact ⟨⟨a,ha,rfl⟩,lt⟩
    rw [map_,Finset.card_map]
  cases smallAt : indexed small v s with
  | some t =>
    obtain ⟨mem,rank⟩ := (indexed_iff small v s t).mp smallAt
    apply (indexed_iff large (up v) s (up t)).mpr
    exact ⟨actual.symm ▸ Finset.mem_map.mpr ⟨t,mem,rfl⟩,(order t).trans rank⟩
  | none =>
    cases largeAt : indexed large (up v) s with
    | none => rfl
    | some z =>
      obtain ⟨mem,rank⟩ := (indexed_iff large (up v) s z).mp largeAt
      rw [actual] at mem
      obtain ⟨t,ht,rfl⟩ := Finset.mem_map.mp mem
      have found := (indexed_iff small v s t).mpr ⟨ht,(order t).symm.trans rank⟩
      simp [smallAt] at found

end
end Hierarchy.DescentSortedRoster

end OAI
