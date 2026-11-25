import OAI.ThreeFlat.RAM.TraceSuffixFit

namespace OAI
/-! # One physical input aperture suffices for every scalar public-header query -/

namespace ThreeFlat.RAM.TraceSuffixOracle
variable {W : ℕ} {s : Layout}

/-- The absolute endpoint for a mounted suffix, including eager arithmetic on wrong-branch
values. Every pointer in a single scalar lookup lies strictly below this endpoint. -/
def suffixExtent (s : Layout) (S : ℕ) :=
  max 12 (max (s.hWidth+1) (max (s.paired+1) (max (s.rawParams+1)
    (max (s.rawTable+1) (max (s.rawCount+1) (max (s.codeBase+s.textSize+1)
      (max (s.description+s.textOffset+S) (max (s.parameters+S) (s.table+S)))))))))

/-- An ordinary physical layout bound on each segment and the requested header length
is sufficient for the compound eager-address calculations. -/
theorem extent_le {s : Layout} {S cap : ℕ} (small : 12≤cap) (size : S≤cap)
    (width : s.hWidth<cap) (paired : s.paired<cap) (par : s.rawParams<cap)
    (tab : s.rawTable<cap) (raw : s.rawCount<cap) (code : s.codeBase+s.textSize<cap)
    (description : s.description+s.textOffset≤cap) (parameters : s.parameters≤cap)
    (table : s.table≤cap) : suffixExtent s S≤2*cap := by
  simp only [suffixExtent,max_le_iff]
  omega

theorem bounds_of_extent {S t : ℕ} (ht : t<S) (space : suffixExtent s S≤2^W) :
    Bounds W s t := by
  simp only [suffixExtent,max_le_iff] at space
  constructor <;> omega


end ThreeFlat.RAM.TraceSuffixOracle

end OAI
