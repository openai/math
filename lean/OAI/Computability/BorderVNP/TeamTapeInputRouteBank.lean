import OAI.Computability.BorderVNP.TeamTapeInputRouteSize

/-! # Identification of the extracted bit fields with the physical sorting bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputRoute

open VPVNP BurstRAM RAMTape RAMLayout RAMBoundary TeamTapeSorting
open RAMTape.Boundary (recordBytes blockBytes)

variable {d e w : ℕ}

/-- Only the parser's retained incident source and the three specified post-pass ports
can change. This also frames the complete ordinary RAM and private-call verification. -/
theorem routed_other (lane : Bool) (a : Fields d e w) (v : Word d) (rest : List Bool) (s : Stacks Port)
    (k : Port) (hi : k ≠ source) (hp : k ≠ .post lane SitePost.previousPort)
    (hs : k ≠ .post lane SitePost.sentPort) (hc : k ≠ .post lane SitePost.incidentPort) :
    routed lane a v rest s k = s k := by simp [routed,putField,Field.sink,hi,hp,hs,hc]

/-- A complete sorting bank with its three routed fields initially vacant becomes the
bank of the original post-pass, bit for bit. -/
theorem routed_post_bank (lane : Bool) (a : Fields d e w) (v : Word d) (rest : List Bool)
    (s : Stacks Port) (slots : ℕ) (addr block flags : List Bool)
    (hbank : s ∘ Port.post lane = SitePost.rawBank d w slots addr block [] flags [] []) :
    routed lane a v rest s ∘ Port.post lane = SitePost.rawBank d w slots addr block
      (comparisonBits a v) flags (recordBytes (incoming a v)) (recordBytes (outgoing a v)) := by
  have he (i : SitePost.Port) : s (.post lane i) = SitePost.rawBank d w slots addr block [] flags [] [] i :=
    congrFun hbank i
  obtain ⟨hprev,hsent,hcmp⟩ := routed_fields lane a v rest s
  funext i
  by_cases hp : i = SitePost.previousPort
  · subst i; rw [he, show SitePost.rawBank d w slots addr block [] flags [] [] SitePost.previousPort = [] from rfl, List.append_nil] at hprev; exact hprev
  by_cases ho : i = SitePost.sentPort
  · subst i; rw [he, show SitePost.rawBank d w slots addr block [] flags [] [] SitePost.sentPort = [] from rfl, List.append_nil] at hsent; exact hsent
  by_cases hc : i = SitePost.incidentPort
  · subst i; rw [he, show SitePost.rawBank d w slots addr block [] flags [] [] SitePost.incidentPort = [] from rfl, List.append_nil] at hcmp; exact hcmp
  rw [Function.comp_apply, routed_other _ _ _ _ _ _ (by simp) (by simpa) (by simpa) (by simpa), he]
  rcases i with (c | (((r|z)|o)|u)) | extra
  · cases c <;> rfl
  · cases r <;> first | rfl | exact (hc rfl).elim
  · cases z <;> rfl
  · cases o <;> rfl
  · cases u; rfl
  · cases extra <;> first | rfl | exact (hp rfl).elim | exact (ho rfl).elim

/-- After routing, the concrete post-pass bank is precisely the typed prestate used in
the correctness theorem of the sort and boundary checker. -/
theorem routed_prestate {h : ℕ} (lane : Bool) (a : Fields d e w) (v : Word d) (rest : List Bool)
    (s : Stacks Port) (x : SortReplay.State h w)
    (hb : s ∘ Port.post lane = SitePost.rawBank d w (2^h) (wordBits v)
      (blockBytes (List.ofFn x.1)) [] x.2 [] []) :
    routed lane a v rest s ∘ Port.post lane = SitePost.prestate v (incoming a v)
      (outgoing a v) x (comparisonBits a v) := by
  rw [SitePost.prestate_eq_raw]
  exact routed_post_bank lane a v rest s _ _ _ _ hb

end TeamTapeInputRoute

end BorderVNP
end Computability
end OAI
