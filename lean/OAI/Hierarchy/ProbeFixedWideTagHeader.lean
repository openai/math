import OAI.Hierarchy.ProbeFixedWidePrivateHeader

namespace OAI
/-! # Independent input tag words for the original charged wide controller -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute CatalystArchive
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

private theorem JointHeader.above_tags {z d N k phases : ℕ} (b : JointHeader.Board)
    (phase : Fin phases→PhasePrice) (π τ : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ)
    (rest : Boot.Tape z d) (x : ℕ) (high : 2^z≤x) :
    JointHeader.words b z d N k phase π stock rest x=JointHeader.words b z d N k phase τ stock rest x := by
  have upper : AdviceLocal (fun m : Boot.Tape z d =>
      GlobalTests.allPages (JointHeader.scores b z N k) z N k phase (JointHeader.lowData b z N k stock m)) :=
    (GlobalTests.all_local _ phase).comp ((AdviceLocal.fill _ _ _).comp
      ((AdviceLocal.fill _ _ _).comp (AdviceLocal.fill _ _ _)))
  exact upper (Boot.permutationWords π rest) (Boot.permutationWords τ rest) x
    (by simp [Boot.permutationWords,Nat.not_lt.mpr high])

namespace FixedProtocolFormat
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies

theorem wide_tags_above (stock : Bank) (M : ℕ) (π τ : Equiv.Perm (Fin (2^h)))
    (o : Orders h D k) (raw : Boot.Tape h D) (x : ℕ) (high : 2^h≤x) :
    v.wideSignedWords h width stock M π o raw x=v.wideSignedWords h width stock M τ o raw x := by
  unfold wideSignedWords chargedMasterWords
  apply JointHeader.above_tags
  exact high

/-- The low rows accept arbitrary binary tag words. The high memory is the
fixed geometry and selector input shared by all choices of the low rows. -/
def wideTagHeader (stock : Bank) (M : ℕ) (o : Orders h D k) (raw : Boot.Tape h D)
    (tags : Fin (2^h)→Word w) : Boot.Tape h D :=
  fun x=>if hx : x<2^h then tags ⟨x,hx⟩ else
    v.wideSignedWords h width stock M (Equiv.refl _) o raw x

theorem wide_tag_header_eq (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
    (o : Orders h D k) (raw : Boot.Tape h D) :
    v.wideTagHeader h width stock M o raw (fun i=>(π i).val)=v.wideSignedWords h width stock M π o raw := by
  funext x
  by_cases hx : x<2^h
  · simp only [wideTagHeader,dite_eq_left hx]
    exact (v.wide_signed_words_authentic h width stock M π o raw ⟨x,hx⟩).symm
  · simp only [wideTagHeader,dite_eq_right hx]
    exact v.wide_tags_above h width stock M _ π o raw x (Nat.le_of_not_lt hx)

end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
