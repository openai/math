import OAI.Computability.VPVNP.CompressorSourceWalk
import OAI.Computability.VPVNP.CompressorRefreshStageFrame

/-!
# Joining chronological source evidence

Fixed stage lengths identify the same report boundaries in two walks. This lets
a physical source execution carry independently verified cursor and memory facts.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords
open BurstRAM
open scoped Fin.CommRing

/-- Two proofs about the same chronological sequence can be joined once their
per-stage report counts agree. Empty stages and nonzero entry cursors are allowed. -/
theorem SourceWalk.zip {w : ℕ} {J : Type*} {p q : J → Memory w → List (Report w) → Prop}
    {js : List J} {m : Memory w} {rs ts : List (Report w)} (one : SourceWalk p js m rs)
    (two : SourceWalk q js m ts) (same : rs=ts)
    (lengths : ∀ j m xs ys, p j m xs → q j m ys → xs.length = ys.length) :
    SourceWalk (fun j m xs ↦ p j m xs ∧ q j m xs) js m rs := by
  induction one generalizing ts with
  | done => exact .done _
  | next head _ ih =>
    cases two with
    | next other tail =>
      obtain ⟨rfl,rfl⟩ := List.append_inj same (lengths _ _ _ _ head other)
      exact .next ⟨head,other⟩ (ih tail rfl)

theorem StageFrame.Scanned.length {w j N : ℕ} {rs : List (Report w)} (s : Scanned j N rs) :
    rs.length = N-j := by
  induction s with
  | done => simp
  | next live _ _ ih => rw [List.length_cons,ih]; omega

/-- Successful calls in an arbitrary tape advance the concrete ordinal by one. -/
theorem StageFrame.scanned_tapes {w : ℕ} {Q : Type*} (P : BurstRAM.Program w Q) (fuel N : ℕ)
    (inc : ∀ j < N, ∀ mem bs rep, execute P fuel (P.start (j : Word w)) mem bs = some rep →
      rep.result = some ((j+1 : ℕ) : Word w)) (j : ℕ) (m : Memory w) (bs : List (List Bool))
    (rs : List (Report w)) (size : j+bs.length = N)
    (run : runSegment P fuel (some (j : Word w)) m bs = some rs) : Scanned j N rs := by
  induction bs generalizing j m rs with
  | nil =>
    have e : j=N := by simpa using size
    change some []=some rs at run
    cases Option.some.inj run
    exact e ▸ .done _
  | cons b bs ih =>
    have live : j<N := by simp only [List.length_cons] at size; omega
    cases h : execute P fuel (P.start (j : Word w)) m b with
    | none => simp [runSegment,h] at run
    | some rep =>
      have ret := inc j live m b rep h
      rw [runSegment,h] at run
      simp only [ret,Option.map_eq_some_iff] at run
      obtain ⟨tail,ht,rfl⟩ := run
      exact .next live ret (ih (j+1) _ _ (by simp only [List.length_cons] at size; omega) ht)

end CompressorRecords

end VPVNP
end Computability
end OAI
