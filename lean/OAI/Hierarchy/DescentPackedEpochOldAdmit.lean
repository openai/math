import OAI.Hierarchy.DescentPackedEpochExact

namespace OAI
/-! # A single pre-exterior physical flag for a reached packed epoch transcript -/
namespace Hierarchy.DescentPackedEpochShelves
open DescentTerminalEpochChart DescentPackedProfileTape DescentPackedProfileInstall DescentPackedEpochFold
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {A : Type} {w : ℕ}

def oldState (lo C r seed : ℕ) (ss : List (Source A)) (count : ℕ→ℕ) (z : A→ Bool) (m : Memory w) :=
  finalImage z (final lo C r ss) seed (controls lo C r ss count (fun _=>seed)) m

/-- Each stage's optional exterior input reuses the already measured original
seed bit. The accumulated flag therefore tests only the seed and the epoch
profiles. The separate physical exterior transpose verifier can follow it. -/
theorem oldAdmit {S Z U : Type} {bits : Z→ S→ Bool} {ok : (S→ Bool)→ Prop} {fd : U→ Z}
    (b : Chart bits ok fd) (z : b.Pin→ Bool) (old m : Memory w) (lo C r seed : ℕ) (count : ℕ→ℕ)
    (same : DescentTerminalEpochDecoder.Uniform C b.layout) (pos : 0 < r) (seedLow : seed < lo)
    (lower : ∀p∈shelves r lo 0 b.layout,count p.ordinal < lo)
    (wide : ∀s∈b.layout,slots s.seats r*r < 2^w) (space : final lo C r b.layout+1 < 2^w)
    (held : ∀a,lo ≤ a→ a < end_ (lo+extent r b.layout) C r→ m a=header lo C r b.layout z old a)
    (seeded : m seed=0 ↔ ok (z∘b.seed))
    (counts : List.IsPrefix ((b.rows z).map Observation.count)
      ((controls lo C r b.layout count (fun _=>seed)).map fun s=>(m s.banks.count.base).val)) :
    let ss:=controls lo C r b.layout count (fun _=>seed)
    let dst:=final lo C r b.layout
    let o:=oldState lo C r seed b.layout count z m
    (fold w seed dst ss).Exec m o (bill seed dst ss) ∧ CheapCode (fold w seed dst ss) ∧
    (o dst=0 ↔ ∃c,b.read z=some c) ∧ ∀a < end_ (lo+extent r b.layout) C r,o a=m a := by
  let ext : ℕ→ℕ:=fun _=>seed
  let ss:=controls lo C r b.layout count ext
  let dst:=final lo C r b.layout
  let base:=end_ (lo+extent r b.layout) C r
  obtain ⟨safe,pr,data_,domain⟩:=data_after b z old m lo C r seed count ext same pos seedLow
    (fun q h=>⟨lower q h,seedLow⟩) wide space held
  have exact_:=exact_run base seed dst ss z m safe pr data_
  have test:=survives b z m ss seed seeded domain counts
  have ports (s : Stage b.Pin) (hs : s∈ss) : s.exterior=seed := by
    obtain ⟨p,hp,src,bs,g,ex,_⟩:=phase_mem (lo+extent r b.layout) C r count ext base
      (shelves r lo 0 b.layout) s hs
    exact ex
  have neq:=one_ne (w:=w) (by omega)
  refine ⟨exact_.1,(run base seed dst ss z m safe pr data_).2,?_,exact_.2.2⟩
  change finalImage z dst seed ss m dst=0 ↔ _
  rw [exact_.2.1]
  constructor
  · intro zero
    by_contra no
    have dead : ¬(m seed=0 ∧ ∀s∈ss,m s.exterior=0 ∧ (view s m z).Valid) := fun h=>no (test.mp h).1
    exact neq (by simpa only [ite_eq_right dead] using zero)
  · intro chosen
    have live:=seeded.mpr ((b.accepted z).mp chosen).1
    exact ite_eq_left (test.mpr ⟨chosen,fun s h=>(congrArg m (ports s h)).trans live⟩)

theorem oldState_frame {S Z U : Type} {bits : Z→ S→ Bool} {ok : (S→ Bool)→ Prop} {fd : U→ Z}
    (b : Chart bits ok fd) (z : b.Pin→ Bool) (old m : Memory w) (lo C r seed : ℕ) (count : ℕ→ℕ)
    (same : DescentTerminalEpochDecoder.Uniform C b.layout) (pos : 0 < r) (seedLow : seed < lo)
    (lower : ∀p∈shelves r lo 0 b.layout,count p.ordinal < lo)
    (wide : ∀s∈b.layout,slots s.seats r*r < 2^w) (space : final lo C r b.layout+1 < 2^w)
    (held : ∀a,lo ≤ a→ a < end_ (lo+extent r b.layout) C r→ m a=header lo C r b.layout z old a)
    (a : ℕ) (away : a < end_ (lo+extent r b.layout) C r ∨ final lo C r b.layout < a) :
    oldState lo C r seed b.layout count z m a=m a := by
  obtain ⟨safe,paid,data_,_⟩:=data_after b z old m lo C r seed count (fun _=>seed) same pos seedLow
    (fun q h=>⟨lower q h,seedLow⟩) wide space held
  rcases away with low|high
  · exact (exact_run _ _ _ _ z m safe paid data_).2.2 a low
  · exact high_frame z m safe paid high

end
end Hierarchy.DescentPackedEpochShelves

end OAI
