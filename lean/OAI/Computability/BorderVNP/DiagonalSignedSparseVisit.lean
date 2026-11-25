import OAI.Computability.BorderVNP.DiagonalSignedLaunchedCells
import OAI.Computability.BorderVNP.FragmentDirectoryReturn

/-! # The sparse patch on the real signed argument history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM FragmentRows SignedTaskArena CellPacket

variable {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (a : SignedTaskArena.Layout)
local notation "head" => readings pub 0
local notation "f" => FragmentRows.Layout.fromFrame (readings pub 0) (readings m)

/-- Split a genuine returning argument trace once. The emitter and the patch
obtained from its first two returns name exactly the live memory of its last
three native producers, for all original and supplemental cell descriptors. -/
theorem signed_argument_patch {ctl u v k team offsets live ports : ℕ} (x : Returns SignedPrep.arguments pub mac s m)
    (fit : (f).Fits w (readings m)) (pointer : readings m (head+92)=ctl)
    (words : ∀ i : Fin 37, readings m (ctl+i.val)=a.controls i.val)
    (before : head+112 ≤ ctl) (start : ctl+37 ≤ a.fragments.quads)
    (cables : (f).host.count=a.cube.cables) (raw : readings m (head+9)≤a.cube.maxRows)
    (cells : readings m (head+11)=a.cube.cells) (high : a.endAddress w u v k<2^w) :
    let visits := (argumentVisitsEquiv pub mac s m).symm x
    let R := a.controlRows team head offsets ctl live ports
    ∃ e : SparseEmission a f m fit cells.symm, e.bank=visits.1.val.2.1 ∧ e.output=visits.1.val.2.2 ∧
      ∀ (Site : Type) (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record),
      R.toLayout.Fields (readings e.output) → R.toLayout.Room (readings e.output) w →
      (∀ c < R.cells, readings e.output (R.sorted+R.padded+(R.stops+c))-readings e.output (R.sorted+R.padded+c)-1 =
        3*((p c).parts.length+3)) →
      ∃ patch : SparsePatch (w:=w) Site R (readings e.output), patch.placed=p ∧ patch.geometry=geom ∧ patch.extra=extra ∧
        patch.built=visits.2.1.val.2.2 ∧ ∃ last : Returns
          (.block [CellPacket.Supplement.Batch.entry,SparseExterior.prepare,TypedBatch.entry]) pub mac visits.2.1.val.2.1 patch.built,
          last.val.2.2=x.val.2.2 := by
  intro visits R
  obtain ⟨e,bank,mem⟩ := emission_of_return pub mac s m a fit pointer words before start cables raw cells high visits.1.property
  refine ⟨e,bank,mem,?_⟩
  intro Site p geom extra fields room span
  have checked := TypedTaskBuilder.program_run pub mac e.bank e.output R.toLayout rfl fields room
  obtain ⟨es,t,mt,run,_,image⟩ := checked
  rw [bank,mem] at run
  have state := (visits.2.1.property.unique_of_deterministic (by decide) run).2.2
  let patch : SparsePatch (w:=w) Site R (readings e.output) :=
    ⟨visits.2.1.val.2.2,p,geom,extra,room,(congrArg readings state).trans image,span⟩
  refine ⟨patch,rfl,rfl,rfl,rfl,visits.2.2,?_⟩
  have finish := argumentVisitsEquiv_val pub mac s m visits
  rw [show argumentVisitsEquiv pub mac s m visits=x from Equiv.apply_symm_apply ..] at finish
  exact (congrArg (fun z => z.2.2) finish).symm

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
