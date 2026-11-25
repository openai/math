import OAI.Computability.BorderVNP.FragmentBucketPrefix
import OAI.Computability.BorderVNP.FragmentBucketScatter
import OAI.Computability.BorderVNP.FragmentBucketHeader
import OAI.Computability.BorderVNP.RoutingISADeterministic
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # The actual linear-time stable bucket program on the sparse input fragment stream -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FragmentBucket

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open private outside_of_apart from OAI.Computability.BorderVNP.FragmentBucketScatter

/-- The same fixed evaluator code reads the real controller, constructs its cell
headers and writes every occupied input interval exactly once. -/
def program : Code := setup.seq (prefixProgram.seq scatter)

/-- Native postcondition of the three passes on the initialized physical memory. -/
structure Result (l : Layout) (tag : Fin l.rows → Fin l.cells) (p : Fin l.rows → Fin 3 → ℕ)
    (before z : NatState) : Prop where
  ready : l.Ready z
  root : z.reg 0 = before.reg 0
  starts : ∀ c : Fin l.cells, z.mem (l.pairs+2*c.val) = start tag c.val
  counts : ∀ c : Fin l.cells, z.mem (l.pairs+2*c.val+1) = count tag c
  cursors : ∀ c : Fin l.cells, z.mem (l.cursors+c.val) = start tag c.val + count tag c
  fields : ∀ i : Fin l.rows, ∀ j : Fin 3, z.mem (l.triples+3*(dest tag i).val+j.val) = p i j
  other : ∀ a, Outside l.pairs (2*l.cells) a → Outside l.triples (3*l.rows) a →
    Outside l.cursors l.cells a → z.mem a = before.mem a

/-- Reading a cell's contiguous output slice yields exactly its original
subsequence of triples, in the order supplied by the native fragment emitter. -/
theorem Result.stable {l : Layout} {tag : Fin l.rows → Fin l.cells} {p : Fin l.rows → Fin 3 → ℕ} {before z}
    (h : Result l tag p before z) (c : Fin l.cells) :
    (List.finRange (count tag c)).map (fun k => fun j : Fin 3 =>
      z.mem (l.triples+3*(start tag c.val+k.val)+j.val)) =
        ((List.finRange l.rows).filter (fun i => tag i = c)).map p := by
  rw [← stable_cell tag p c]
  apply List.map_congr_left
  intro k _
  funext j
  have hr := h.fields ((dest tag).symm (cellPos tag c k)) j
  rwa [Equiv.apply_symm_apply,cellPos_val] at hr

private theorem prefixInput {l : Layout} {tag : Fin l.rows → Fin l.cells} {p : Fin l.rows → Fin 3 → ℕ}
    {w : ℕ} {z before : NatState} (fit : l.Fits w) (h : l.PrefixReady tag before z)
    (input : l.Input tag p before.mem) : l.Input tag p z.mem := by
  have read (i : Fin l.rows) (j : ℕ) (hj : j < 4) :
      z.mem (l.quads+4*i.val+j) = before.mem (l.quads+4*i.val+j) := by
    have bound : 4*i.val+j < 4*l.rows := by have := i.isLt; omega
    rw [Nat.add_assoc]
    exact h.frame _ (outside_of_apart fit.qp bound) (outside_of_apart fit.qc bound)
  refine ⟨fun i => (read i 0 (by decide)).trans (input.cell i),fun i j => ?_⟩
  rw [Nat.add_assoc,read i (1+j.val) (by have := j.isLt; omega),← Nat.add_assoc]
  exact input.field i j

/-- The fully linked code has a constant cost per occupied fragment and per cell,
with no cost proportional to the logical input width or sparse address gaps. -/
theorem program_runs {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (l : Layout) (tag : Fin l.rows → Fin l.cells) (p : Fin l.rows → Fin 3 → ℕ) (frame ctl : ℕ)
    (fit : l.Fits w) (input : l.Input tag p (readings m)) (addr : readings pub 0 = frame)
    (hdr : l.Header frame ctl (readings m)) (fr : frame+92 < 2^w) (cr : ctl+33 < 2^w) :
    BoundedRun pub macros program s m (31+19*l.cells+38*l.rows) (Result l tag p (.ofWords s m)) := by
  have load := setup_run pub macros s m l frame ctl addr hdr fr cr
  have all := load.seq (Q:=Result l tag p (.ofWords s m)) (t:=(7+19*l.cells+13*l.rows)+(2+l.rows*(scatterStep.slots+1)))
    (fun b mb header => by
      obtain ⟨rd,root,mem⟩ := header
      change readings mb = readings m at mem
      have inp : l.Input tag p (readings mb) := mem ▸ input
      apply (prefixProgram_run l fit tag p pub macros b mb rd inp).seq
      intro c mc pf
      have pass := scatter_run tag p pub macros fit c mc pf.ready (prefixInput fit pf inp) pf.cursors
      apply pass.mono le_rfl
      rintro z ⟨endReady,endRoot,h⟩
      have keep (k : Fin l.cells) (offset : ℕ) (ho : offset < 2) :
          z.mem (l.pairs+2*k.val+offset) = readings mc (l.pairs+2*k.val+offset) := by
        have bound : 2*k.val+offset < 2*l.cells := by have := k.isLt; omega
        rw [Nat.add_assoc]
        exact h.other _ (outside_of_apart fit.pt bound) (outside_of_apart fit.pc bound)
      refine ⟨endReady,endRoot.trans (pf.root.trans root),?_,?_,?_,fun i => h.written i i.isLt,?_⟩
      · intro k
        have base := pf.starts k
        change readings mc (l.startAddr k.val) = _ at base
        rw [Layout.startAddr,← two_mul] at base
        exact (keep k 0 (by decide)).trans base
      · intro k
        have b := pf.counts k
        change readings mc (l.countAddr k.val) = _ at b
        rw [Layout.countAddr,← two_mul] at b
        exact (keep k 1 (by decide)).trans b
      · intro k
        rw [h.cursor,prior_end]
      · intro a pa ta ca
        exact (h.other a ta ca).trans ((pf.frame a pa ca).trans (congrFun mem a)))
  apply all.mono _ (fun _ h => h)
  change 22+((7+19*l.cells+13*l.rows)+(2+l.rows*(24+1))) ≤ _
  omega

/-- All passes are ordinary deterministic native instructions and reach the
enclosing evaluator's continuation. -/
theorem program_control : program.deterministic = true ∧ program.withoutAccept = true := by decide

/-- Every chronological step is positive and consumes no private choice bit. -/
theorem program_unsigned : program.unsigned = true := by decide

end FragmentBucket

end BorderVNP
end Computability
end OAI
