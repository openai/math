import OAI.Hierarchy.ProtocolRAMCatalystLayoutTypes
import OAI.Hierarchy.ProtocolRAMCatalystOwnerWords
import OAI.Hierarchy.ProtocolRAMDisjointPassReads
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Executable owner lookup from the retained strip geometries -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical Fin.CommRing
variable {w q d count payload : ℕ}

/-- An inactive or padded slot can have any old operand. All scatter destinations
are valid even for a zero amount; positive rows keep their exact pair key. -/
def clamp (count : ℕ) (term : Expr) : Expr :=
  .branch .lt term (.lit count) term (.lit 0)

def key (positive : 0<count) (v : Word w) : Fin count :=
  if h : v.val<count then ⟨v.val,h⟩ else ⟨0,positive⟩

theorem clamp_eval (pos : 0<count) (fit : count<2^w) (t : Expr) (m : Memory w) (r : Word w) :
    (clamp count t).eval m r=((key pos (t.eval m r)).val:Word w) := by
  simp only [clamp,Expr.eval,Comparison.test,Fin.lt_def,decide_eq_true_eq,Fin.val_cast_of_lt fit,key]
  split_ifs <;> simp

theorem key_true (pos : 0<count) (fit : count<2^w) (i : Fin count) :
    key pos (i.val:Word w)=i := by
  apply Fin.ext
  simp [key,Fin.val_cast_of_lt (i.isLt.trans fit),i.isLt]

namespace OwnerLedger
variable (L : OwnerLedger) (c : Mesh)

def stage (count : ℕ) (ev : Event) : Pass :=
  ⟨L.arena.base c ev,L.rows ev,clamp count (L.term ev)⟩

def scans (count : ℕ) : List Pass := (events c).map (L.stage c count)

theorem ordered (count : ℕ) (span : ∀e∈events c,L.rows e≤L.arena.stride) :
    (L.scans c count).Pairwise (fun a b=>a.out+a.rows≤b.out ∨ b.out+b.rows≤a.out) := by
  have order : ((events c).map (position c)).Pairwise (·<·) := by rw [positions]; exact List.pairwise_lt_range
  rw [List.pairwise_map] at order
  rw [scans,List.pairwise_map]
  apply order.imp_of_mem
  intro a b ha _ ht
  exact Or.inl ((Nat.add_le_add_left (span a ha) _).trans (L.arena.apart c ht))

theorem before (count : ℕ) (m : Memory w) (x : ℕ) (prior : x<L.arena.first) :
    result (L.scans c count) m x=m x := by
  apply result_below
  intro p hp
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hp
  exact prior.trans_le (Nat.le_add_right ..)

theorem addressed (pos : 0<count) (width : count<2^w) (m : Memory w)
    (span : ∀e∈events c,L.rows e≤L.arena.stride) (e : Event) (time : e∈events c)
    (fits : (L.term e).Fits w L.arena.first) (row : Fin (L.rows e)) :
    result (L.scans c count) m (L.arena.base c e+row.val)=
      ((key pos ((L.term e).eval m (row.val:Word w))).val:Word w) := by
  have guard : (clamp count (L.term e)).Fits w L.arena.first := ⟨fits,trivial,fits,trivial⟩
  exact (FeedLayout.scheduled_read (L.scans c count) m (L.stage c count e)
    (List.mem_map_of_mem time) row L.arena.first guard (by
      intro p hp
      obtain ⟨f,_,rfl⟩ := List.mem_map.mp hp
      exact Nat.le_add_right ..) (L.ordered c count span)).trans (clamp_eval pos width _ _ _)

theorem execute (count : ℕ) (m : Memory w) (span : ∀ e∈events c,L.rows e≤L.arena.stride)
    (inputs : ∀ e∈events c,(L.term e).Fits w L.arena.first) (room : L.arena.endAddress c<2^w) :
    (program w (L.scans c count)).Exec m (result (L.scans c count) m) (clock (L.scans c count)) := by
  apply program_exec
  intro p hp
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
  have fit := ProtocolRAMGeneratedWrite.fits_mono (L.term e)
    (show L.arena.first≤L.arena.base c e from Nat.le_add_right ..) (inputs e he)
  change (clamp count (L.term e)).Fits w (L.arena.base c e) ∧ _
  exact ⟨⟨fit,trivial,fit,trivial⟩,((Nat.add_le_add_left (span _ he) _).trans (L.arena.within c e he)).trans_lt room⟩

theorem time_bound (count r cost : ℕ)
    (span : ∀e∈events c,L.rows e≤r ∧ (clamp count (L.term e)).work≤cost) :
    clock (L.scans c count)≤4+(events c).length*(4+r*(2*cost+4)) := by
  simpa only [scans,List.length_map] using clock_le (L.scans c count) r cost (by
    intro p hp; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp; exact span _ he)

end OwnerLedger
end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
