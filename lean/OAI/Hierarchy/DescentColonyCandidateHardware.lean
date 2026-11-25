import OAI.Hierarchy.DescentColonyCandidateRAM

namespace OAI
/-! # Instruction and hardware bounds for the native multiplier scorer -/

noncomputable section
namespace Hierarchy.DescentColonies.CandidateRAM
open ProtocolRAM Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open NativeBatch
open DescentGL (Bits Nonzero)

def storage {w : ℕ} (P : Procedure w) := P.labels+P.registers+P.slots

structure Bounded {w : ℕ} (P : Procedure w) (t : ℕ) : Prop where
  cheap : CheapCode P
  size : storage P≤4*t

theorem seq_bound {w : ℕ} {A B : Procedure w} {s t : ℕ}
    (a : Bounded A s) (b : Bounded B t) : Bounded (A.seq B) (s+t) := by
  refine ⟨cheap_seq a.cheap b.cheap,?_⟩
  have one := a.size
  have two := b.size
  dsimp only [storage,Procedure.seq] at *
  omega

theorem empty_bound (w : ℕ) : Bounded (ProtocolRAM.program w []) 4 := by
  refine ⟨program_cheap w [],?_⟩
  change 15≤4*4
  decide

theorem scan_bound (w out n : ℕ) (e : Expr) (positive : 0<n) :
    Bounded (scan w out n e) (4+n*(2*e.work+4)) := by
  refine ⟨scan_cheap w out n e,?_⟩
  have scaled := Nat.mul_le_mul_right (2*e.work+4) positive
  obtain ⟨l,r,s⟩ := scan_size w out n e
  unfold storage
  rw [l,r,s]
  omega

theorem passes_bound (w : ℕ) (ps : List Pass) (live : ∀p∈ps,0<p.rows) :
    Bounded (ProtocolRAM.program w ps) (ProtocolRAM.clock ps) := by
  induction ps with
  | nil => exact empty_bound w
  | cons p ps ih =>
    exact seq_bound (scan_bound w p.out p.rows p.term (live p List.mem_cons_self))
      (ih (fun q hq => live q (List.mem_cons_of_mem p hq)))

theorem batch_bound {w N : ℕ} (f : Fin N → Code w) (ok : ∀i,Bounded (f i).text (f i).ticks)
    (n : ℕ) (hn : n≤N) : Bounded (Code.seq f n hn).text (Code.seq f n hn).ticks := by
  induction n with
  | zero => exact empty_bound _
  | succ n ih => exact seq_bound (ih _) (ok _)

private theorem group_bound {H k : ℕ} (w base : ℕ) (incoming : Fin H→List (Fin H)) (p : Fin H→ℕ)
    (D cap : ℕ) (a μ : Bits k) : Bounded (SiteRAM.groupCode w k base incoming p D cap a μ).text
       (SiteRAM.groupCode w k base incoming p D cap a μ).ticks := by
  apply seq_bound
  · exact batch_bound (SiteRAM.transfer w k base p a μ)
      (fun _=>scan_bound _ _ _ _ (Nat.two_pow_pos _)) _ _
  · apply seq_bound
    · apply passes_bound
      intro q hq
      rw [LayerRAM.pass_rows hq]
      exact Nat.two_pow_pos _
    · exact scan_bound _ _ 1 _ (by decide)

theorem candidate_bound {G H k : ℕ} (w base : ℕ) (incoming : Fin H→List (Fin H))
    (ptr : Fin G→Fin H→ℕ) (D cap : ℕ) (a : Bits k) (μ : Nonzero k) :
    Bounded (program w base incoming ptr D cap a μ) (ticks w base incoming ptr D cap a μ) :=
  seq_bound (batch_bound (steps w base incoming ptr D cap a μ)
    (fun g => group_bound w (output g.val H k base) incoming (ptr g) D cap a μ.val) G le_rfl)
    (scan_bound w (output G H k base) 1 (tally G (receipt H k base)) (by decide))

theorem program_cheap {G H k : ℕ} (w base : ℕ) (incoming : Fin H→List (Fin H))
    (ptr : Fin G→Fin H→ℕ) (D cap : ℕ) (a : Bits k) (μ : Nonzero k) :
    CheapCode (program w base incoming ptr D cap a μ) :=
  (candidate_bound w base incoming ptr D cap a μ).cheap

theorem program_size {G H k : ℕ} (w base : ℕ) (incoming : Fin H→List (Fin H))
    (ptr : Fin G→Fin H→ℕ) (D cap : ℕ) (a : Bits k) (μ : Nonzero k) :
    let P := program w base incoming ptr D cap a μ
    P.labels+P.registers+P.slots≤4*ticks w base incoming ptr D cap a μ :=
  (candidate_bound w base incoming ptr D cap a μ).size

end Hierarchy.DescentColonies.CandidateRAM

end
end OAI
