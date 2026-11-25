import OAI.Computability.BorderVNP.DiagonalTallyAlign

/-! # Complete fixed-address evaluation on the actual sparse operand count -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM DiagonalTallyMaterialize
open private supplied_unchanged from OAI.Computability.BorderVNP.DiagonalTallyRAMAllocatedRun

/-- Align the runtime record interval, initialize the fixed-address sums, and compute the
entire residue query at the length-only address installed in the entry-reader frame. -/
def alignedAllocateAndEvaluate : Code := .seq alignTallies allocateAndEvaluate

/-- Every operand still lies before a later fresh record boundary. -/
theorem supplied_mono {w : ℕ} (m : Memory w) {lo hi : ℕ} (hle : lo ≤ hi) (p : ℕ) (os : List Operand)
    (input : supplied m lo p os) : supplied m hi p os := by
  induction os generalizing p with
  | nil => trivial
  | cons o os ih =>
    obtain ⟨word,before,res,fit,tail⟩ := input
    exact ⟨word.trans hle,⟨before.1.trans_le hle,before.2.1.trans_le hle,before.2.2.1.trans hle,
      fun j hj => (before.2.2.2 j hj).trans_le hle⟩,res,fit,ih _ tail⟩

/-- The same genuine sparse input and broadcast produce the exact common query bits,
with the additional alignment update touching only the dedicated frame pointer. -/
theorem alignedAllocateAndEvaluate_natural_runs {w : ℕ} (a : Arena) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) (os : List Operand)
    (p : ℕ) (rows : Fin a.teams → Fin a.dim → ℕ)
    (seed : a.alignedSeed pub m p) (fit : a.Fits w (pub 0).val) (hdir : (pub 0).val+101<2^w)
    (ops : supplied m a.fresh p os)
    (opSep : ∀ q, operandReads p os q → outsidePointers (pub 0).val q ∧ q≠(pub 0).val+34)
    (rawSep : ∀ q, a.raw≤q → q<a.raw+(a.teams*a.dim)*a.width → outsidePointers (pub 0).val q ∧ q≠(pub 0).val+34)
    (count : os.length=a.count) (coords : ∀ o∈os,o.pair.1<a.dim)
    (bits : DiagonalTallyBits.WordsAt m a.raw (broadcast a.width rows))
    (localCounts : ∀ c, a.localRow os c.val=rows ⟨a.team,fit.team⟩ c)
    (rowFit : ∀ i c,rows i c<2^a.width) (sumFit : ∀ c, ∑ i, rows i c<2^w) :
    ∃ es t m', Runs pub mac alignedAllocateAndEvaluate s m es t m' ∧
      traceCost es ≤ alignTallies.slots+allocateTallies.slots+a.work w os ∧
      (∀ e∈es,e.choices=[] ∧ e.sign=.plus ∧ e.action.extra=0) ∧
      ∀ c : Fin a.dim, ∀ j<w, m' ((a.bitFrame w).dst+(c.val*w+j))=
        word w (((∑ i,rows i c).testBit j).toNat) := by
  obtain ⟨a₀,u,mu,r₀,c₀,img,trace₀⟩ := alignTallies_runs pub mac s m _ _ seed.2.1 seed.2.2.1
    (by omega) (Nat.le_add_left _ _)
  change readings mu=Function.update (readings m) ((pub 0).val+34) (a.fresh+2*a.count-2*a.count) at img
  rw [Nat.add_sub_cancel] at img
  have keep (j : ℕ) (hn : j≠(pub 0).val+34) : mu j=m j := by
    apply Fin.ext
    change readings mu j=readings m j
    rw [img,Function.update_of_ne hn]
  have raw' : DiagonalTallyBits.WordsAt mu a.raw (broadcast a.width rows) :=
    DiagonalTallyBits.words_congr m mu a.raw a.width _ bits (by
      intro b hb
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hb
      exact length_wordBits _) (by
      intro j hj hi
      simp only [broadcast,List.length_ofFn] at hi
      exact keep _ (rawSep _ hj hi).2)
  have ops' := supplied_unchanged m mu p a.fresh os ops (fun j hj => keep j (opSep j hj).2)
  obtain ⟨b,t,mt,r₁,c₁,tr₁,data⟩ := allocateAndEvaluate_natural_runs a pub mac u mu os p rows
    (a.seed_after_align pub m mu p seed img) fit hdir ops' (fun j hj => (opSep j hj).1)
    (fun j hj hi => (rawSep j hj hi).1) count coords raw' localCounts rowFit sumFit
  refine ⟨_,t,mt,r₀.seq r₁,?_,?_,data⟩
  · rw [show traceCost (a₀++b)=traceCost a₀+traceCost b from VPVNP.RAMBuckets.cost_append ..,Nat.add_assoc]
    exact Nat.add_le_add c₀ c₁
  · intro e he
    exact (List.mem_append.mp he).elim (trace₀ e) (tr₁ e)

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
