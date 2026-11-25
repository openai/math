import OAI.Computability.BorderVNP.DiagonalResidueRAMPrepare
import OAI.Computability.BorderVNP.DiagonalResidueRAMCount
import OAI.Computability.BorderVNP.RoutingISABlockAppend

/-!
# The advised residue trace count on the delivered literal bits

The deterministic staging trace prefixes every accepting verifier trace
once. Splitting a returning path at the first verifier instruction recovers
both parts uniquely, including all previous-word probes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BooleanTranscript VPVNP.BurstRAM RoutingISA

variable {w u v k : ℕ}

/-- Accepting native event histories for the entry reader including all of its staging code. -/
def StagedPaths (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) :=
  {es : List (TeamRAM.Event w) //
    TeamRAM.execute (stagedReader.program.fetch pub mac) ⟨0,s⟩ m (es.map TeamRAM.Event.choices) = some es}

/-- Removing the uniquely executed staging prefix preserves every native path. -/
noncomputable def prefixEquiv {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m es t mt} (prep : Runs pub mac prepare s m es t mt) :
    Paths pub mac t mt ≃ StagedPaths pub mac s m := by
  let f (z : Paths pub mac t mt) : StagedPaths pub mac s m := ⟨es++z.val,by
    obtain ⟨⟨q,mq,r⟩,_⟩ := (Code.execute_iff_runs (c := reader) (by decide)).mp z.property
    exact (show Runs pub mac stagedReader s m (es++z.val) q mq from .seq prep r).execute⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b he
    exact Subtype.ext (List.append_cancel_left (congrArg Subtype.val he))
  · intro z
    obtain ⟨⟨q,mq,r⟩,_⟩ := (Code.execute_iff_runs (c := stagedReader) (by decide)).mp z.property
    obtain ⟨t',mt',pre,tail,he,hr,rest⟩ := Runs.seq_iff.mp r
    obtain ⟨rfl,rfl,rfl⟩ := prep.unique_of_deterministic (by decide) hr
    exact ⟨⟨tail,rest.execute⟩,Subtype.ext he.symm⟩

/-- The fully staged reader counts the Boolean verifier on its true query.
Only actually delivered individual literal bits and source words are required
in the initial memory. All ordinary scratch registers may be arbitrary. -/
theorem staged_count (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (base start dense : ℕ) (src : Fin u → ℕ)
    (c : Circuit (Fin u ⊕ Fin v) k) (x : Fin u → Bool)
    (L : Layout base start dense src v k w) (hpub : (pub 0).val+30 < 2^w)
    (hframe : packFrame pub m dense start (6+3*k+u))
    (hbits : DiagonalTallyBits.WordsAt m dense ((payload w base start c src).map BurstRAM.wordBits))
    (hsrc : ∀ i, m (src i) = wordBit w (x i)) :
    (Nat.card (StagedPaths pub mac s m) : ℤ) =
      ∑ y : Fin v → Bool, if c.eval (Sum.elim x y) then (1 : ℤ) else 0 := by
  obtain ⟨z,mz,⟨_,prep,_⟩,ready,query,advice⟩ := prepare_runs pub mac s m base start dense src c x
    L hpub hframe hbits hsrc
  rw [← Nat.card_congr (prefixEquiv prep)]
  have hfit : (frame base (start+6) c).fits w := by
    refine ⟨L.valuation.trans (Nat.le_add_right _ _),?_⟩
    have := L.packed
    change start+6+3*k < _; omega
  exact native_count pub mac base (start+6) c x z mz hfit ready query advice

/-- Every accepted staged path has the exact clock, positive sign and
the same private binary choices as its verifier witness. -/
theorem staged_trace (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (base start dense : ℕ) (src : Fin u → ℕ)
    (c : Circuit (Fin u ⊕ Fin v) k) (x : Fin u → Bool)
    (L : Layout base start dense src v k w) (hpub : (pub 0).val+30 < 2^w)
    (hframe : packFrame pub m dense start (6+3*k+u))
    (hbits : DiagonalTallyBits.WordsAt m dense ((payload w base start c src).map BurstRAM.wordBits))
    (hsrc : ∀ i, m (src i) = wordBit w (x i)) (path : StagedPaths pub mac s m) :
    ∃ y : Fin v → Bool, c.eval (Sum.elim x y) = true ∧
      TraceOK path.val (List.ofFn y) (prepareTicks u k w + ticks k v) := by
  obtain ⟨z,mz,⟨ps,prep,tp⟩,ready,query,advice⟩ := prepare_runs pub mac s m base start dense src c x
    L hpub hframe hbits hsrc
  obtain ⟨⟨q,mq,r⟩,_⟩ := (Code.execute_iff_runs (c := stagedReader) (by decide)).mp path.property
  obtain ⟨z',mz',pre,tail,he,hr,rest⟩ := Runs.seq_iff.mp r
  obtain ⟨rfl,rfl,rfl⟩ := prep.unique_of_deterministic (by decide) hr
  have hfit : (frame base (start+6) c).fits w := by
    refine ⟨L.valuation.trans (Nat.le_add_right _ _),?_⟩
    have := L.packed
    change start+6+3*k < _; omega
  obtain ⟨y,hy,ht⟩ := reader_complete pub mac base (start+6) c x z mz hfit ready query advice rest.execute
  exact ⟨y,hy,he ▸ (tp.append ht)⟩

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
