import OAI.Computability.MultitapeWeakETH.CNFVolume
import OAI.Computability.VPVNP.RAMSerialization
import OAI.Computability.NearSquareRoot.CRTControlledBenesRun
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-! # Routing the incidences of a trivalent formula network

A site owns four addresses with the same prefix. The ends of every wire
occupy distinct ports, even for loops. Exchanging the ends is one permutation
of all addresses, to which the verified Beneš table compiler applies.
-/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork

open Algorithms.SubexponentialSAT NearSquareRoot.Benes Finset
open scoped Classical
noncomputable section

variable {n : ℕ} (F : SAT.CNF (Fin n))

abbrev End := Wire F ⊕ Wire F
def host : End F → Site F := Sum.elim (src F) (dst F)

theorem ends_per_site (width : SAT.WidthAtMost 3 F) (v : Site F) :
    Fintype.card {e // host F e = v} ≤ 3 := by
  have count : (∑ e : End F, if host F e = v then 1 else 0) ≤ 3 := by
    rw [Fintype.sum_sum_type]
    change (∑ e, if src F e = v then (1:ℕ) else 0) + (∑ e, if dst F e = v then 1 else 0) ≤ 3
    simpa only [sum_boole,Nat.cast_id] using degree_le_three F width v
  simpa [Fintype.card_subtype] using count

private def sumKey {A B : Type} (f : A ↪ List ℕ) (g : B ↪ List ℕ) : A ⊕ B ↪ List ℕ where
  toFun := Sum.elim (fun x => 0 :: f x) (fun y => 1 :: g y)
  inj' := by
    rintro (x|y) (x'|y') eq <;> simp_all [f.injective.eq_iff,g.injective.eq_iff]

def siteKey : Site F ↪ List ℕ := sumKey (slotKey F)
  ⟨fun c => Encoding.clauseNumbers c.val,fun _ _ h => Subtype.ext (Encoding.clauseNumbers_injective h)⟩

def endKey : End F ↪ List ℕ :=
  let wire := sumKey (slotKey F) (occKey F)
  sumKey wire wire

private def bitsAt {α : Type} [Fintype α] (key : α ↪ List ℕ) {k : ℕ} (h : Fintype.card α ≤ 2^k) :
    α ↪ Word k := (FormulaRanks.ordinal key).toEmbedding.trans
      ((Fin.castLEEmb h).trans (VPVNP.RAMSerialization.wordBits k).toEmbedding)

def siteCode {k : ℕ} (fit : Fintype.card (Site F) ≤ 2^k) : Site F ↪ Word k :=
  bitsAt (siteKey F) fit

/-- Number each site and each of its used ports independently. -/
def addresses {k : ℕ} (fit : Fintype.card (Site F) ≤ 2^k) (width : SAT.WidthAtMost 3 F) :
    End F ↪ Word (k+2) :=
  let site := siteCode F fit
  let port (v : Site F) : {e // host F e = v} ↪ Word 2 := bitsAt
    ((Function.Embedding.subtype _).trans (endKey F)) ((ends_per_site F width v).trans (by decide))
  let packed : End F ↪ Word k × Word 2 := {
    toFun e := (site (host F e), port (host F e) ⟨e,rfl⟩)
    inj' := by
      intro x y eq
      obtain ⟨hx,px⟩ := Prod.mk.inj eq
      have hosts := site.injective hx
      have py : port (host F x) ⟨x,rfl⟩ = port (host F x) ⟨y,hosts.symm⟩ := by
        convert! px using 1
        generalize host F x = v at hosts ⊢
        subst v
        rfl
      exact congrArg Subtype.val ((port _).injective py) }
  packed.trans (Fin.appendEquiv k 2).toEmbedding

theorem address_prefix {k : ℕ} (fit : Fintype.card (Site F) ≤ 2^k) (width : SAT.WidthAtMost 3 F)
    (e : End F) (j : Fin k) : addresses F fit width e (j.castAdd 2) = siteCode F fit (host F e) j :=
  Fin.append_left ..

def exchange {k : ℕ} (fit : Fintype.card (Site F) ≤ 2^k) (width : SAT.WidthAtMost 3 F) :
    Equiv.Perm (Word (k+2)) :=
  Equiv.Perm.viaEmbedding (Equiv.sumComm (Wire F) (Wire F)) (addresses F fit width)

/-- One permutation table serves all wires simultaneously. Padding addresses are fixed. -/
theorem route_ends {k : ℕ} (fit : Fintype.card (Site F) ≤ 2^k) (width : SAT.WidthAtMost 3 F) :
    ∃ table : RawTable, RawRepresents (exchange F fit width) table ∧
      ∀ e : End F, (executionOrder (k+2)).foldl
        (fun w a => stagePerm table a.1 a.2 w) (addresses F fit width e) =
        addresses F fit width (e.swap) := by
  let p := exchange F fit width
  let number := VPVNP.RAMSerialization.wordBits (k+2)
  let keys := List.ofFn number
  let table := keys.map fun x => (List.ofFn x,List.ofFn (p x))
  have repr : RawRepresents p table := ⟨keys,List.nodup_ofFn.mpr number.injective,fun x => List.mem_ofFn.mpr (number.surjective x),rfl⟩
  refine ⟨table,repr,fun e => ?_⟩
  rw [stagesPerm_run p table repr]
  exact Equiv.Perm.viaEmbedding_apply _ _ _

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork
