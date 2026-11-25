import OAI.Hierarchy.PairedCursor
import OAI.ThreeFlat.Diagonal.NativeTrace

namespace OAI
/-! # Distributing a capped weighted RAM trace with paired inputs

A summand specifies each adaptive rewrite term and each terminal shared edge label. Its scalar
factors are indexed by terminal positions. The owner of a pin follows the composed relocation
of the cursor-zero vertex of its initial bucket.
-/

noncomputable section
namespace Hierarchy.TraceDistribution

open ThreeFlat LinearAlgebra.SpectralBooks
open Diagonal Diagonal.HistoryContraction Diagonal.LaneCursor
open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.RAMMemory
open scoped BigOperators Classical

variable {F : Type} [Field F] {n k low offsets slots : ℕ} {N : BitNetwork F n}
variable (R : RowLayout N (k+1) low offsets slots) (hk : 2 ≤ k+1) (copies : ℕ)
variable (P : Plan F (PairedCursor.shape hk low offsets slots copies))

abbrev Selector := (h : P.History) × (P.finish h).Boundary

def factor (pin : Fin n → Bool) (z : Selector hk copies P) (v : (P.finish z.1).Site) : F :=
  P.cells z.1 (PairedCursor.seed R hk copies pin) v ((P.finish z.1).graph.atVertex z.2 v)

def destination (h : P.History) (j : Fin n) : (P.finish h).Site :=
  P.destination h (PairedCursor.owner R j)

theorem eval_eq (pin : Fin n → Bool) :
    N.eval pin = ∑ z : Selector hk copies P, ∏ v, factor R hk copies P pin z v := by
  rw [← PairedCursor.contract_seed R hk copies pin, P.contract_eq_cells, Fintype.sum_sigma]
  rfl

theorem factor_local (x y : Fin n → Bool) (z : Selector hk copies P) (v : (P.finish z.1).Site)
    (same : ∀ j, destination R hk copies P z.1 j=v → x j=y j) :
    factor R hk copies P x z v = factor R hk copies P y z v := by
  apply congrFun (P.cells_local _ v _ _ ?_)
  intro i hi
  exact PairedCursor.seed_local R hk copies i x y fun j hj => same j (by unfold destination; rw [hj]; exact hi)

theorem paired_owner (h : P.History) {i j : Fin n} (same : R.pinRow i=R.pinRow j) :
    destination R hk copies P h i=destination R hk copies P h j := by
  unfold destination PairedCursor.owner
  rw [same]

section Native

variable [Fintype F] {w pc regs words S base fuel : ℕ}
variable (M : Machine w pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F ≤ 2^w) (st : Word w)

abbrev layout := TraceBitHeader.layout hF t.width t.labels base st t.header t.time regs words (k:=k+1) t.grid

/-- Both consecutive pins take the same route through every stage, for every selected term. -/
theorem native_pair (Q : Plan F (PairedCursor.shape hk low (1+(((k+1)+low)+((k+1)+low)))
      (TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words ((k+1)+low)).cells copies))
    (h : Q.History) (i : ℕ) (hi : 2*i+1<S) :
    destination (layout M t hF st) hk copies Q h ⟨2*i,by omega⟩ =
      destination (layout M t hF st) hk copies Q h ⟨2*i+1,hi⟩ :=
  paired_owner _ hk copies Q h (TraceBitHeader.paired_pins hF t.width t.labels base st t.header
    t.time regs words (k:=k+1) t.grid i hi)

/-- The index of the interval in the public bucket table is the quotient of
the bit address by twice the number of rows per bucket. -/
theorem native_interval_index (i : Fin S) :
    (finFunctionFinEquiv (PairedCursor.owner (layout M t hF st) i).2).val =
      i.val / (2*2^low) := by
  unfold PairedCursor.owner splitRow
  simp only [Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_fst,Equiv.apply_symm_apply]
  change ((layout M t hF st).pinRow i).val / 2^low = _
  rw [TraceBitHeader.layout_pin,Nat.div_div_eq_div_mul]

/-- Charging a prefix fiber to its old bucket and its within-bucket address
bounds the number of input bits seen by any one terminal factor. -/
theorem native_factor_pins {B : ℕ} (extent : B≤S) {D : Type} (move : PairedCursor.Site (k+1) → D) (v : D) :
    Nat.card {j : Fin B // move (PairedCursor.owner (layout M t hF st) ⟨j.val,j.isLt.trans_le extent⟩)=v} ≤
    Nat.card {i // move i=v} * (2*2^low) := by
  classical
  let span := 2*2^low
  let input (j : Fin B) : Fin S := ⟨j.val,j.isLt.trans_le extent⟩
  let encode (j : {j : Fin B // move (PairedCursor.owner (layout M t hF st) (input j))=v}) :
      {i // move i=v} × Fin span :=
    (⟨PairedCursor.owner (layout M t hF st) (input j.1),j.2⟩,⟨j.1.val%span,Nat.mod_lt _ (by dsimp [span]; positivity)⟩)
  have inj : Function.Injective encode := by
    intro a b hab
    have owners := congrArg (fun z : {i // move i=v} × Fin span => (finFunctionFinEquiv z.1.val.2).val) hab
    have lows := congrArg (fun z : {i // move i=v} × Fin span => z.2.val) hab
    change (finFunctionFinEquiv (PairedCursor.owner (layout M t hF st) (input a.1)).2).val =
      (finFunctionFinEquiv (PairedCursor.owner (layout M t hF st) (input b.1)).2).val at owners
    rw [native_interval_index,native_interval_index] at owners
    change a.val.val/span=b.val.val/span at owners
    change a.val.val%span=b.val.val%span at lows
    apply Subtype.ext
    apply Fin.ext
    calc
      a.val.val = a.val.val%span + span*(a.val.val/span) := (Nat.mod_add_div ..).symm
      _ = b.val.val%span + span*(b.val.val/span) := by rw [owners,lows]
      _ = b.val.val := Nat.mod_add_div ..
  simpa [Nat.card_prod,span] using Nat.card_le_card_of_injective encode inj

/-- The descriptor for a terminal site is the list of initial intervals whose
cursor-zero factors are moved to it. It depends only on the compression history. -/
def intervalList {S : Shape} (Q : Plan F S) (h : Q.History)
    {lanes : ℕ} (site : Fin lanes → S.Site) (v : (Q.finish h).Site) : List (Fin lanes) :=
  (List.finRange lanes).filter (fun i => decide (Q.destination h (site i)=v))

omit [Fintype F] in
theorem intervalList_mem {S : Shape} (Q : Plan F S) (h : Q.History) {lanes : ℕ}
    (site : Fin lanes → S.Site) (v : (Q.finish h).Site) (j : Fin lanes) :
    j ∈ intervalList Q h site v ↔ Q.destination h (site j)=v := by
  simp [intervalList]

omit [Fintype F] in
/-- Every bucket interval is stored exactly once across the final descriptors. -/
theorem interval_sum {S : Shape} (Q : Plan F S) (h : Q.History) {lanes : ℕ}
    (site : Fin lanes → S.Site) :
    (∑ v : (Q.finish h).Site, (intervalList Q h site v).length) = lanes := by
  classical
  let f (i : Fin lanes) := Q.destination h (site i)
  have count (v : (Q.finish h).Site) :
      (intervalList Q h site v).length = (Finset.univ.filter (fun i => f i=v)).card := by
    have distinct : (intervalList Q h site v).Nodup := (List.nodup_finRange lanes).filter _
    rw [←List.toFinset_card_of_nodup distinct]
    congr 1
    ext j
    simp [intervalList_mem,f]
  simp_rw [count]
  simpa using (Finset.card_eq_sum_card_fiberwise (s:=Finset.univ) (t:=Finset.univ)
    (f:=f) (fun _ _ => Finset.mem_univ _)).symm

/-- This is the field-valued sum of accepting paths of the actual capped machine, including its
mounted executable header. The same compression plan works for every choice of the input. -/
theorem native_value (Q : Plan F (PairedCursor.shape hk low (1+(((k+1)+low)+((k+1)+low)))
      (TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words ((k+1)+low)).cells copies))
    (input : ℕ → Bool) :
    RAM.value (RAM.FieldCode.ofCardLe hF) M fuel st
        (RAM.memoryWithAdvice base (NativeTrace.executable M)
          (initialMemory S (fun j => TraceBitHeader.binaryWord w (input j)))) =
      ∑ z : Selector hk copies Q, ∏ v, factor (layout M t hF st) hk copies Q
        (TraceBitHeader.advicePins base (NativeTrace.executable M) input) z v := by
  rw [← NativeTrace.installed M t hF st input]
  exact eval_eq (layout M t hF st) hk copies Q _

/-- Keep the externally supplied prefix separate from the fixed input and advice. -/
def prefixBits {B : ℕ} (publicBit : ℕ → Bool) (x : Fin B → Bool) (i : ℕ) : Bool :=
  if h : i<B then x ⟨i,h⟩ else publicBit i

theorem prefix_local {B : ℕ} (size : B≤S) (publicBit : ℕ → Bool)
    (Q : Plan F (PairedCursor.shape hk low (1+(((k+1)+low)+((k+1)+low)))
      (TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words ((k+1)+low)).cells copies))
    (z : Selector hk copies Q) (v : (Q.finish z.1).Site) (x y : Fin B → Bool)
    (same : ∀ i, destination (layout M t hF st) hk copies Q z.1
      ⟨i.val,i.isLt.trans_le size⟩ = v → x i=y i) :
    factor (layout M t hF st) hk copies Q
      (TraceBitHeader.advicePins base (NativeTrace.executable M) (prefixBits publicBit x)) z v =
    factor (layout M t hF st) hk copies Q
      (TraceBitHeader.advicePins base (NativeTrace.executable M) (prefixBits publicBit y)) z v := by
  apply factor_local
  intro i hi
  unfold TraceBitHeader.advicePins
  split
  · rfl
  · unfold prefixBits
    split
    · exact same _ hi
    · rfl

end Native

end Hierarchy.TraceDistribution

end
end OAI
