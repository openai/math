import OAI.Hierarchy.TaggedShorterCPURow
import OAI.Hierarchy.TaggedRadixPins
import OAI.ThreeFlat.Diagonal.TraceCpuPacket
import OAI.ThreeFlat.Diagonal.TraceClockSites

namespace OAI
/-! # Canonically padded finite CPU history checked on its stored bits -/

noncomputable section
namespace Hierarchy.TaggedShorterClock
open ThreeFlat Routing Diagonal TraceRows TracePair TraceBanks TraceWords
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open scoped Classical BigOperators

variable {F : Type*} [CommRing F] {w p r k f : ℕ}
abbrev Pin (w r f : ℕ) := Fin f × Fin ((5+r)*(w+1))

private def here (t : ℕ) (b : Fin ((5+r)*(w+1))) : Pin w r f ⊕ Bool :=
  if h : t<f then .inl (⟨t,h⟩,b) else .inr false

private def rowPin (t : ℕ) (a : CodePin w r) : Pin w r f ⊕ Bool := here t (finProdFinEquiv a)
private def pairPin (t : ℕ) (a : Raw w r) : Pin w r f ⊕ Bool :=
  rowPin (if a.1 then t+1 else t) a.2

private theorem readRow (hw : 3≤w+1) (hp : p≤2^(w+1)) (rows : Fin f → Record w p r)
    (t : ℕ) (a : CodePin w r) :
    Sum.elim (Function.uncurry (writeCpu hw hp rows)) id (rowPin t a) =
      bits ((rowFormat hw hp).words (clockAt rows t) a.1) a.2 := by
  rw [bits,Computability.VPVNP.LiveHeader.testBit_wordBits,←arrayBits_at]
  by_cases hi : t<f
  · simp [rowPin,here,clockAt,hi,writeCpu,Format.encode]
  · simpa [rowPin,here,clockAt,hi,Format.encode] using
      (congrFun (TraceRowPackets.padding_encode (r:=r) hw hp) (finProdFinEquiv a)).symm

private def test {σ : Type} [Fintype σ] (v : TraceCompose.Packet σ) : BitNetwork F (Fintype.card σ) :=
  TraceCircuit.localNetwork (fun _ : Fin 1 => v) (Fintype.equivFin _) (fun _ b => if b then 1 else 0)

private theorem test_eval {σ : Type} [Fintype σ] (v : TraceCompose.Packet σ) (x : σ → Bool) :
    TypedWiring.value (test (F:=F) v) x = if v.2.eval x then 1 else 0 := by
  simp [TypedWiring.value,test,TraceCircuit.localNetwork_eval,Function.comp_def]

def pieces (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w) :
    Option (Fin f × Bool) → BitNetwork F (Fintype.card (Pin w r f))
  | none => Tagged.RadixStage.pullPins
      (test (formulaPacket (initialCheck hp M.entry (fun j => .const (bits (wide st) j))
        (fun x : CodePin w r => Expr.input x)))) (rowPin 0)
  | some (i,false) => Tagged.RadixStage.pullPins
      (test ⟨_,(canonicalFrame (r:=r) hw hp).circuit ()⟩) (rowPin i.val)
  | some (i,true) => Tagged.RadixStage.pullPins (TaggedShorterCPURow.network M) (pairPin i.val)

def network (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w) :
    BitNetwork F (Fintype.card (Pin w r f)) :=
  TypedWiring.glue (pieces M hw hp st) (fun _ u => (Sum.inl u : Pin w r f ⊕ Empty))

private theorem product_eval (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1))
    (st : Word w) (x : Pin w r f → Bool) :
    TypedWiring.value (network (F:=F) M hw hp st) x =
      ∏ s, TypedWiring.value (pieces M hw hp st s) x := by
  simp [network,TypedWiring.glue_value]

private theorem canonical (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (x : Pin w r f → Bool) (i : Fin f) :
    TypedWiring.value (pieces (F:=F) M hw hp st (some (i,false))) x =
      if writeCpu hw hp (readCpu hw hp (Function.curry x)) i = Function.curry x i then 1 else 0 := by
  rw [pieces,Tagged.RadixStage.pullPins_value,test_eval]
  have e : Sum.elim x id ∘ rowPin i.val = fun j => Function.curry x i (finProdFinEquiv j) := by
    funext j; simp [rowPin,here,i.isLt,Function.curry]
  rw [e]
  by_cases yes : writeCpu hw hp (readCpu hw hp (Function.curry x)) i = Function.curry x i
  · simp only [ite_eq_left yes,ite_eq_left ((TraceRowPackets.canonical_roundtrip hw hp M.entry _).mpr yes)]
  · simp only [ite_eq_right yes,ite_eq_right (fun h => yes ((TraceRowPackets.canonical_roundtrip hw hp M.entry _).mp h))]

/-- Every bit in the clock array, including padding, has one canonical
assignment. For that assignment, the circuit tests all transitions and its
initial state on the actual physical CPU instruction graph. -/
theorem checks (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w) (x : Pin w r f → Bool) :
    TypedWiring.value (network (F:=F) M hw hp st) x =
      if let rows:=readCpu hw hp (Function.curry x)
         writeCpu hw hp rows=Function.curry x ∧
         Local (exposed M) ((exposed M).start (wide st)) (List.ofFn rows) then 1 else 0 := by
  let rows := readCpu hw hp (Function.curry x)
  by_cases good : writeCpu hw hp rows=Function.curry x
  · have atX : Function.uncurry (writeCpu hw hp rows)=x := by rw [good]; rfl
    have localCheck := TraceRows.local_iff_pairs (exposed M) ((exposed M).start (wide st)) (List.ofFn rows)
    have entry : TypedWiring.value (pieces (F:=F) M hw hp st none) x =
        if before ((List.ofFn rows).headD .pad) = some ((exposed M).start (wide st)) then 1 else 0 := by
      rw [pieces,Tagged.RadixStage.pullPins_value,test_eval,formulaPacket_eval,ofFn_headD]
      have check := initialCheck_at hw hp M.entry st (fun j => .const (bits (wide st) j))
        (fun a : CodePin w r => .input a) (Sum.elim x id ∘ rowPin 0) (clockAt rows 0) (fun _ => rfl)
        (fun u v => atX ▸ readRow hw hp rows 0 (u,v))
      simp [check,exposed]
    have moves i : TypedWiring.value (pieces (F:=F) M hw hp st (some (i,true))) x =
        if pair (exposed M) (rows i) (clockAt rows (i.val+1)) then 1 else 0 := by
      rw [pieces,Tagged.RadixStage.pullPins_value,←TaggedShorterCPURow.checks M hw hp]
      apply congrArg _
      funext ⟨side,j,q⟩
      rw [←atX]
      cases side with
      | false => simpa [pairPin,TracePair.packed,clockAt,i.isLt] using readRow hw hp rows i.val (j,q)
      | true => exact readRow hw hp rows (i.val+1) (j,q)
    have roundtrip (i : Fin f) : TypedWiring.value (pieces (F:=F) M hw hp st (some (i,false))) x = 1 :=
      (canonical M hw hp st x i).trans (ite_eq_left (congrFun good i))
    let head := before ((List.ofFn rows).headD .pad) = some ((exposed M).start (wide st))
    let adjacent := fun i:Fin f => pair (exposed M) (rows i) (clockAt rows (i.val+1))
    have audit : Local (exposed M) ((exposed M).start (wide st)) (List.ofFn rows) ↔ head ∧ ∀ i, adjacent i :=
      localCheck.trans (and_congr Iff.rfl (pairs_ofFn_iff (exposed M) rows))
    rw [product_eval,Fintype.prod_option,entry,Fintype.prod_prod_type]
    simp only [Fintype.prod_bool,moves,roundtrip,mul_one]
    change (if head then (1:F) else 0) * (∏ i, if adjacent i then 1 else 0) =
      if writeCpu hw hp rows=Function.curry x ∧ Local (exposed M) ((exposed M).start (wide st)) (List.ofFn rows) then 1 else 0
    have test := Fintype.prod_boole (M₀:=F) (p:=adjacent)
    rw [test]
    by_cases first : head
    · by_cases all : ∀i,adjacent i
      · rw [ite_eq_left first,ite_eq_left all,ite_eq_left ⟨good,audit.mpr ⟨first,all⟩⟩,one_mul]
      · rw [ite_eq_left first,ite_eq_right all,ite_eq_right (fun h => all (audit.mp h.2).2),one_mul]
    · rw [ite_eq_right first,zero_mul,ite_eq_right (fun h => first (audit.mp h.2).1)]
  · change _ = if writeCpu hw hp rows=Function.curry x ∧ _ then 1 else 0
    rw [ite_eq_right (fun h => good h.1),product_eval]
    obtain ⟨i,ne⟩ := Function.ne_iff.mp good
    apply Finset.prod_eq_zero (Finset.mem_univ (some (i,false)))
    exact (canonical M hw hp st x i).trans (ite_eq_right ne)

end Hierarchy.TaggedShorterClock

end
end OAI
