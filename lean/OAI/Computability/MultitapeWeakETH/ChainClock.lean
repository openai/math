import OAI.Computability.MultitapeWeakETH.ChainExecution
import OAI.Computability.MultitapeWeakETH.BoundedSweep

/-! # Polynomial tape time for deterministic replay of a full candidate history -/

namespace OAI.Computability.MultitapeWeakETH.CallProgram

open IntegerMultiplication Code VPVNP RAMTape BurstRAM PrivateRAM NativeGrid
open private publicZero from OAI.Computability.MultitapeWeakETH.ChainExecution
noncomputable section

variable {p r k : ℕ}

private abbrev RowInput (p : ℕ) := Bits.Word × (Tally × State p) × Tally

private def prepareRow (T : Template p r k) (q : RowInput p) :=
  ((q.2.2,q.2.1.1,feedBytes T (q.1,q.2.1.2)),q.2.2)

private theorem prepareRow_poly (T : Template p r k) : Poly (prepareRow T) := by
  let left : Poly (fun q : RowInput p => feedBytes T (q.1,q.2.1.2)) :=
    (Easy.fst.poly.pair (by fun_prop)).compose (feed_poly T)
  have grid : Poly (fun q : RowInput p => q.2.1.1) := by fun_prop
  have fuel : Poly (fun q : RowInput p => q.2.2) := by fun_prop
  exact (fuel.pair (grid.pair left)).pair fuel

private theorem prefix_cost (prefixItems all : List Bits.Word) (prefixOf : prefixItems <+: all) :
    (prefixItems.map List.length).sum ≤ size all := by
  have mass (l : List Bits.Word) : (l.map List.length).sum ≤ size l := by
    induction l with
    | nil => simp
    | cons x l ih => simp only [List.map_cons,List.sum_cons,size_cons,Bits.size_word]; omega
  obtain ⟨tail,he⟩ := prefixOf
  change prefixItems++tail = all at he
  have eq := size_append_right prefixItems tail
  rw [he] at eq
  have := size_pos tail
  exact (mass _).trans (by omega)

theorem chain_on {I : Type} (T : Template p r k) (read : Read) (hr : Poly read)
    (budget w fuel : I → ℕ) (grid : I → Tally) (tapes : I → List Bits.Word)
    (base : ∀ i, Memory (w i))
    (rd : ∀ i log (a : Word (w i)), read ((grid i,wordBits a),writes log) = wordBits (memory (base i) log a.val))
    (hw : Dom budget w) (hf : Dom budget fuel) (hg : Dom budget (fun i => size (grid i)))
    (ht : Dom budget (fun i => size (tapes i))) :
    let seed (i : I) : Model (w i) p r := .finished (some 0) []
    let physical (i : I) (x : Model (w i) p r) := ((grid i,encode (publicZero k (w i)) x),tally (fuel i))
    Task.BT budget (fun i => send (tapes i,physical i (seed i)))
      (fun i => send (physical i ((tapes i).foldl (pass T (base i) (fuel i)) (seed i)))) := by
  intro seed physical
  let pre (l : List Bits.Word) (i : I) := (tapes i).take ((tapes i).length-l.length)
  let current (l : List Bits.Word) (i : I) := (pre l i).foldl (pass T (base i) (fuel i)) (seed i)
  let acc (l : List Bits.Word) (i : I) := send (physical i (current l i))
  let m (i : I) := size (tapes i) + 2*fuel i*(tapes i).length
  have hm : Dom budget m := ht.add (((Dom.const _ 2).mul hf).mul (ht.mono fun i => (duration _).le))
  have before (l : List Bits.Word) (i : I) : load (current l i) ≤ m i := by
    have h : pre l i <+: tapes i := List.take_prefix _ _
    have a := chain_load T (base i) (fuel i) (pre l i) (seed i)
    change load (current l i) ≤ 0+(List.map List.length (pre l i)).sum+2*fuel i*(pre l i).length at a
    rw [Nat.zero_add] at a
    exact a.trans (Nat.add_le_add (prefix_cost _ _ h) (Nat.mul_le_mul_left _ h.length_le))
  let Q := SweepRow tapes
  let i₀ (q : Q) := q.val.2.2
  let curr (q : Q) := current (q.val.1::q.val.2.1) (i₀ q)
  let L (q : Q) := budget (i₀ q)
  have payload : Dom L (fun q : Q => size q.val.1) :=
    (ht.map i₀).mono fun q => (size_bel (q.property.subset List.mem_cons_self)).le
  have afterFeed : Dom L (fun q : Q => load (feed T q.val.1 (curr q))) :=
    ((hm.map i₀).add payload).mono fun q => (feed_load T q.val.1 (curr q)).trans
      (Nat.add_le_add (before _ _) (duration _).le)
  let query (q : Q) : RowInput p := (q.val.1,physical (i₀ q) (curr q))
  have henc : Dom L (fun q : Q => size (encode (publicZero k (w (i₀ q))) (curr q))) :=
    (capacity_dom p r k (hw.map i₀) (hm.map i₀)).mono fun q => encode_size _ _ _ (before _ _)
  have hcap := (((Dom.const L 2).mul (hf.map i₀)).add (Dom.const L 1))
  have sizeQ : Dom L (fun q => size (query q)) := by
    have h := (payload.add (((((hg.map i₀).add henc).add (Dom.const L 1)).add hcap).add (Dom.const L 1))).add (Dom.const L 1)
    simpa only [query,physical,size_prod,size_tally,tally_length] using h
  obtain ⟨cost,bound,one⟩ := call_on T read hr L _ (fun q => fuel (i₀ q)) (fun q => grid (i₀ q))
    (fun q => publicZero k (w (i₀ q))) (fun q => base (i₀ q)) (fun q => feed T q.val.1 (curr q))
    (fun q => rd (i₀ q)) (hw.map i₀) (hf.map i₀) (hg.map i₀) afterFeed
  have oneLeft := one.left (fun q : Q => send (tally (fuel (i₀ q))))
  have prep := (prepareRow_poly T).on sizeQ
  suffices work : Task.BT budget (fun i => Tree.fork (send (tapes i)) (acc (tapes i) i)) (acc []) by
    obtain ⟨t,ht,exec⟩ := work
    exact ⟨t,ht,exec.conform (fun _ => rfl) (fun i => by simp [acc,current,pre]) (fun i => by simp [acc,current,pre])⟩
  apply bounded_sweep budget tapes acc ht
  obtain ⟨prepCost,prepBound,P⟩ := prep
  refine ⟨_,prepBound.add bound,P.compose (oneLeft.conform (fun _ => rfl) ?_ ?_)⟩
  · intro q
    rw [← feed_spec]
    rfl
  · rintro ⟨⟨b,l,i⟩,⟨xs,eq⟩⟩
    change send (physical i (pass T (base i) (fuel i) (current (b::l) i) b)) = send (physical i (current l i))
    change xs++b::l = tapes i at eq
    have h : (xs ++ b::l).take (xs.length+1) = xs++[b] := by rw [List.take_append]; simp
    simp only [current,pre,← eq,List.length_append,List.length_cons,Nat.add_sub_cancel]
    rw [show xs.length+(l.length+1)-l.length=xs.length+1 by omega,h]
    simp [List.foldl_append]

end
end OAI.Computability.MultitapeWeakETH.CallProgram
