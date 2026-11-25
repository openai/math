import OAI.Computability.MultitapeWeakETH.CallCapacity

/-! # A polynomially charged tape program for each full descriptor call -/

namespace OAI.Computability.MultitapeWeakETH.CallProgram

open IntegerMultiplication Code VPVNP RAMTape BurstRAM PrivateRAM NativeGrid
noncomputable section

variable {p r k : ℕ}

/-- Evaluate all instructions up to the fuel bound with the same tape
program, also when the supplied branch bits lead to rejection. Width, fuel
and starting log may vary together with the input. -/
theorem call_on {I : Type} (T : Template p r k) (read : Read) (hr : Poly read)
    (budget w fuel : I → ℕ) (grid : I → Tally) (pub : ∀ i, Fin k → Word (w i))
    (base : ∀ i, Memory (w i)) (x : ∀ i, Model (w i) p r)
    (rd : ∀ i log (a : Word (w i)), read ((grid i,wordBits a),writes log) = wordBits (memory (base i) log a.val))
    (hw : Dom budget w) (hf : Dom budget fuel) (hg : Dom budget (fun i => size (grid i)))
    (hx : Dom budget (fun i => load (x i))) :
    Task.BT budget (fun i => send (tally (fuel i),grid i,encode (pub i) (x i)))
      (fun i => send (grid i,encode (pub i) ((modelStep T (pub i) (base i))^[fuel i] (x i)))) := by
  let step (q : Tally × State p) := (q.1,tick T read q)
  have hstep : Poly step := Easy.fst.poly.pair (tick_poly T read hr)
  let seed (i : I) := (grid i,encode (pub i) (x i))
  have eq (i : I) (j : ℕ) : step^[j] (seed i) =
      (grid i,encode (pub i) ((modelStep T (pub i) (base i))^[j] (x i))) := by
    induction j with
    | zero => rfl
    | succ j ih => simp only [Function.iterate_succ_apply',ih,step,tick_spec T (pub i) read (grid i) (base i) (rd i)]

  let m (i : I) := load (x i) + 2*fuel i
  have hm : Dom budget m := hx.add ((Dom.const _ 2).mul hf)
  let c := Dom.const budget
  have cap := capacity_dom p r k hw hm
  obtain ⟨d,C,lim⟩ := (hg.add cap).add (c 1)
  have runs := bounded_iteration budget fuel seed step hstep hf C d (fun i j hj => ?_)
  · simpa only [eq,seed] using runs
  · rw [eq,size_prod]
    apply le_trans _ (lim i)
    have small := (load_iterate T (pub i) (base i) (x i) j).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ hj) _)
    exact Nat.add_le_add_right (Nat.add_le_add_left (encode_size _ _ (m i) small) _) _

end
end OAI.Computability.MultitapeWeakETH.CallProgram
