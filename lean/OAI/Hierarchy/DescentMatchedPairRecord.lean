import OAI.Hierarchy.DescentMatchedPairRAM

namespace OAI
/-! # All nine native field passes and preservation of the preceding chosen pairs -/

namespace Hierarchy.DescentPacking.PairRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing
variable {w n : ℕ} {s : Inputs} {z bins dest dead scratch : ℕ}

theorem low (x : ℕ) {cut : ℕ} (bound : (Bank.mk x 0).Fits w cut) : x < cut := by
  exact (show x+1 ≤ cut from bound.2.2)

def agrees (cut : ℕ) (a b : Memory w) := ∀ x < cut,a x=b x

theorem pass_agrees (m : Memory w) (b : Space w n s bins dest dead scratch m) (f : Fin 9) :
    agrees dest (writes (n:=n) s z bins dest dead scratch f m) m := by
  intro x hx
  have := b.dense
  have := b.padding
  apply keeps
  · intro q
    unfold target
    split <;> omega
  · omega

theorem transfer {a b : Memory w} (p : Space w n s bins dest dead scratch a)
    (same : agrees dest b a) : Space w n s bins dest dead scratch b :=
  { p with dense := by rw [same _ (low s.acceptedBefore p.acceptedBefore)];exact p.dense }

theorem target_transfer {a b : Memory w} (space : Space w n s bins dest dead scratch a)
    (same : agrees dest b a) (f : Fin 9) (q : Fin n) :
    target s bins dest dead f.val b q=target s bins dest dead f.val a q := by
  simp only [target,same _ (low _ space.choice),same _ (low _ space.amount),
    same _ (low _ space.acceptedBefore)]

def records (w n : ℕ) (s : Inputs) (z bins dest dead scratch : ℕ) : List (Fin 9) → Procedure w
  | [] => scan w scratch 0 (.lit 0)
  | f::fs => (pass w n s z bins dest dead scratch f).seq (records w n s z bins dest dead scratch fs)

def result (n : ℕ) (s : Inputs) (z bins dest dead scratch : ℕ) :
    List (Fin 9) → Memory w → Memory w
  | [],m => m
  | f::fs,m => result n s z bins dest dead scratch fs (writes (n:=n) s z bins dest dead scratch f m)

def ticks (n : ℕ) (s : Inputs) (z bins dest dead : ℕ) : List (Fin 9) → ℕ
  | [] => 4
  | f::fs => time n s z bins dest dead f+ticks n s z bins dest dead fs

theorem records_exec (fs : List (Fin 9)) (m : Memory w) (space : Space w n s bins dest dead scratch m) :
    (records w n s z bins dest dead scratch fs).Exec m (result n s z bins dest dead scratch fs m)
      (ticks n s z bins dest dead fs) := by
  induction fs generalizing m with
  | nil =>
    have end_ := space.end_
    have empty : ProtocolRAM.image scratch 0 (.lit 0) m = m := by
      exact fillSegment_zero _ _ _
    intro P R K machine pc reg pub exit installed vals cfg mem entry same
    have step := @scan_exec w scratch 0 (.lit 0) m trivial (by omega)
      P R K machine pc reg pub exit installed vals cfg mem entry same
    simpa only [records,result,ticks,empty,Nat.zero_mul,Nat.add_zero] using step
  | cons f fs ih =>
    exact Procedure.Exec.then (execute m space f) (ih _ (transfer space (pass_agrees m space f)))

theorem records_frame (fs : List (Fin 9)) (m : Memory w) (space : Space w n s bins dest dead scratch m)
    (x : ℕ) (outside : x < scratch ∨ scratch+2*n≤x)
    (miss : ∀f∈fs,∀q : Fin n,x≠target s bins dest dead f.val m q) :
    result n s z bins dest dead scratch fs m x=m x := by
  induction fs generalizing m with
  | nil => rfl
  | cons f fs ih =>
    have same := pass_agrees (z:=z) m space f
    exact (ih _ (transfer space same) (fun j hj q=>by
      rw [target_transfer space same];exact miss j (List.mem_cons_of_mem _ hj) q)).trans
      (keeps s z bins dest dead scratch f m x (miss f List.mem_cons_self) outside)

/-- The same compacted pair gets all nine fields at the common ordinal. Other
fields and other live units have disjoint addresses, including inside one item. -/
theorem records_stored (fs : List (Fin 9)) (nodup : fs.Nodup) (m : Memory w)
    (space : Space w n s bins dest dead scratch m) (f : Fin 9) (inList : f∈fs)
    (q : Fin n) (chosen : (m s.choice).val < bins) (small : q.val < (m s.amount).val) :
    result n s z bins dest dead scratch fs m (dest+9*((m s.acceptedBefore).val+q.val)+f.val)=
      (field s z f).eval m (q.val:Word w) := by
  induction fs generalizing m with
  | nil => cases inList
  | cons g gs ih =>
    let m₁ := writes (n:=n) s z bins dest dead scratch g m
    have same : agrees dest m₁ m := pass_agrees m space g
    have next := transfer space same
    have ord := same _ (low _ space.acceptedBefore)
    rcases List.mem_cons.mp inList with eqn|later
    · subst g
      have hd := space.dense
      have pad := space.padding
      have qn := q.isLt
      have fn := f.isLt
      have frame := records_frame (z:=z) gs m₁ next (dest+9*((m s.acceptedBefore).val+q.val)+f.val)
        (.inl (by omega)) (by
          intro j member i
          have diff : f.val≠j.val := by
            intro d
            exact nodup.notMem (by rwa [show f=j from Fin.ext d])
          have jn := j.isLt
          rw [target_transfer space same]
          unfold target
          split <;> omega)
      exact frame.trans (stored space f q chosen small)
    · have ca := same _ (low _ space.choice)
      have am := same _ (low _ space.amount)
      have ready := ih nodup.tail m₁ next later (by simpa [ca] using chosen) (by simpa [am] using small)
      rw [ord] at ready
      exact ready.trans (eval_below _ _ m m₁ (fits (z:=z) (bins:=bins) (dead:=dead) space.toEarly f).2 same)

theorem nine_fields (m : Memory w) (space : Space w n s bins dest dead scratch m) (f : Fin 9)
    (q : Fin n) (chosen : (m s.choice).val < bins) (small : q.val < (m s.amount).val) :
    result n s z bins dest dead scratch (List.finRange 9) m (dest+9*((m s.acceptedBefore).val+q.val)+f.val)=
      (field s z f).eval m (q.val:Word w) :=
  records_stored (List.finRange 9) (List.nodup_finRange _) m space f (List.mem_finRange _) q chosen small

end Hierarchy.DescentPacking.PairRAM

end OAI
