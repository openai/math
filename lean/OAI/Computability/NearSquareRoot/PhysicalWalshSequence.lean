import OAI.Computability.IntegerMultiplication.Code.Iter
import OAI.Computability.NearSquareRoot.BoundedProduct
import OAI.Computability.NearSquareRoot.PhysicalWalshAgendaOps
import OAI.Computability.IntegerMultiplication.Code.Fold
import Mathlib.Algebra.BigOperators.Intervals

/-! # Running consecutive variable-cost pieces on one ordered stream

The command tests the physical agenda for the empty-list constructor. At a
cons it calls the same header-driven piece program, retains the remaining
headers, and tail-calls its own dispatcher. The integral clock sums the
individual piece costs. One arena holds the stream and the outstanding agenda.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Sequence

open IntegerMultiplication Code Space

variable {I H D : Type} [Codec H] [Codec D]

private def prepare (p : (H × List H) × D) := ((p.1.1,p.2),p.1.2)
private def finish (p : (H × D) × List H) := (p.2,p.1.2)
private theorem easy_prepare : Easy (prepare (H:=H) (D:=D)) := by unfold prepare; fun_prop
private theorem easy_finish : Easy (finish (H:=H) (D:=D)) := by unfold finish; fun_prop

private def body (c : Cmd) : Cmd := splitRoot 0 (fun _ => .pass) (splitRoot 0 (fun _ => .pass)
    ((pack 0).join ((pack 0).join (c.join (.again 0)))))

private noncomputable def frame (H D : Type) [Codec H] [Codec D] (step : Cmd) : Cmd :=
  (((easy_prepare (H:=H) (D:=D)).choose).join (KernelEffectiveFamily.leftCmd step)).join
    (easy_finish (H:=H) (D:=D)).choose

/-- The loop skeleton parks the unused agenda while the named piece runs. -/
noncomputable def walkCmd (H D : Type) [Codec H] [Codec D] (step : Cmd) : Cmd :=
  (body (frame H D step)).tie

theorem size_drop (l : List H) (j : ℕ) : size (l.drop j) ≤ size l := by
  have h := size_append_right (l.take j) (l.drop j)
  rw [List.take_append_drop] at h
  have hpos := size_pos (l.take j)
  omega

/-- Chronological transfer for a generated finite agenda. The entry state and
result at index `j` may satisfy arbitrary numeric guards at each actual call. -/
theorem walkWith {step : Cmd} (hs : I → List H) (v : I → ℕ → D) (cost : I → ℕ → ℕ) (arena : I → ℕ)
    (room : ∀ i j, j ≤ (hs i).length → size (v i j) ≤ arena i)
    (piece : EffectiveBoundedTask.Runs step (fun z : (i : I) × Fin (hs i).length => cost z.1 z.2)
      (fun z => arena z.1) (fun z => send ((hs z.1).get z.2,v z.1 z.2))
      (fun z => send ((hs z.1).get z.2,v z.1 (z.2.val+1)))) :
    let G i := size (hs i)+arena i
    EffectiveBoundedTask.Runs (walkCmd H D step) (fun i => (G i+1) + ∑ j ∈ Finset.range (hs i).length, (cost i j+G i+1)) G
      (fun i => send (hs i,v i 0)) (fun i => send (v i (hs i).length)) := by
  intro G
  let X := (i : I) × Fin (hs i).length
  let head (z : X) := (hs z.1).get z.2
  let tail (z : X) := (hs z.1).drop (z.2.val+1)
  let p (z : X) := ((head z,tail z),v z.1 z.2)
  let q (z : X) := ((head z,v z.1 (z.2.val+1)),tail z)
  have hop := AgendaOps.compose (AgendaOps.compose (AgendaOps.easy easy_prepare p)
    (AgendaOps.left piece (fun z => send (tail z)))) (AgendaOps.easy easy_finish q)
  have remainingSize (z : X) : size (head z)+size (tail z)+1 ≤ size (hs z.1) := by
    have h := size_drop (hs z.1) z.2
    rwa [List.drop_eq_getElem_cons z.2.isLt,size_cons] at h
  let c := frame H D step
  have core : EffectiveBoundedTask.Runs c (fun z : X => cost z.1 z.2+G z.1) (fun z => G z.1)
      (fun z => send (p z)) (fun z => send (tail z,v z.1 (z.2.val+1))) := by
    apply hop.bound 8 8 <;> intro z
    all_goals
      have pairSize := remainingSize z
      have v0 := room z.1 z.2 z.2.isLt.le
      have v1 := room z.1 (z.2.val+1) z.2.isLt
      have h0 : size (p z) ≤ G z.1 + 2 := by
        simp only [p,size_prod,G]; omega
      have h1 : size (q z) ≤ G z.1 + 2 := by
        simp only [q,size_prod,G]; omega
    · change size (p z)+cost z.1 z.2+size (q z)+1 ≤ _
      omega
    · change max (max (size (p z)+size (p z)) (arena z.1+size (tail z)))
          (size (q z)+size (q z))+1 ≤ _
      dsimp only [G] at h0 h1 ⊢
      omega
  obtain ⟨C,hc⟩ := core
  let B := C+32
  let dep i := B*(G i+1)
  let weight i j := cost i j+G i+1
  let clock i j := G i+1+∑ n ∈ Finset.Ico j (hs i).length, weight i n
  have aux (i : I) (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
      ∀ j, j ≤ (hs i).length → BoundedFits (body c :: env) (body c)
        (pile 0 (send ((hs i).drop j,v i j)) r) (pile 0 (send (v i (hs i).length)) r)
        (B*clock i j) (base+dep i) (dep i) := by
    intro j hj
    induction hj using Nat.decreasingInduction with
    | self =>
      let n := (hs i).length
      have hG : size (v i n) ≤ G i := (room i n le_rfl).trans (Nat.le_add_left ..)
      have spare : G i+3 ≤ dep i := by dsimp only [dep,B]; rw [Nat.add_mul]; omega
      have hc0 : DeckCap (base+dep i) (pile 0 (send (([] : List H),v i n)) r) :=
        (hr.pile 0 _).mono (by change base+size (([] : List H), v i n) ≤ _; simp only [size_prod,size_nil]; omega)
      have hbit := BoundedFits.bit (env:=body c :: env) (c:=fun _ => .pass) (d:=(pack 0).join ((pack 0).join (c.join (.again 0))))
          (b:=false) (BoundedFits.pass (hr.pile 0 _ |>.mono (show base+size (v i n) ≤ base+dep i by omega)))
          hc0.exposeFork (by omega : 1 ≤ dep i)
      have hbase := BoundedFits.pair (c:=fun _ => .pass) hbit hc0 (by omega)
      simp only [List.drop_length,clock,Finset.Ico_self,Finset.sum_empty,Nat.add_zero]
      exact hbase.mono (by dsimp only [B]; rw [Nat.add_mul]; omega) le_rfl le_rfl
    | of_succ j hj ih =>
      let z : X := ⟨i,⟨j,hj⟩⟩
      have hcore := hc z (body c :: env) r base hr
      have reserve : C*(G i+1)+1 ≤ dep i := by dsimp only [dep,B]; rw [Nat.add_mul]; omega
      have hcore' := hcore.mono le_rfl (Nat.add_le_add_left (Nat.le_of_lt reserve) base) le_rfl
      have hjoin := hcore'.join ih.again0 reserve
      obtain ⟨_,_,run⟩ := hcore
      have H : DeckCap (base+dep i) (pile 0 (send (p z)) r) :=
        (show DeckCap _ _ from run.start).mono (Nat.add_le_add_left (Nat.le_of_lt reserve) base)
      have ret₁ := (BoundedFits.pack _ _ r 0 _ (depth:=0) H).join hjoin (by omega)
      have ret₂ := (BoundedFits.pack _ _ _ 0 _ (depth:=0) H.exposeFork).join ret₁ (by omega)
      have nested := BoundedFits.pair (c:=fun _ => .pass) ret₂ H.exposeFork (by omega)
      have res := BoundedFits.pair (c:=fun _ => .pass) nested H (by omega)
      have clockStep : clock i j = clock i (j+1)+weight i j := by
        simp only [clock,Finset.sum_eq_sum_Ico_succ_bot hj (weight i)]; omega
      rw [List.drop_eq_getElem_cons hj]
      apply res.mono _ le_rfl le_rfl
      change 1+(1+(C*(cost i j+G i+1)+(B*clock i (j+1)+1)+2)+2)+2+4+4 ≤ _
      rw [clockStep]
      conv_rhs => rw [Nat.mul_add]
      dsimp only [weight,B]
      rw [Nat.add_mul C 32 (cost i j+G i+1)]
      omega
  refine ⟨B,fun i env r b hb => ?_⟩
  have run := (aux i env r b hb 0 (Nat.zero_le _)).tie
  simp only [List.drop_zero,clock,Nat.Ico_zero_eq_range] at run
  exact run.mono (by dsimp only [weight,B]; conv_rhs => rw [Nat.mul_add,Nat.mul_one]
                     omega) le_rfl le_rfl

theorem walk (hs : I → List H) (v : I → ℕ → D) (cost : I → ℕ → ℕ) (arena : I → ℕ)
    (room : ∀ i j, j ≤ (hs i).length → size (v i j) ≤ arena i)
    (piece : BoundedTask (fun z : (i : I) × Fin (hs i).length => cost z.1 z.2)
      (fun z => arena z.1) (fun z => send ((hs z.1).get z.2,v z.1 z.2))
      (fun z => send ((hs z.1).get z.2,v z.1 (z.2.val+1)))) :
    let G i := size (hs i)+arena i
    BoundedTask (fun i => (G i+1) + ∑ j ∈ Finset.range (hs i).length, (cost i j+G i+1)) G
      (fun i => send (hs i,v i 0)) (fun i => send (v i (hs i).length)) := by
  obtain ⟨step,h⟩ := piece
  exact (walkWith (step:=step) hs v cost arena room h).task

open CommonRegisters GeneratorSyntax

theorem walkCmd_effective (H D : Type) [Codec H] [Codec D] {P : Type} [Primcodable P]
    {step : P → Cmd} (h : Effective ltr step) : Effective ltr (fun p => walkCmd H D (step p)) := by
  have f : Effective ltr (fun p => frame H D (step p)) :=
    ((effective_const _ _).join (KernelEffectiveFamily.effective_left h)).join (effective_const _ _)
  apply Effective.tie
  apply KernelEffectiveFamily.effective_splitRoot _ (fun _ => effective_const _ _)
  apply KernelEffectiveFamily.effective_splitRoot _ (fun _ => effective_const _ _)
  exact (effective_const _ _).join ((effective_const _ _).join (f.join (effective_const _ _)))

/-- Fixed framing commands use a single register ceiling, independently of
the number of pieces and the supplied child code. -/
theorem walkCmd_within (H D : Type) [Codec H] [Codec D] (r : ℕ) :
    ∃ R, 0<R ∧ ∀ step : Cmd, Within r step → Within R (walkCmd H D step) := by
  obtain ⟨R,⟨⟨pos,p⟩,q⟩,le⟩ := (((Filter.eventually_gt_atTop (0:ℕ)).and
    (RegisterSelect.within_eventually (easy_prepare (H:=H) (D:=D)).choose)).and
    (RegisterSelect.within_eventually (easy_finish (H:=H) (D:=D)).choose) |>.and
    (Filter.eventually_ge_atTop r)).exists
  refine ⟨R,pos,fun step hs => ?_⟩
  have stepOk := KernelEffectiveFamily.within_left pos (RegisterSelect.within_mono le _ hs)
  have inner : Within R (frame H D step) := ⟨⟨p,stepOk⟩,q⟩
  simp [walkCmd,body,RegisterWitness.splitRoot_within,Within,pack,inner,pos]

end PhysicalWalsh.Sequence

end NearSquareRoot
end Computability
end OAI
