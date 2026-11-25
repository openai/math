import OAI.Computability.MultitapeWeakETH.WitnessWalkResult

/-! # Space used on an accepted depth-first traversal -/

namespace OAI.Computability.MultitapeWeakETH.WitnessWalk

open IntegerMultiplication Code

variable {D : Type} (visit : Visit D) (ctx : D)

/-- A successful chronological list of visits, with the actual packets and
coefficient lists. Each visit can only shorten the unread prefix stream. -/
inductive Transcript : Store → List Job → Bits.Word → List Tally → Prop
  | done (tail labels) : Transcript (([],tail),labels) [] tail labels
  | step {job pending bits prior children next names jobs tail labels}
      (call : visit ((ctx,job),bits) = some ((children,next),names))
      (consumed : next.length ≤ bits.length)
      (rest : Transcript ((children ++ pending,next),prior ++ names) jobs tail labels) :
      Transcript ((job::pending,bits),prior) (job::jobs) tail labels

variable {visit ctx}

private theorem sublist_size {A : Type} [Codec A] {xs ys : List A} (h : xs.Sublist ys) : size xs ≤ size ys := by
  induction h with
  | slnil => exact le_rfl
  | cons _ _ ih => rw [size_cons]; omega
  | cons_cons _ _ ih => rw [size_cons,size_cons]; omega

theorem Transcript.pending {s jobs tail labels} (t : Transcript visit ctx s jobs tail labels) :
    s.1.1.Sublist jobs := by
  induction t with
  | done => exact .slnil
  | @step j pending bits prior children next names jobs tail labels _ _ _ ih =>
    exact .cons_cons j ((List.sublist_append_right children pending).trans ih)

theorem Transcript.labels {s jobs tail labels} (t : Transcript visit ctx s jobs tail labels) :
    s.2.Sublist labels := by
  induction t with
  | done => exact List.Sublist.refl _
  | step _ _ _ ih => exact (List.sublist_append_left ..).trans ih

theorem Transcript.run {s jobs tail labels} (t : Transcript visit ctx s jobs tail labels) :
    (advance visit ctx)^[jobs.length] (some s) = some (([],tail),labels) := by
  induction t with
  | done => rfl
  | step call _ _ ih => rw [List.length_cons,Function.iterate_succ_apply,advance_cons,call,Option.map_some]; exact ih

/-- Every intermediate frontier is contained in the jobs still to run. The
complete trace therefore bounds even a cutoff padded beyond its last visit. -/
theorem Transcript.space {s jobs tail labels} (t : Transcript visit ctx s jobs tail labels) :
    ∀ n st, (advance visit ctx)^[n] (some s) = some st →
      size st ≤ size jobs + size s.1.2 + size labels + 2 := by
  induction t with
  | done tail labels =>
    intro n st
    have fixed : (advance visit ctx)^[n] (some (([],tail),labels)) = some (([],tail),labels) := by
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply',ih,advance_done]
    rintro h
    obtain rfl := Option.some.inj (h.symm.trans fixed)
    simp [size_prod]
    omega
  | @step j pending bits prior children next names jobs tail labels call consumed rest ih =>
    intro n st h
    cases n with
    | zero =>
      obtain rfl := Option.some.inj h
      have p := sublist_size (Transcript.pending (Transcript.step call consumed rest))
      have l := sublist_size (Transcript.labels (Transcript.step call consumed rest))
      dsimp only [Prod.fst,Prod.snd] at *
      simp only [size_prod]
      omega
    | succ n =>
      rw [Function.iterate_succ_apply,advance_cons,call,Option.map_some] at h
      have sub := ih n st h
      simp only [Bits.size_word,size_cons] at *
      omega

private theorem size_list_le {A : Type} [Codec A] (xs : List A) (b : ℕ) (room : ∀ x ∈ xs, size x ≤ b) :
    size xs ≤ (b+1)*xs.length+1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have small := room x List.mem_cons_self
    have rest := ih (fun y hy => room y (List.mem_cons_of_mem _ hy))
    rw [size_cons,List.length_cons,Nat.mul_succ]
    omega

/-- Convert the mathematical job, packet and label bounds into the code-tree
space required by the actual interpreter. -/
theorem Transcript.evaluate [Codec D] {jobs init bits tail labels} (t : Transcript visit ctx ((init,bits),[]) jobs tail labels)
    (fuel cap : Tally) (time : jobs.length ≤ fuel.length) (jobSize labelSize : ℕ)
    (bounded : ∀ j ∈ jobs, size j ≤ jobSize) (small : ∀ l ∈ labels, l.length ≤ labelSize)
    (room : (jobSize+1)*jobs.length + 2*bits.length + (2*labelSize+2)*labels.length + 5 ≤ cap.length) :
    evaluate visit (fuel,(ctx,cap),some ((init,bits),[])) = some (tail,labels) := by
  obtain ⟨n,steps,ds,parses,eq⟩ := run_sound jobs.length init bits tail [] labels t.run
  simp only [List.nil_append] at eq
  apply evaluate_complete visit ctx cap fuel (eq.symm ▸ parses) (steps.trans time)
  intro j _ st reached
  have bound := t.space j st reached
  have packed := size_list_le jobs jobSize bounded
  have tags := size_list_le labels (2*labelSize+1) (fun l hl => by rw [size_tally]; have := small l hl; omega)
  rw [show 2*labelSize+1+1 = 2*labelSize+2 by omega] at tags
  simp only [Bits.size_word] at bound
  omega

end OAI.Computability.MultitapeWeakETH.WitnessWalk
