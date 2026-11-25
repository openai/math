import OAI.Hierarchy.DescentTerminalEpochFlags

namespace OAI
/-! # Publishing a single rejection word for a complete retained selector history -/

namespace Hierarchy.DescentTerminalEpochFlags
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}

structure EpochRow where
  C : ℕ
  count : ℕ
  codes : Bank
  rom : Bank
  seats : ℕ
  exterior : ℕ
  out : ℕ
  dst : ℕ

def EpochRow.Valid (a : EpochRow) (m : Memory w) : Prop := m a.exterior=0 ∧
  ∀i : Fin a.seats,SeatValid a.C (m a.count).val (m (a.codes.base+i.val)).val i.val

structure Archived (w low : ℕ) (a : EpochRow) : Prop where
  rom : a.rom.Fits w low
  codes : a.codes.Fits w low
  count : (Bank.mk a.count 0).Fits w low
  exterior : a.exterior < low
  letters : alphabet a.C ≤ a.rom.size
  seats : a.seats ≤ a.codes.size

def Spaced (w low terminal previous : ℕ) : List EpochRow → Prop
  | [] => previous < terminal ∧ low ≤ terminal ∧ terminal+1 < 2^w
  | a::ts => low ≤ a.out ∧ previous < a.out ∧ a.out+a.seats+1 ≤ a.dst ∧ a.dst+1 < 2^w ∧
      Spaced w low terminal a.dst ts

def foldProgram (w terminal previous : ℕ) : List EpochRow → Procedure w
  | [] => step w previous previous previous terminal
  | a::ts => (epochProgram w a.C a.count a.codes a.rom a.seats a.out previous a.exterior a.dst).seq
      (foldProgram w terminal a.dst ts)

def foldTime (terminal previous : ℕ) : List EpochRow → ℕ
  | [] => 4+1*(2*(sticky previous previous previous).work+4)
  | a::ts => epochCost a.C a.count a.codes a.rom a.seats a.out previous a.exterior+
      foldTime terminal a.dst ts

theorem foldTime_eq (terminal previous : ℕ) (ts : List EpochRow) :
    foldTime terminal previous ts=64+194*ts.length+126*(ts.map EpochRow.seats).sum := by
  induction ts generalizing previous with
  | nil=>rfl
  | cons a ts ih=>
    rw [foldTime,epochCost_eq,ih]
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega

private theorem upper {b : Bank} {low out : ℕ} (h : b.Fits w low) (ge : low ≤ out) : b.Fits w out :=
  ⟨h.1,h.2.1,h.2.2.trans ge⟩

private theorem valid_frame {a : EpochRow} {low : ℕ} (ar : Archived w low a) {m mid : Memory w}
    (hold : ∀i < low,mid i=m i) : a.Valid mid ↔ a.Valid m := by
  have count : a.count < low := by have := ar.count.2.2; change a.count+1 ≤ low at this; omega
  have codes (i : Fin a.seats) : a.codes.base+i.val < low := by
    have := ar.codes.2.2
    have := i.isLt.trans_le ar.seats
    omega
  simp only [EpochRow.Valid,hold _ ar.exterior,hold _ count,hold _ (codes _)]

private theorem word_one {w : ℕ} (small : 1 < 2^w) : (1:Word w)≠0 := by
  intro eq
  have v := congrArg Fin.val eq
  simp [Nat.mod_eq_of_lt small] at v

/-- All raw candidates, including out-of-range words and nonzero padded seats, are read from
the retained header. No validity condition on the seed word or on any profile word is required. -/
private theorem joined_cheap {A B : Procedure w} {p q : Prop}
    (first : p ∧ CheapCode A) (after : q ∧ CheapCode B) : CheapCode (A.seq B) :=
  @cheap_seq w A B first.2 after.2

private theorem from_input {A : Procedure w} {pre : Memory w → Prop}
    {post : Memory w → Memory w → Prop} {cost : ℕ} {target : Memory w → Prop}
    (run : A.Spec pre post cost) (m : Memory w) (initial : pre m)
    (read : ∀ dst, post m dst → target dst) :
    A.Spec (·=m) (fun _ dst=>target dst) cost := by
  intro P R K machine pc reg pub exit installed data cfg src entry hsrc
  subst src
  obtain ⟨ticks,bound,last,dst,execution,returned,result⟩ :=
    run machine pc reg pub exit installed data cfg m entry initial
  exact ⟨ticks,bound,last,dst,execution,returned,read dst result⟩

theorem fold_run (low terminal previous : ℕ) (ts : List EpochRow)
    (spaces : Spaced w low terminal previous ts) (archive : ∀a∈ts,Archived w low a) (m : Memory w)
    (tables : ∀a∈ts,HasROM a.C a.rom m) :
    (foldProgram w terminal previous ts).Spec (·=m) (fun _ dst =>
      dst terminal=(if m previous=0 ∧ ∀a∈ts,a.Valid m then 0 else 1) ∧ ∀i < low,dst i=m i)
      (foldTime terminal previous ts) ∧ CheapCode (foldProgram w terminal previous ts) := by
  induction ts generalizing previous m with
  | nil=>
    obtain ⟨before,high,room⟩:=spaces
    have fits : (Bank.mk previous 0).Fits w terminal := by
      change 0 < 1 ∧ 1 < 2^w ∧ previous+1 ≤ terminal
      omega
    have s := step_exec previous previous previous terminal m fits fits fits room
    refine ⟨?_,s.2.1⟩
    refine @from_input w (step w previous previous previous terminal) _ _ _ _ s.1 m rfl ?_
    intro dst eq
    subst dst
    exact ⟨by simpa using s.2.2.1,fun i hi=>s.2.2.2 i (by omega)⟩
  | cons a ts ih=>
    obtain ⟨start,old,apart,room,remaining⟩:=spaces
    have ar := archive a (by simp)
    have next := epoch_run a.C a.count a.codes a.rom a.seats a.out previous a.exterior a.dst
      (upper ar.rom start) (upper ar.codes start) (upper ar.count start)
      ar.letters ar.seats ⟨old,ar.exterior.trans_le start⟩ apart room
    let left := fun (mid : Memory w) =>
      mid a.dst=(if m previous=0 ∧ a.Valid m then 0 else 1) ∧ ∀i < low,mid i=m i
    have test : (epochProgram w a.C a.count a.codes a.rom a.seats a.out previous a.exterior a.dst).Spec
        (·=m) (fun _ mid=>left mid) (epochCost a.C a.count a.codes a.rom a.seats a.out previous a.exterior) := by
      let P := epochProgram w a.C a.count a.codes a.rom a.seats a.out previous a.exterior a.dst
      refine @from_input w P _ _ _ _ next.1 m (tables a (by simp)) ?_
      intro mid hm
      refine ⟨?_,fun i hi=>hm.2 i (Or.inl (by omega)) (by omega)⟩
      by_cases valid : m previous=0 ∧ a.Valid m
      · rw [ite_eq_left valid]
        exact hm.1.trans (ite_eq_left valid)
      · rw [ite_eq_right valid]
        exact hm.1.trans (ite_eq_right valid)
    have rest : ∀b∈ts,Archived w low b := fun b hb=>archive b (List.mem_cons_of_mem _ hb)
    have static_ : ∀b∈ts,HasROM b.C b.rom m := fun b hb=>tables b (List.mem_cons_of_mem _ hb)
    let right := fun (mid dst : Memory w) =>
      dst terminal=(if mid a.dst=0 ∧ ∀b∈ts,b.Valid mid then 0 else 1) ∧ ∀i < low,dst i=mid i
    have tail : (foldProgram w terminal a.dst ts).Spec left right (foldTime terminal a.dst ts) := by
      intro P R K machine pc reg pub exit installed data cfg mid entry hmid
      have stored : ∀b∈ts,HasROM b.C b.rom mid := by
        intro b hb i hi
        have ar' := rest b hb
        rw [hmid.2 _ (by have := ar'.rom.2.2; have := hi.trans_le ar'.letters; omega)]
        exact static_ b hb i hi
      exact (ih a.dst remaining rest mid stored).1 machine pc reg pub exit installed data cfg mid entry rfl
    let first := epochProgram w a.C a.count a.codes a.rom a.seats a.out previous a.exterior a.dst
    let after := foldProgram w terminal a.dst ts
    have program : (first.seq after).Spec (·=m) (fun _ dst=>∃ mid,left mid ∧ right mid dst)
        (foldTime terminal previous (a::ts)) :=
      @Procedure.Spec.seq w first after (·=m) left (fun _ mid=>left mid) right
        (epochCost a.C a.count a.codes a.rom a.seats a.out previous a.exterior)
        (foldTime terminal a.dst ts) (@test) (@tail) (fun _ _ h=>h)
    change _ ∧ CheapCode (first.seq after)
    refine ⟨?_, @joined_cheap w first after _ _ next (ih a.dst remaining rest m static_)⟩
    refine @from_input w (first.seq after) _ _ _ _ (@program) m rfl ?_
    rintro dst ⟨mid,hl,hr⟩
    refine ⟨?_,fun i hi=>(hr.2 i hi).trans (hl.2 i hi)⟩
    have other : (∀b∈ts,b.Valid mid) ↔ ∀b∈ts,b.Valid m := by
      constructor <;> intro h b hb
      · exact (valid_frame (rest b hb) hl.2).mp (h b hb)
      · exact (valid_frame (rest b hb) hl.2).mpr (h b hb)
    have one := word_one (w:=w) (by omega)
    rw [hr.1,hl.1]
    simp only [List.forall_mem_cons,other]
    split_ifs <;> simp_all
/-- A single unary zero-scalar request enforces seed validity, all exterior tests,
the bounds on the eight active fields, and every unused selector word. -/
theorem rejection_factor {F : Type*} [Semiring F] (terminal previous : ℕ) (ts : List EpochRow)
    (m o : Memory w) (seedOK : Prop) [Decidable seedOK] (seed : m previous=0 ↔ seedOK)
    (wide : 1 < 2^w) (word : o terminal=if m previous=0 ∧ ∀a∈ts,a.Valid m then 0 else 1) :
    (0:F)^(o terminal).val = if seedOK ∧ ∀a∈ts,a.Valid m then 1 else 0 := by
  rw [word]
  by_cases accepted : m previous=0 ∧ ∀a∈ts,a.Valid m
  · have ok : seedOK ∧ ∀a∈ts,a.Valid m := ⟨seed.mp accepted.1,accepted.2⟩
    rw [ite_eq_left accepted,ite_eq_left ok]
    exact pow_zero _
  · have no : ¬(seedOK ∧ ∀a∈ts,a.Valid m) := fun h => accepted ⟨seed.mpr h.1,h.2⟩
    have one : (1 : Word w).val=1 := Fin.val_cast_of_lt (n:=2^w) wide
    rw [ite_eq_right accepted,ite_eq_right no,one,pow_one]



end
end Hierarchy.DescentTerminalEpochFlags

end OAI
