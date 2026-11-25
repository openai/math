import OAI.Computability.MultitapeWeakETH.TraceSchedule

/-! # Tables testing the input, frozen epoch and output stages of a common trace -/

namespace OAI.Computability.MultitapeWeakETH.PhysicalBlocks

open scoped Classical
noncomputable section

variable {M : Machine} {n b T : ℕ}
abbrev Memory (M : Machine) (b : ℕ) := (k : Key M) → Value M b k

def readCell (hb : 0 < b) (a : Memory M b) (i : M.Tapes) (z : ℤ) : M.Alphabet :=
  a (some (i,z/b)) (offset hb z)

@[simp] theorem readCell_store (hb : 0 < b) (p : Phase M) (i : M.Tapes) (z : ℤ) :
    readCell hb (store hb p) i z = ((config p).tape i).absolute z := by
  exact congrArg ((config p).tape i).absolute (block_offset hb z)

def Accept (p : Phase M) := stopped p = true ∧ M.accepts (config p).pc = true

theorem accept_of_controller {p q : Phase M} (hb : 0 < b)
    (same : store hb p none = store hb q none) : Accept p → Accept q := by
  have h : (stopped p,(config p).pc,fun i => offset hb ((config p).tape i).pos) =
           (stopped q,(config q).pc,fun i => offset hb ((config q).tape i).pos) := same
  obtain ⟨flag,state,_⟩ := (Prod.mk.inj h).imp_right Prod.mk.inj
  simp only [Accept,flag,state,imp_self]

def InputStep (hb : 0 < b) (j : ℕ) (x : Word n) (a d : Memory M b) : Prop :=
  ∀ k ∈ ioKeys M (leftTape M) (leftStart M n) n b j, d k = insertBits hb j x k (a k)

def EpochStep (hb : 0 < b) (T : ℕ) (base : ℕ → M.Tapes → ℤ)
    (allowed : ℕ → M.Choice → Prop) (j : ℕ) (a d : Memory M b) : Prop :=
  ∃ (p : Phase M) (coins : ℕ → M.Choice), (∀ t, allowed t (coins t)) ∧
    let finish := segment coins (cut T b j) p (cut T b (j+1) - cut T b j)
    Fits (b:=b) (base j) p ∧ Fits (b:=b) (base (j+1)) finish ∧
    (j+1 = epochs T b → Accept finish) ∧
    ∀ k ∈ epochKeys M (base j), store hb p k = a k ∧ store hb finish k = d k

def OutputStep (hb : 0 < b) (j : ℕ) (out : Word n) (a d : Memory M b) : Prop :=
  (∀ k ∈ ioKeys M M.output (M.offset n) n b j, a k = d k) ∧
  ∀ i : Fin n, block b i = j → readCell hb a M.output (M.offset n + i.val) = M.bit (out i)

def testStage (hb : 0 < b) (T : ℕ) (base : ℕ → M.Tapes → ℤ) (allowed : ℕ → M.Choice → Prop)
    (v : Fin (vertices n b T)) (a d : Memory M b) (x out : Word n) : Prop :=
  if v.val < n ⌈/⌉ b then InputStep hb v.val x a d
  else if v.val < n ⌈/⌉ b + epochs T b then EpochStep hb T base allowed (v.val - n ⌈/⌉ b) a d
  else OutputStep hb (v.val - (n ⌈/⌉ b + epochs T b)) out a d

def History (hb : 0 < b) (T : ℕ) (base : ℕ → M.Tapes → ℤ) (allowed : ℕ → M.Choice → Prop)
    (x y out : Word n) : Prop :=
  ∃ mem : ℕ → Memory M b, mem 0 = store hb (.running (initial M (fun _ => false) y)) ∧
    ∀ v : Fin (vertices n b T), testStage hb T base allowed v (mem v.val) (mem (v.val+1)) x out ∧
      ∀ k, k ∉ schedule M n b T base v → mem (v.val+1) k = mem v.val k

private theorem local_test (hb : 0 < b) (base : ℕ → M.Tapes → ℤ) (allowed : ℕ → M.Choice → Prop)
    (v : Fin (vertices n b T)) {a d a' d' : Memory M b} {x out x' out' : Word n}
    (ha : ∀ k ∈ schedule M n b T base v, a k = a' k)
    (hd : ∀ k ∈ schedule M n b T base v, d k = d' k)
    (hx : ∀ i : (traceNetwork M n b T base).localBits (inVertex n b T) v, x i.val = x' i.val)
    (ho : ∀ i : (traceNetwork M n b T base).localBits (outVertex n b T) v, out i.val = out' i.val)
    (test : testStage hb T base allowed v a d x out) : testStage hb T base allowed v a' d' x' out' := by
  by_cases input : v.val < n ⌈/⌉ b
  · simp only [testStage,input,ite_true,InputStep] at test ⊢
    simp only [schedule,input,ite_true] at ha hd
    intro k hk
    rw [← hd k hk,test k hk,ha k hk]
    apply insertBits_congr
    intro i hi
    exact hx ⟨i,⟨⟨v.val,input⟩,hi.symm,Fin.ext rfl⟩⟩
  · by_cases mid : v.val < n ⌈/⌉ b + epochs T b
    · simp only [testStage,input,mid,ite_false,ite_true,EpochStep] at test ⊢
      simp only [schedule,input,mid,ite_false,ite_true] at ha hd
      obtain ⟨p,coins,ok,fits,ends,accept,agree⟩ := test
      exact ⟨p,coins,ok,fits,ends,accept,fun k hk =>
        ⟨((agree k hk).1).trans (ha k hk),((agree k hk).2).trans (hd k hk)⟩⟩
    · simp only [testStage,input,mid,ite_false,OutputStep] at test ⊢
      simp only [schedule,input,mid,ite_false] at ha hd
      refine ⟨fun k hk => (ha k hk).symm.trans ((test.1 k hk).trans (hd k hk)),?_⟩
      intro i hi
      have hk := mem_ioKeys M hb i (M.offset n) M.output
      rw [hi] at hk
      have eq : readCell hb a M.output (M.offset n+i.val) = readCell hb a' M.output (M.offset n+i.val) :=
        congrFun (ha _ hk) _
      have atOutput : ∃ j : Fin (n ⌈/⌉ b), j.val = block b i ∧ outVertex n b T j = v := by
        have hv := v.isLt
        unfold vertices at hv
        refine ⟨⟨_,by omega⟩,hi.symm,Fin.ext ?_⟩
        change n ⌈/⌉ b + epochs T b + (v.val-(n ⌈/⌉ b + epochs T b)) = v.val
        omega
      exact eq.symm.trans ((test.2 i hi).trans (congrArg M.bit (ho ⟨i,atOutput⟩)))

/-- A column chooses the initial background memory. Every other parameter
of the graph is shared by all columns, including the complete wiring. -/
theorem exists_trace_tables (hb : 0 < b) (T : ℕ) (base : ℕ → M.Tapes → ℤ)
    (allowed : ℕ → M.Choice → Prop) :
    ∃ tables : Word n → (traceNetwork M n b T base).Relation, ∀ x y out,
      (traceNetwork M n b T base).Attains (tables y) x out ↔ History hb T base allowed x y out := by
  let keys := schedule M n b T base
  let input := inVertex n b T
  let output := outVertex n b T
  let G := traceNetwork M n b T base
  let stage (v : Fin (vertices n b T)) (before after : (k : ↥(keys v)) → Value M b k.val)
      (ins : G.localBits input v → Bool) (outs : G.localBits output v → Bool) : Prop :=
    ∃ (a d : Memory M b) (x out : Word n), testStage hb T base allowed v a d x out ∧
      (∀ k, a k.val = before k) ∧ (∀ k, d k.val = after k) ∧
      (∀ i, x i.val = ins i) ∧ (∀ i, out i.val = outs i)
  have existence (y : Word n) := TraceNetwork.exists_typed_tables keys (fun _ => widthFactor M*b)
    input output (Value M b) (pack M hb) (store hb (.running (initial M (fun _ => false) y))) stage
  choose R spec using existence
  refine ⟨R,fun x y out => (spec y x out).trans ?_⟩
  constructor
  · rintro ⟨mem,start,stages⟩
    refine ⟨mem,start,fun v => ⟨?_,(stages v).2⟩⟩
    obtain ⟨a,d,row,word,valid,hA,hD,hX,hO⟩ := (stages v).1
    exact local_test hb base allowed v (fun k hk => hA ⟨k,hk⟩) (fun k hk => hD ⟨k,hk⟩) hX hO valid
  · rintro ⟨mem,start,stages⟩
    exact ⟨mem,start,fun v => ⟨⟨mem v.val,mem (v.val+1),x,out,(stages v).1,fun _ => rfl,
      fun _ => rfl,fun _ => rfl,fun _ => rfl⟩,(stages v).2⟩⟩

end
end OAI.Computability.MultitapeWeakETH.PhysicalBlocks
