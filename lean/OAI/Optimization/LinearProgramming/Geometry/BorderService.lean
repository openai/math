import OAI.Optimization.LinearProgramming.OracleSpec.ReplyDeterminism
import OAI.Optimization.LinearProgramming.OracleSpec.IndexOrder
import OAI.Optimization.LinearProgramming.Geometry.BorderProtocol

/-! The persistent service behind the scalar minor oracle. Its counted trace retains the
physical scalar and address banks across every request, including a restarting one. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open Contract OracleSpec OracleSpec.MinorLog RAM Matrix

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

structure Service (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ) where
  program : Program
  ready : State ℚ
  clock : ℕ
  height : ℕ
  outputBits : ℕ
  restartBudget : ℕ
  serve (us : List (Index D E)) : ∃ rs, Processes (fun u : Index D E => words u.val)
    program clock height outputBits ready us rs ∧ restartCount rs ≤ restartBudget ∧
    ∀ j ≤ rs.length, extension n outputBits (logarithm D E) (rs.take j)

/-- The sealed online theorem chooses the same pair of programs and polynomial constants
uniformly before the matrices are supplied. The initializing execution remains visible. -/
theorem service_of_online (online : OracleSpec.OnlineMinorLogCompression) :
    ∃ init serve : Program, ∃ C k Cr : ℕ, ∀ r s : ℕ, ∀ D : Matrix (Fin r) (Fin (r+s)) ℚ,
      ∀ E : Matrix (Fin s) (Fin (r+s)) ℚ, ∃ S : Service D E,
        S.program=serve ∧ S.clock=C*(r+s+1)^k ∧ S.outputBits=C*(r+s+1)^k ∧
        S.height=C*(((entries D++entries E).map ratBits).sum+1)^k ∧
        S.restartBudget=Cr*(r+s)^2*((2*(r+s)).log2+1) ∧
        call init S.clock S.height (start [r,s,r+s] (entries D++entries E)) S.ready ∧ S.ready.output=some 0 := by
  obtain ⟨init,serve,C,k,Cr,alg⟩ := online
  refine ⟨init,serve,C,k,Cr,?_⟩
  intro r s D E
  obtain ⟨z,initRun,tag,h⟩ := alg r s D E
  exact ⟨⟨serve,z,_,_,_,_,h⟩,rfl,rfl,rfl,rfl,rfl,initRun,tag⟩

/-- Each call starts with the actual preceding state, installs only the short request
in the address bank, and charges for each installed word and every arithmetic instruction. -/
inductive ServiceTrace {ι : Type} (encode : ι → List ℕ) (p : Program) (clock height width : ℕ) :
    State ℚ → List (ι × Option ℚ) → ℕ → State ℚ → Prop where
  | nil (s : State ℚ) : ServiceTrace encode p clock height width s [] 0 s
  | cons {s t z : State ℚ} {u : ι} {ans : Option ℚ} {tail : List (ι × Option ℚ)} {k cost : ℕ}
      (tr : Fin (k+1) → State ℚ) (ticks : (encode u).length+k ≤ clock)
      (run : Trace p (resume s (encode u)) k tr) (last : tr (Fin.last k)=t)
      (bounded : ∀ i j,ratBits ((tr i).data j) ≤ height) (response : emits t ans)
      (small : ∀q,ans=some q → ratBits q ≤ width)
      (rest : ServiceTrace encode p clock height width t tail cost z) :
      ServiceTrace encode p clock height width s ((u,ans)::tail) ((encode u).length+k+cost) z

theorem ServiceTrace.bound {ι : Type} {encode : ι → List ℕ} {p : Program} {clock height width cost : ℕ}
    {s t : State ℚ} {rs : List (ι × Option ℚ)} (run : ServiceTrace encode p clock height width s rs cost t) :
    cost ≤ rs.length*clock := by
  induction run with
  | nil => simp
  | cons tr paid core last bounds ans small rest ih =>
    simp only [List.length_cons,Nat.succ_mul]
    omega

theorem trace_of_processes {ι : Type} {encode : ι → List ℕ} {p : Program} {clock height width : ℕ}
    {s : State ℚ} {qs : List ι} {rs : List (ι × Option ℚ)}
    (run : Processes encode p clock height width s qs rs) :
    ∃ t cost, ServiceTrace encode p clock height width s rs cost t ∧ cost ≤ qs.length*clock := by
  induction run with
  | nil z => exact ⟨z,0,.nil _,by simp⟩
  | cons call lng ans small _ ih =>
    obtain ⟨t,c,rest,hr⟩ := ih
    obtain ⟨k,hk,tr,ex,last,hs⟩ := call
    refine ⟨t,_,.cons tr (by omega) ex last hs ans small rest,?_⟩
    simp only [List.length_cons,Nat.succ_mul]; omega

/-- Installing a request preserves all scalars and the address cells outside its prefix. -/
theorem resume_frame (s : State ℚ) (q : List ℕ) :
    (resume s q).data=s.data ∧ ∀ i, q.length ≤ i → (resume s q).index i=s.index i :=
  ⟨rfl,fun i hi => by simp [resume,List.getElem?_eq_none hi]⟩

namespace Service

noncomputable def events (S : Service D E) (us : List (Index D E)) : List (Index D E × Option ℚ) :=
  (S.serve us).choose

theorem events_spec (S : Service D E) (us : List (Index D E)) :
    Processes (fun u : Index D E => words u.val) S.program S.clock S.height S.outputBits S.ready us (S.events us) ∧
    restartCount (S.events us) ≤ S.restartBudget ∧
    ∀ j ≤ (S.events us).length, extension n S.outputBits (logarithm D E) ((S.events us).take j) := (S.serve us).choose_spec

theorem requests_of_processes {ι : Type} {encode : ι → List ℕ} {p : Program} {c b w : ℕ} {st : State ℚ}
    {us : List ι} {rs : List (ι × Option ℚ)} (h : Processes encode p c b w st us rs) : rs.map Prod.fst=us := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ ih => simp [ih]

@[simp] theorem requests (S : Service D E) (us : List (Index D E)) : (S.events us).map Prod.fst=us :=
  requests_of_processes (S.events_spec us).1

@[simp] theorem events_nil (S : Service D E) : S.events []=[] := by
  exact List.map_eq_nil_iff.mp (S.requests [])

private theorem extract_last {ι : Type} {encode : ι → List ℕ} {p : Program} {c b w : ℕ} (us : List ι)
    (u : ι) (st : State ℚ) (rs : List (ι × Option ℚ)) (proc : Processes encode p c b w st (us++[u]) rs) :
    ∃ ys ans, rs=ys++[(u,ans)] ∧ Processes encode p c b w st us ys ∧ ∀q,ans=some q → ratBits q ≤ w := by
  induction us generalizing st rs with
  | nil =>
    cases proc with
    | cons _ _ ans small tail =>
      cases tail
      exact ⟨[],_,rfl,.nil _,small⟩
  | cons a as ih =>
    cases proc with
    | cons first len tag size tail =>
      obtain ⟨ys,ans,rfl,before,small⟩ := ih _ _ tail
      exact ⟨_::ys,ans,rfl,.cons first len tag size before,small⟩

/-- The returned scalar is uniquely determined by the typed request prefix. -/
noncomputable def next (S : Service D E) (us : List (Index D E)) (u : Index D E) : Option ℚ :=
  (((S.events (us++[u])).getLast?).map Prod.snd).getD none

theorem events_snoc (S : Service D E) (us : List (Index D E)) (u : Index D E) :
    S.events (us++[u])=S.events us++[(u,S.next us u)] ∧ ∀q,S.next us u=some q → ratBits q ≤ S.outputBits := by
  obtain ⟨ys,ans,hys,pre,small⟩ := extract_last us u _ _ (S.events_spec (us++[u])).1
  have eq := pre.replies_unique (S.events_spec us).1
  have last : S.next us u=ans := by simp [next,hys]
  exact ⟨by rw [hys,eq,last],fun _ h => small _ (last ▸ h)⟩

end Service
end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
