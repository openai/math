import OAI.Computability.IntegerMultiplication.Morse.Opus
import OAI.Computability.IntegerMultiplication.Code.Children

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Morse
open Net Net.Walsh Strip Loom Adic Dusk Grid Axon Finset Code Bits
noncomputable section
structure Tone where
  t:ℕ
  w:ℕ
  p:ℕ
  q:Word
  b:ℕ→Grain w
  x:Deck 0 t w
  v:p≤w+1
abbrev lone (u:Tone):Order:= ⟨0,u.t,u.w,u.p,u.q,u.b,u.x,u.v⟩
abbrev label(i:Order):Bool:=decide (i.k≠0)
def g_sons:Order→ List Order
| ⟨0,_,_,_,_,_,_,_⟩=>[]
| ⟨k+1,t,w,p,q,b,x,v⟩=> let i : Lute:=⟨k,t,w,p,q,b,x,v⟩; [child i 0,child i 1]
@[simp] theorem desc (i:Lute):g_sons (played i)=[child i 0, child i 1]:= by cases i; rfl
abbrev restS(i:Order):Rows:= bif label i then [] else card i.x
abbrev restT(i:Order):Tree:=send (restS i)


abbrev dispatch i:= Tree.fork (Task.forest ready (g_sons i)) (restT i)

theorem level0 :
    Task (pay ∘ lone) (ready ∘ lone) (dispatch ∘ lone) := by
  let f:brig→List brig×Rows:=fun x=>([],x.2)
  have v:Easy f:=by unfold f; fun_prop
  have s:=v.on (fun i:Tone=>prep (lone i))
  have e i : (dispatch ∘ lone) i = send (f (prep (lone i))) := rfl
  exact (by
    simp_rw [Function.comp_def]; change Task _ _ _
    -- conform
    apply Task.conform (s.bound (b':=pay ∘ lone) 51 (fun i=>by
      change (ready _).count+1≤_
      have e:=(board (lone i)).trans (Nat.mul_le_mul_left 50 (price1 _))
      simp only [Function.comp_apply]; omega))
      (fun _=>rfl) (fun _=>rfl) (fun i=>(e i).symm))
theorem levelN :
    Task (pay ∘ played) (ready ∘ played) (dispatch ∘ played) :=
  delivered.runs.release.conform (fun i=>by change ⌈(pay (played i):ℝ)⌉₊ = pay _; rw [Nat.ceil_natCast])
    (fun _=>rfl) (fun i=>(bills i))

private def waveFlag (i:brig): Bool:=Iter.small (([]:Scroll),i.1)
private theorem flagE:Easy waveFlag:=by unfold waveFlag;have y:=Iter.small_easy (X:=BlockT) (Y:=BlockT); fun_prop
theorem sign(i:Order):
    waveFlag (prep i)=label i:= by unfold waveFlag prep label Iter.small; simp only [List.length_nil,scroll_len]; congr 1; ext; omega
theorem playedSurj (x:Order)(v:label x=true):
    ∃ i:Lute, played i=x := by
  cases x with
  | mk k t w p q b x z=>
    cases k
    · exact (by contradiction : False).elim
    rename_i k
    exact ⟨⟨k,t,w,p,q,b,x,z⟩, rfl⟩
theorem loneSurj (x:Order)(v:label x=false):
    ∃ i:Tone,lone i=x := by
  cases x with
  | mk k t w p q b x z=>
    cases k
    · exact ⟨⟨t,w,p,q,b,x,z⟩,rfl⟩
    exact (by contradiction : False).elim

theorem poster :
    Task pay ready dispatch := by
  let v := fun x=> (waveFlag x,x)
  have e := (flagE.pair Easy.identity).on prep
  have d := e.bound (b':=pay) 51 (fun i=> by
    change (ready _).count+1≤_
    have e:=(board i).trans (Nat.mul_le_mul_left 50 (price1 _)); omega)
  simp_rw [sign] at d
  have k := Task.control (X:=Order) (a:=pay) (f:=ready) (g:=dispatch) label
    (by
      choose f h using loneSurj
      have u:=level0.on (fun i:{i:Order//label i=false}=>f i.1 i.2)
      simpa only [Function.comp_def,h] using u)
    (by
      choose f h using playedSurj
      have u:=levelN.on (fun i:{i:Order//label i=true}=>f i.1 i.2)
      simpa only [Function.comp_def,h] using u)
  exact (d.compose k).bound 2 (by intro i; omega)

abbrev yield_(i:Order):mail:= ((g_sons i).map cure,restS i)
private theorem yields (i) :
    send (yield_ i) = Tree.fork (Task.forest react (g_sons i)) (restT i) := by
  rw [send_prod]; congr 1
  unfold yield_
  rw [← Task.forest_send]
  simp [Task.forest_map]; rfl
private theorem y_zero (i:Tone) :
    post (yield_ (lone i))=cure (lone i) := by
  change card i.x=_
  unfold cure; congr 1; funext v j
  -- prol k=0
  have W : refl_ v=v := by funext t; exact t.elim0
  change i.x v j =i.x (refl_ v) j
  rw [W]

private theorem yellow (i) :
    post (yield_ i)=cure i := by
  cases h:label i
  · obtain ⟨x,rfl⟩:=loneSurj _ h
    exact y_zero x
  obtain ⟨x,rfl⟩:=playedSurj _ h
  unfold yield_ ; simp only [desc,List.map_cons,List.map_nil]
  exact post_L x

theorem child_s (i:Lute)(u:B):pay (child i u)+pay (child i u) = pay (played i):=by
  unfold pay scale_ child played; dsimp only; rw [pow_succ]; ring
theorem child_p (i:Lute)(u:B):pay (child i u)≤pay (played i):= by have :=child_s i u; omega
theorem census (i):
    (Task.forest react (g_sons i)).count ≤ 40*pay i:= by
  cases h:label i
  · obtain ⟨x,rfl⟩:=loneSurj _ h; change 1≤_; have := price2 (lone x); omega
  obtain ⟨x,rfl⟩:=playedSurj _ h
  rw [desc]
  change (react _).count+((react _).count+1+1)+1 ≤_
  have W (u:B): (react (child x u)).count ≤ 16*pay (played x) :=
    (school (child x u)).trans (Nat.mul_le_mul_left _ (le_trans (price1 _) (child_p ..)))
  have k:=price2 (played x); have :=W 0; have :=W 1; omega

theorem caps (i):
    size (yield_ i) ≤ 60*pay i := by
  change (send _).count ≤ _
  rw [yields]; dsimp only [Tree.count]
  have H := census i
  have U : (restT i).count ≤16*pay i := by
    unfold restT restS; cases label i
    · exact (rates i i.x).trans (Nat.mul_le_mul_left _ (price1 i))
    have := price2 i; change 1≤_; omega
  have :=price2 i; omega
theorem after :
    Task pay (fun i=>Tree.fork (Task.forest react (g_sons i)) (restT i)) react :=
  ((post_E.on yield_).bound 61 (fun i=> by have :=caps i; omega)).conform
    (fun _=>rfl) (fun _=> yields _) (fun _=> congrArg send (yellow _))

abbrev song (i:Order):=50*(i.k+1)*pay i
-- slack per children layer minimal
theorem bud (i:Order):
    pay i+pay i+1+(Task.forest react (g_sons i)).count+costSum song (g_sons i) ≤ song i := by
  have u:=price2 i; have g:=census i
  cases h:label i
  · obtain ⟨x,rfl⟩:=loneSurj _ h
    rw [show costSum _ _=0 from rfl]
    unfold song; nlinarith
  obtain ⟨x,rfl⟩:=playedSurj i h
  rw [desc] at g ⊢
  change _+(song (child x 0)+(song (child x 1)+0)) ≤_
  have c0:=child_s x 0
  have c1:=child_s x 1
  unfold song; change _+(50*(x.k+1)*pay _+(50*(x.k+1)*pay _+0)) ≤ 50*(x.k+1+1)*pay _
  nlinarith [congrArg ((x.k+1)*·) c0, congrArg ((x.k+1)*·) c1]

/-- arbitrary single-axis FFT tape engine -/
theorem form : Task song ready react := Task.children g_sons restT poster after bud
theorem money :
    Carries (fun i=> (i.k+1:ℝ)*lease i) ready react := by
  let m (i:Order):ℝ:=(i.k+1:ℝ)*lease i
  have e(i):1 ≤ m i:=one_le_mul_of_one_le_of_one_le (by simp) (price3 i)
  refine ⟨(Sized.natural form).adapts e 51 (fun i=>?_),?_⟩
  · change (song i:ℝ)+1≤ 51 * m i
    unfold song; push_cast; have h:= e i; unfold m lease pay scale_ at *; push_cast at *; nlinarith
  refine ⟨50,fun i=>?_⟩
  have d : ((ready i).count : ℝ) ≤ 50*lease i := by exact_mod_cast ((board i).trans (Nat.mul_le_mul_left 50 (price1 i)))
  rw [Nat.cast_ofNat]
  apply d.trans
  have g:= price3 i
  have z:(0:ℝ)≤ (i.k:ℝ):=by positivity
  change 50*_ ≤ 50*((i.k+1:ℝ)*lease i)
  nlinarith
end
end Morse

end IntegerMultiplication
end Computability
end OAI
