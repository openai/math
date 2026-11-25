import OAI.Computability.IntegerMultiplication.Wave.Ticket

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Wave
open Param Scale Halo Strip Code Dims Cap Loom Staff Brief Carry Echo Well Moira Bureau

variable {I:Type}(n:I→ℕ)(h:∀i,Season (n i))(a:(i:I)→Direction (n i))(u:Bool)
abbrev headS(i:I):=Person (criterion (n i)) u (a i)
abbrev tailS(i:I):=Zone (criterion (n i)) u (a i)
abbrev cover_s (i:I):
    Adopt (T0 n u i) (Moira.land (Moira.land (X0 n a u) (A0 n a)) (Y0 n a u) i):=
  ((routeS (criterion (n i)) u (a i)).view).thenDo (Adopt.rotate _ _ _).back
variable (x:(i:I)→Tri (n i)→Tree)
abbrev emit (i:I)(j:headS n a u i)(k:Fin (L0 n a i))(z:tailS n a u i):Tree:=
  x i (offered (criterion (n i)) u (a i) j k z)
abbrev stripeN := stackRun (T0 n u) x
abbrev beltN := Moira.triple (X0 n a u) (A0 n a) (Y0 n a u) (emit n a u x)
theorem scoreS :
    stripeN n u x=Moira.raw (X0 n a u) (A0 n a) (Y0 n a u) (emit n a u x):= by
  funext i
  unfold Moira.raw stripeN stackRun
  rw [(cover_s n a u i).packet]
  apply congrArg (stripe _)
  funext c
  exact (congrArg (x i) ((cover_s n a u i).cast.symm_apply_apply c)).symm

variable {r:Regime I}(T:Origin n r)(A:Realizes r (fun i=> (a i).val))
variable {p:I→Tree}{f:I→ℝ}
theorem wharf (s:Carries f p (beltN n a u x)): Carries f p (stripeN n u x):= by
  rw [scoreS n a]
  let z:= X0 n a u; let v:=A0 n a; let K:=Y0 n a u
  have R:= Strip.flatten z v (fun i (j:headS n a u i×Fin (L0 n a i))=>stripe (K i) (emit n a u x i j.1 j.2)) s
  exact Strip.flatten (land z v) K (fun i j=> emit n a u x i j.1.1 j.1.2 j.2) R
include h T A
theorem seal0 (x0: Mix n r p (stripeN n u x)):
    Mix n r p (beltN n a u x):= by
  rw [scoreS n a] at x0
  let Q:=chart n h a u T.guide A; let y:=name0 n a T.guide A
  let z:= X0 n a u; let v:=A0 n a; let K:=Y0 n a u; let l:=land z v
  let H:=atlas n h a u
  have R : Figure r (ct l):= by unfold l ct land; simp_rw [Series.count_cart]; exact Q.1.multiplied y
  let m:= emit n a u x
  have E:= Well.division n T (land z v) K (fun i j=>m i j.1.1 j.1.2 j.2) x0 H.up R Q.2
  exact Well.division n T z v (fun i j=>stripe (K i) (m i j.1 j.2)) E H.pair Q.1 y
omit T A
theorem volts (c:ℕ)(q:∀ i a,(x i a).count≤ c*P (n i)):
    close n (stripeN n u x):= by
  refine ⟨c+4,fun i=>?_⟩
  let k:=n i
  have e:= stripe_size (T0 n u i) (x i) (c*P k) (q i)
  rw [Series.total,Cap.card,show Cap.space (criterion _)=load (n i) from (h i).volume] at e
  unfold token ton; norm_cast
  have s:1≤load k:=Nat.pow_pos (by decide); have f:1≤P k:=budget_p _
  exact e.trans (by unfold k at *; nlinarith)
-- typed variant
variable {X:Type}[Codec X](g:(i:I)→Tri (n i)→X) -- ≥1
abbrev SpeakN := stripeN n u (fun i a=>send (g i a))
abbrev Card (i:I)(j:headS n a u i)(k:Fin (L0 n a i)):List X:=
  (Y0 n a u i).tab (fun b=> g i (offered (criterion _) _ _ j k b))
abbrev SpeakS(i:I)(j:headS n a u i):List (List X) :=
  List.ofFn (Card n a u g i j)
abbrev SpeakB :=
  stackRun (X0 n a u) (fun i p=>send (SpeakS n a u g i p))

omit h in
theorem mimic : SpeakB n a u g=beltN n a u (fun i a=>send (g i a)):= by
  funext i
  unfold SpeakB stackRun beltN Moira.triple
  apply congrArg (stripe _)
  funext b
  let G:=Card n a u g i b
  have W (j : Fin (L0 n a i)): stripe (Y0 n a u i) (emit n a u (fun i c=>send (g i c)) i b j)=send (G j):= stripe_eq' ..
  simp_rw [W, stripe_eq']
  change send (List.ofFn G) = send (List.map G (List.finRange _))
  simp [List.finRange,Function.comp_def]
include A T
theorem toB (v: Mix n r p (SpeakN n u g)): Mix n r p (SpeakB n a u g):= by
  rw [mimic]
  exact seal0 n h a u (fun i c=>send (g i c)) T A v
omit A T h
theorem toN(v:Carries f p (SpeakB n a u g)):Carries f p (SpeakN n u g):= by
  rw [mimic] at v
  exact wharf n a u _ v
theorem specs :
    SpeakN n u g=(fun i=>send ((road (criterion (n i)) u).tab (g i))) :=
  funext fun _i=>stripe_eq' ..
end Wave

end IntegerMultiplication
end Computability
end OAI
