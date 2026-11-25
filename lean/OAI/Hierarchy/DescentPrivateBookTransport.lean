import OAI.Hierarchy.DescentResetPrivateDonors
import OAI.Hierarchy.DescentChronologicalBundle

namespace OAI
/-! # Chronological live private reads through real cable cuts and readdressing -/
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentSixParty Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {A B C T U V : Type} (r : Recipe T A) (s : Recipe U B) (t : Recipe V C)

structure WordBook where
  node : r.Node ≃ s.Node
  word : r.UsedWord ≃ s.UsedWord
  length : ∀u,r.arity u=s.arity (node u)
  hit : ∀u (j : Fin (r.arity u)) (w : r.UsedWord), r.operand u j=Sum.inr w.val ↔
    s.operand (node u) (Fin.cast (length u) j)=Sum.inr (word w).val
  publicWord : B→A
  publicHit : ∀u (j : Fin (r.arity u)) (a : B),
    s.operand (node u) (Fin.cast (length u) j)=Sum.inl a → r.operand u j=Sum.inl (publicWord a)

namespace WordBook
def refl : WordBook r r := ⟨Equiv.refl _,Equiv.refl _,fun _=>rfl,fun _ _ _=>Iff.rfl,id,fun _ _ _ h=>h⟩
def trans (a : WordBook r s) (b : WordBook s t) : WordBook r t where
  node:=a.node.trans b.node
  word:=a.word.trans b.word
  length u:=(a.length u).trans (b.length _)
  hit u j w:=(a.hit u j w).trans (b.hit _ _ _)
  publicWord:=a.publicWord ∘ b.publicWord
  publicHit u j t read:=a.publicHit u j _ (b.publicHit _ _ t read)

theorem public_origin (book:WordBook r s) (u:r.Node) (j:Fin (r.arity u)) (a:A)
    (hit:r.operand u j=.inl a) :
    ∃ b,s.operand (book.node u) (j.cast (book.length u))=.inl b ∧ book.publicWord b=a := by
  cases pre:s.operand (book.node u) (j.cast (book.length u)) with
  | inl b=>
    exact ⟨b,rfl,Sum.inl.inj ((book.publicHit u j b pre).symm.trans hit)⟩
  | inr w=>
    let alive:s.UsedWord:=⟨w,⟨book.node u,j.cast (book.length u),pre⟩⟩
    have read:= (book.hit u j (book.word.symm alive)).mpr (by rw [Equiv.apply_symm_apply];exact pre)
    rw [hit] at read
    contradiction

variable {p : ℕ} {width : A→ℕ} {width' : B→ℕ} {recipe : BitRecipe T A width}
    {route : BitRef width→BitRef width'} (hp : 0<p) (sh : Shape p recipe) (f : BlockMap p width width' route)
def rerouted : WordBook ((sh.reroute f).recipe hp) (sh.recipe hp) where
  node:=Equiv.refl _
  word:=rerouteLive hp sh f
  length:=rerouteLen hp sh f
  hit u j w:=by
    let j':=Fin.cast (rerouteLen hp sh f u) j
    have eqn:=reroute_operand hp sh f u j'
    change ((sh.reroute f).recipe hp).operand u j=Sum.inr w.val ↔ (sh.recipe hp).operand u j'=Sum.inr w.val
    rw [show Fin.cast (rerouteLen hp sh f u).symm j'=j by rfl] at eqn
    rw [eqn]
    cases hj : (sh.recipe hp).operand u j' with
    | inl b => simp
    | inr h =>
      constructor <;> intro same <;> exact congrArg Sum.inr (Sum.inr.inj same)
  publicWord:=f.map
  publicHit u j b found:=by
    let j':=Fin.cast (rerouteLen hp sh f u) j
    have eqn:=reroute_operand hp sh f u j'
    rw [show Fin.cast (rerouteLen hp sh f u).symm j'=j by rfl] at eqn
    exact eqn.trans (congrArg (Sum.map f.map id) found)
end WordBook

variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ}
variable {W Y S : MarkedWorld F d P bits} {old : BitDescription W} {mid : BitDescription Y} {last : BitDescription S}
    (hp : 0<p)
def BlockRef.exteriorAt {n:ℕ} (N:Network n P bits) (v:N.Site) (b:BlockRef p (boundaryWidth N v))
    (z:P) (j:ℕ) : Prop :=
  ∃a:Attached N v,a.val=z ∧ b.port=.inr a ∧ b.block=j

def BlockRef.pinPayload {n:ℕ} (N:Network n P bits) (v:N.Site) (b:BlockRef p (boundaryWidth N v)) :
    Option (P×ℕ) := match b.port with | .inl _=>none | .inr a=>some (a.val,b.block)

theorem BlockRef.pinPayload_iff {n:ℕ} (N:Network n P bits) (v:N.Site) (b:BlockRef p (boundaryWidth N v))
    (z:P) (j:ℕ) : b.pinPayload N v=some (z,j) ↔ b.exteriorAt N v z j :=by
  rcases b with ⟨e|a,k,fit⟩
  · simp [pinPayload,exteriorAt]
  · simp [pinPayload,exteriorAt]
    intro _
    constructor
    · intro hz
      subst z
      exact ⟨a.property, Subtype.ext rfl⟩
    · rintro ⟨_, eq⟩
      exact congrArg (fun c : Attached N v => c.val) eq

structure SiteBooks (s : WorldShape p R old) (t : WorldShape p R mid) where
  home : W.graph.Site ≃ Y.graph.Site
  atSite : ∀v,WordBook ((s.sites v).recipe hp) ((t.sites (home v)).recipe hp)

  pinPayload : ∀v (b:BlockRef p (boundaryWidth Y.graph (home v))),
    ((atSite v).publicWord b).pinPayload W.graph v=b.pinPayload Y.graph (home v)

namespace SiteBooks

theorem exterior_iff {hp:0<p} {s:WorldShape p R old} {t:WorldShape p R mid} (x:SiteBooks hp s t)
    (v:W.graph.Site) (b:BlockRef p (boundaryWidth Y.graph (x.home v))) (z:P) (j:ℕ) :
    ((x.atSite v).publicWord b).exteriorAt W.graph v z j ↔ b.exteriorAt Y.graph (x.home v) z j :=by
  rw [←BlockRef.pinPayload_iff,←BlockRef.pinPayload_iff,x.pinPayload]

theorem exterior {hp:0<p} {s:WorldShape p R old} {t:WorldShape p R mid} (x:SiteBooks hp s t)
    (v:W.graph.Site) (b:BlockRef p (boundaryWidth Y.graph (x.home v))) (z:P) (j:ℕ)
    (read:b.exteriorAt Y.graph (x.home v) z j) : ((x.atSite v).publicWord b).exteriorAt W.graph v z j :=
  (exterior_iff (hp:=hp) x v b z j).mpr read

def refl (s : WorldShape p R old) : SiteBooks hp s s := ⟨Equiv.refl _,fun _v=>WordBook.refl _,fun _ _=>rfl⟩
def trans {a : WorldShape p R old} {b : WorldShape p R mid} {c : WorldShape p R last}
    (x : SiteBooks hp a b) (y : SiteBooks hp b c) : SiteBooks hp a c where
  home:=x.home.trans y.home
  atSite v:=WordBook.trans _ _ _ (x.atSite v) (y.atSite (x.home v))
  pinPayload v w:=(x.pinPayload v _).trans (y.pinPayload _ w)
def rename (s : WorldShape p R old) (vs : Equiv.Perm W.graph.Site) (es : Equiv.Perm W.graph.Edge) :
    SiteBooks hp (s.renamed vs es) s :=
  ⟨vs.symm,fun v=>WordBook.rerouted hp (s.sites (vs.symm v)) (namedMap W vs es v),by
    rintro v ⟨e|a,k,fit⟩ <;> rfl⟩

open private pieceRef from OAI.Hierarchy.DescentBundleSplit
def split (s : WorldShape p R old) (m : W.graph.Edge→ℕ) (q : ℕ) (cut : ∀e∈W.core,W.graph.width e=m e*q)
    (pos : 0<q) (unit : p∣q) : SiteBooks hp (s.pieces m q cut hp pos unit) s := by
  have eqn : q=(q/p)*p := (Nat.div_mul_cancel unit).symm
  have ht : 0<q/p := Nat.div_pos (Nat.le_of_dvd pos unit) hp
  refine ⟨Equiv.refl _,fun v=>WordBook.rerouted hp (s.sites v) (pieceMap W.graph W.core m q cut hp ht eqn v),?_⟩
  rintro v ⟨e|a,k,fit⟩
  · change (pieceRef W.graph W.core m q cut hp ht eqn v ⟨.inl e,k,fit⟩).pinPayload _ _=none
    by_cases keep:e.val∈W.core <;> simp [pieceRef,keep,BlockRef.pinPayload]
  · rfl

private theorem follow_split (q : ℕ) (pos : 0<q) (unit : p∣q)
    (m : W.graph.Edge→ℕ) (cut : ∀e∈W.core, W.graph.width e=m e*q)
    (tail : Normalize (W.pieces q m cut)) (h : Normalize.CutsEqual q tail)
    (s : WorldShape p R old) :
    WorldShape.follow hp pos unit (.split W q m cut tail) ⟨rfl, h⟩ s =
      WorldShape.follow hp pos unit tail h (s.pieces m q cut hp pos unit) := by
  unfold WorldShape.follow
  rfl

def appended (q : ℕ) (pos : 0<q) (unit : p∣q) (n : Normalize W) (valid : Normalize.CutsEqual q n)
    (s : WorldShape p R old) (vs : Equiv.Perm n.result.graph.Site) (es : Equiv.Perm n.result.graph.Edge) :
    SiteBooks hp (WorldShape.follow hp pos unit (n.appendNames vs es) ((Normalize.cutsEqual_appendNames ..).2 valid) s)
      (WorldShape.follow hp pos unit n valid s) := by
  induction n with
  | done W=>exact rename hp s vs es
  | merge W H key flag k g next ih=>exact ih valid (s.coalesced key flag k g) vs es
  | named W vs₀ es₀ next ih=>exact ih valid (s.renamed vs₀ es₀) vs es
  | split W q' m cut next ih=>
    obtain ⟨rfl,rest⟩:=valid
    let extended := (Normalize.cutsEqual_appendNames q' next vs es).2 rest
    have step (tail : Normalize _) (h : Normalize.CutsEqual q' tail)
        (a : Normalize.CutsEqual q' (.split W q' m cut tail)) :
        WorldShape.follow hp pos unit (.split W q' m cut tail) a s =
          WorldShape.follow hp pos unit tail h (s.pieces m q' cut hp pos unit) := by
      exact follow_split hp q' pos unit m cut tail h s
    change SiteBooks hp
      (WorldShape.follow hp pos unit (.split W q' m cut (next.appendNames vs es)) _ s)
      (WorldShape.follow hp pos unit (.split W q' m cut next) _ s)
    exact Eq.mpr
      (congrArg₂ (fun x y => SiteBooks hp x y)
        (step (next.appendNames vs es) extended _)
        (step next rest _))
      (ih rest (s.pieces m q' cut hp pos unit) vs es)

end SiteBooks
end
end Hierarchy.DescentBundleHistory

end OAI
