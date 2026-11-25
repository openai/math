import OAI.Hierarchy.DescentTerminalHeaderDraft

namespace OAI
/-! # Fitting the paid-row scanner from its actual prior socket pages and allocated row-plan bands -/
namespace Hierarchy.DescentTerminalHeaderDraft
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalRowArena DescentTerminalPaidHeaderEvents
open DescentTerminalHeaderSockets
variable {w b:ℕ} {L:DescentTerminalHeaderSockets.Layout}
private theorem repeats {x:Expr} (hx:x.Fits w b) (n:ℕ) : (times x n).Fits w b := by
  induction n with
  | zero=>trivial
  | succ n ih=>exact ⟨ih,hx⟩
private theorem off {x:Expr} (hx:x.Fits w b) (D j:ℕ) : (offset x D j).Fits w b := ⟨repeats hx D,trivial⟩
private theorem dirs (roster:L.roster.Fits w b) {x y:Expr} (hx:x.Fits w b) (hy:y.Fits w b)
    {D:ℕ} (ls:List (Fin D)) : (reverse L x y D ls).Fits w b := by
  induction ls with
  | nil=>trivial
  | cons j ls ih=>exact ⟨⟨roster,off hy D j.val⟩,hx,⟨off hy D j.val,trivial⟩,ih⟩
private theorem canon {x:Expr} (hx:x.Fits w b) (roster:L.roster.Fits w b) (H D j:ℕ) :
    (canonical L x H D j).Fits w b := by
  have hy:(targetAt L x D j).Fits w b:=⟨roster,off hx D j⟩
  exact ⟨hy,trivial,⟨hy,hx,dirs roster hx hy _,⟨off hx D j,trivial⟩⟩,trivial⟩
private theorem bounds {k:Expr} {B:Bank} (key:k.Fits w b) (fit:B.Fits w b) :
    (starts B k).Fits w b ∧ (ends B k).Fits w b :=
  ⟨⟨key,trivial,trivial,⟨fit,key,trivial⟩⟩,⟨key,trivial,trivial,⟨fit,key,trivial⟩⟩⟩
private theorem sockets {x:Expr} (hx:x.Fits w b) (roster:L.roster.Fits w b)
    (pub:L.publicPrefix.Fits w b) (cable:L.cablePrefix.Fits w b) (H D:ℕ) (j:Fin (D+1)) :
    (head L H D x j).Fits w b ∧ (amount L H D x j).Fits w b := by
  refine Fin.cases ?_ (fun s=>?_) j
  · have hs:(successor x).Fits w b:=⟨hx,trivial⟩
    have e:=bounds hs pub
    exact ⟨e.1,e.2,e.1⟩
  · have e:=bounds (canon hx roster H D s.val) cable
    exact ⟨e.1,e.2,e.1⟩
private theorem decide_ {d:ℕ} (c:Column) {a f:Fin d→Expr} (ha:∀s,(a s).Fits w b) (hf:∀s,(f s).Fits w b)
    (ls:List (Fin d)) (r:Expr) (hr:r.Fits w b) : (choose c a f ls r).Fits w b := by
  induction ls generalizing r with
  | nil=>trivial
  | cons j js ih=>
    refine ⟨hr,ha j,?_,ih _ ⟨hr,ha j⟩⟩
    cases c with
    | active|mode=>trivial
    | source=>exact ⟨hf j,hr⟩

theorem allocate (A:Arena) (D:ℕ) (low:A.Lower w) (word:stop A<2^w)
    (roster:L.roster.Fits w A.start) (cable:L.cablePrefix.Fits w A.start) (pub:L.publicPrefix.Fits w A.start) :
    Room A L D w := by
  have fit:A.finish<2^w:=by unfold stop at word;omega
  have h (k:ℕ) (hk:k<22) : (A.bank k).Fits w A.finish:=A.fits_band fit hk le_rfl
  have owner:(Expr.lookup (inputs A L).owner .row).Fits w A.finish:=⟨h 11 (by decide),trivial⟩
  have both:=sockets owner (A.lower_band roster 22) (A.lower_band pub 22) (A.lower_band cable 22) A.sites D
  exact ⟨low,word,fun c=>⟨⟨h 10 (by decide),trivial⟩,trivial,trivial,
    decide_ c (fun j=>(both j).2) (fun j=>(both j).1) _ _ ⟨h 12 (by decide),trivial⟩⟩⟩
end Hierarchy.DescentTerminalHeaderDraft

end OAI
