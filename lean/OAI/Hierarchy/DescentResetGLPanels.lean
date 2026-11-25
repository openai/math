import OAI.Hierarchy.DescentGLPackedBlocks
import OAI.Hierarchy.DescentResetPackedOrder

namespace OAI
/-! # Direct reuse of the selected GL bank for the reset's high and low fields -/
namespace Hierarchy.DescentPlainTerminal.Suffix
open DescentSIMDLookup DescentGL DescentColonies DescentIssuedFallbackPanel
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H c m n l h b M w : ℕ}

private theorem grouped_cast {J r N : ℕ} (count : J*r=N) (base : ℕ) (mem : Memory w)
    (value : Fin H→Fin N→Cell b) (pos : 0<M) (nonempty : 0<r)
    (src : ∀p : Row H N (M*r),mem (base+(row H N (M*r) p).val)=((data value p).val:Word w))
    (p : Row H J M) :
    mem (base+(row H J M p).val)=
      ((data (fun v g=>encode b r (fun x=>value v (Fin.cast count (finProdFinEquiv (g,x))))) p).val:Word w) := by
  subst N
  exact regroup_read pos nonempty base mem value src p

theorem grouped_remix (small : c≤h+l) (pitch : M*2^(h+l-c)=2^l) (pos : 0<M)
    (base : ℕ) (X : Fin H→Block (h+l)→Cell b) (L : Layout (h+l)) (mem : Memory w)
    (src : DescentGLPacked.Dense (h:=h) (l:=l) base (fun v z=>X v ((rearrange L).symm z)) mem) :
    ∀p : Row H (2^c) M,mem (base+(row H (2^c) M p).val)=
      ((data (fun v hi=>encode b (2^(h+l-c)) (fun low=>X v ((rearrange L).symm (join small hi low)))) p).val:Word w) := by
  have count : 2^c*2^(h+l-c)=2^(h+l) := by rw [←pow_add,Nat.add_sub_of_le small]
  have packed : ∀p : Row H (2^(h+l)) (M*2^(h+l-c)),mem (base+(row H _ _ p).val)=
      ((data (fun v z=>X v ((rearrange L).symm z)) p).val:Word w) := by
    rw [pitch]
    exact src
  intro p
  have genuine:=grouped_cast count base mem (fun v z=>X v ((rearrange L).symm z)) pos (Nat.two_pow_pos _) packed p
  have rows (i : Block c) (x : Block (h+l-c)) :
      Fin.cast count (finProdFinEquiv (i,x))=join small i x := by
    apply Fin.ext
    change x.val+2^(h+l-c)*i.val=i.val*2^(h+l-c)+x.val
    ac_rfl
  simpa only [rows] using genuine

private theorem data_cast_width {a b r : ℕ} (width : a = b)
    (cells : Fin H → Fin r → Cell a) (p : Row H r M) :
    (data (a := b) (fun v j => Fin.cast (congrArg (2 ^ ·) width) (cells v j)) p).val =
      (data cells p).val := by
  subst b
  rfl

theorem grouped_planes (small : c≤h+l) (pitch : M*2^(h+l-c)=2^l) (pos : 0<M)
    (b : Fin (h+l)→Bank) (L : Layout (h+l)) (mem : Memory w)
    (src : ∀d,DescentGLPacked.Dense (h:=h) (l:=l) (b d).base (fun (_:Fin H) z=>PackedOrder.plane d ((rearrange L).symm z)) mem)
    (out : ℕ) (before : ∀d,(b d).Fits w out) (space : ∀d,H*chunks (2^c) M≤(b d).size) :
    ∀d,DescentPackedZip.Source (.lookup (b d) .row) (fun (_:Fin H) hi=>PackedOrder.panel small L hi d) M mem := by
  intro d
  apply DescentPackedZip.source_column (b d) out (before d) mem _ (space d)
  have rd:=grouped_remix small pitch pos (b d).base (fun (_:Fin H) x=>PackedOrder.plane d x) L mem (src d)
  intro p
  let cells := fun (_ : Fin H) (hi : Block c) =>
    encode 1 (2^(h+l-c)) (fun low => PackedOrder.plane d ((rearrange L).symm (join small hi low)))
  have panel_value : (data (fun (_ : Fin H) hi => PackedOrder.panel small L hi d) p).val =
      (data cells p).val :=
    data_cast_width (Nat.one_mul (2^(h+l-c))) cells p
  rw [panel_value]
  exact rd p

end
end Hierarchy.DescentPlainTerminal.Suffix

end OAI
