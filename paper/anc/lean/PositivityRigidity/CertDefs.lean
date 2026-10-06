/-
Definitions used to state the computer-assisted certificates of §5 (Theorem 5.1 and Table 1).
-/
import PositivityRigidity.Basic

noncomputable section

open Complex

namespace PosRig

/-- The certified representative of Theorem 5.1:
`F_rep(t) = Ξ(t)² (H(t) + ε e^{−πt²})` with `H(t) = Π_{j < J} (1 + r_j t² + s_j t⁴)`. -/
def Frep {J : ℕ} (r s : Fin J → ℚ) (ε : ℚ) (z : ℂ) : ℂ :=
  Xi z ^ 2 * ((∏ j, (1 + (r j : ℂ) * z ^ 2 + (s j : ℂ) * z ^ 4)) +
    (ε : ℂ) * Complex.exp (-(Real.pi : ℂ) * z ^ 2))

/-- A row of Table 1: `J`, the certified bound `κ_J` (rounded up) and the cushion weight `ε`. -/
structure LadderRow where
  J : ℕ
  kappa : ℚ
  eps : ℚ

/-- Table 1 (the certified ladder), with the printed decimals written as exact rationals:
`κ_J = d.ddddddd · 10^{-e}` is `ddddddd · 10^{-(e+7)}`, `ε = 10^{-e'}`. -/
def kappaLadder : List LadderRow :=
  [⟨20, 20151627 / 10 ^ 69, 1 / 10 ^ 67⟩,
   ⟨23, 11963682 / 10 ^ 87, 1 / 10 ^ 86⟩,
   ⟨24, 52941806 / 10 ^ 98, 1 / 10 ^ 93⟩,
   ⟨30, 77522383 / 10 ^ 139, 1 / 10 ^ 138⟩,
   ⟨35, 99924044 / 10 ^ 184, 1 / 10 ^ 183⟩,
   ⟨40, 93828982 / 10 ^ 227, 1 / 10 ^ 226⟩,
   ⟨50, 18493714 / 10 ^ 318, 1 / 10 ^ 318⟩,
   ⟨60, 10640143 / 10 ^ 424, 1 / 10 ^ 424⟩,
   ⟨100, 11508391 / 10 ^ 913, 1 / 10 ^ 911⟩]

/-- `κ_100 = 1.1508391 · 10^{-906}` (Theorem 5.1). -/
def kappa100 : ℚ := 11508391 / 10 ^ 913

/-- A window of Table 2: an interval `[lo, hi]` (in `t` for the zero side, in `x` with `ξ = ξ_x` for
the prime side), the certified lower bound `m` of `F_80` (resp. `F̂_80`) on it, and the printed mass bound. -/
structure Window where
  lo : ℚ
  hi : ℚ
  m : ℚ
  bound : ℚ

/-- Zero-side windows of Table 2: the gaps `I_k` between the first six positive zero ordinates, shrunk
by `0.1` and rounded inward; `m` from `general/logs/F80_windows.log` (`gap{k}_eta0.1`). -/
def zeroWindows : List Window :=
  [⟨142347251418 / 10 ^ 10, 209220396387 / 10 ^ 10, 1407307 / 10 ^ 14, 275 / 10 ^ 19⟩,
   ⟨211220396388 / 10 ^ 10, 249108575801 / 10 ^ 10, 2032466 / 10 ^ 15, 191 / 10 ^ 18⟩,
   ⟨251108575802 / 10 ^ 10, 303248761258 / 10 ^ 10, 8034813 / 10 ^ 17, 481 / 10 ^ 17⟩,
   ⟨305248761259 / 10 ^ 10, 328350615877 / 10 ^ 10, 1697159 / 10 ^ 17, 228 / 10 ^ 16⟩,
   ⟨330350615878 / 10 ^ 10, 374861781588 / 10 ^ 10, 1621571 / 10 ^ 18, 239 / 10 ^ 15⟩]

/-- Prime-side windows `[ξ_a, ξ_b]` of Table 2; `m` from `F80_windows.log` (`win{a}-{b}`). -/
def primeWindows : List Window :=
  [⟨205 / 100, 295 / 100, 3568896 / 10 ^ 12, 681 / 10 ^ 21⟩,
   ⟨505 / 100, 695 / 100, 3500101 / 10 ^ 17, 694 / 10 ^ 16⟩,
   ⟨705 / 100, 795 / 100, 8932024 / 10 ^ 19, 272 / 10 ^ 14⟩,
   ⟨1005 / 100, 1095 / 100, 4079078 / 10 ^ 21, 595 / 10 ^ 12⟩,
   ⟨1205 / 100, 1295 / 100, 6394993 / 10 ^ 23, 380 / 10 ^ 10⟩,
   ⟨14, 15, 1340778 / 10 ^ 22, 182 / 10 ^ 10⟩]

/-- Prime-side atoms of Table 2 at `ξ_{2.5}` and `ξ_6` (`lo = hi = x`); `m` is the lower end of the
certified enclosure of `F̂_80(ξ_x)` in `F80_windows.log`. -/
def atomWindows : List Window :=
  [⟨5 / 2, 5 / 2, 15866021 / 10 ^ 10, 153 / 10 ^ 23⟩,
   ⟨6, 6, 38125494 / 10 ^ 14, 637 / 10 ^ 20⟩]

end PosRig
