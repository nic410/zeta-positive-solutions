/-
Definitions used to state the computer-assisted certificates of §5: Table 1 (v1.2: the certified exact members
`F_J = Ξ² P_J(t²)` of Proposition 4.5, Theorem 5.1) and the windows of Table 2.
-/
import PositivityRigidity.Basic

noncomputable section

open Complex

namespace PosRig

/-- A row of Table 1 (v1.2): `J`, the certified upper bound `archUp` for `𝒜(F_J)`, the certified lower bound
`intLo` for `∫ F_J`, and the printed bound `κ_J` for `𝒜(F_J)/∫ F_J`, where `F_J = Ξ² P_J(t²)` is the exact member
of Proposition 4.5 (`Ffam J`, `FamilyDefs.lean`). -/
structure ExactRow where
  J : ℕ
  archUp : ℚ
  intLo : ℚ
  kappa : ℚ

/-- Table 1 (v1.2): the certified exact members `J = 10, 60, 61, 110, 111`, with the decimals of the logs
`cone/logs/W_J{J}_x2.log` written as exact rationals: `archUp` is the upper end of the certified interval for
`𝒜(F_J)`, `intLo` the lower end of the certified ball for `∫ F_J = F̂_J(0)` rounded down to 21 decimals, and
`κ_J` the printed bound `κ* ≤ κ_J` (that `κ_J ≥ archUp/intLo` is checked in Lean, `thm_5_1`). -/
def exactMembers : List ExactRow :=
  [⟨10, 421255630298 / 10 ^ 30, 2788432137013103687755 / 10 ^ 21, 15107258 / 10 ^ 26⟩,
   ⟨60, 296693123412 / 10 ^ 428, 2788431831991548482268 / 10 ^ 21, 10640143 / 10 ^ 424⟩,
   ⟨61, 650716403227 / 10 ^ 453, 2788431831933736852610 / 10 ^ 21, 23336286 / 10 ^ 449⟩,
   ⟨110, 557968396331 / 10 ^ 1053, 2788431830827063476513 / 10 ^ 21, 20010115 / 10 ^ 1049⟩,
   ⟨111, 398510732132 / 10 ^ 1071, 2788431830818955391538 / 10 ^ 21, 14291572 / 10 ^ 1067⟩]

/-- `κ_111 = 1.4291572 · 10^{-1060}` (Theorem 5.1, v1.2: the exact member `F₁₁₁`). -/
def kappa111 : ℚ := 14291572 / 10 ^ 1067

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
