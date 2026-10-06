/-
Axiom and dependency audit of the library `PositivityRigidity` (run by `scripts/audit.sh`, which checks the
output).  Run (after `lake build`):  lake env lean scripts/Audit.lean

Prints a global scan of every declaration of the `PositivityRigidity.*` modules:
1. the `axiom` declarations, by module: they must all be in `PositivityRigidity.Ledger` (the ledger), and
   their number must equal the count in `LEDGER.md` (checked by `scripts/audit.sh`);
2. every axiom that some declaration depends on, other than `propext`, `Classical.choice`, `Quot.sound` and
   the ledger axioms (must be none; this includes `sorryAx` and `Lean.ofReduceBool` / `Lean.trustCompiler`,
   the axioms behind `native_decide`);
3. the declarations that depend on `sorryAx` (must be none);
4. the headline theorems: each must exist and be a theorem.
-/
import PositivityRigidity

open Lean Elab Command

namespace PosRigAudit

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The headline theorems (§1 of the paper, v1.0 and v1.1) and the other v1.1 results. -/
def headlines : List Name :=
  [``PosRig.theoremA, ``PosRig.logic_display, ``PosRig.conjS_equivalences, ``PosRig.theoremB',
   ``PosRig.corollary_magic, ``PosRig.theoremC, ``PosRig.theoremD', ``PosRig.theoremB_a,
   ``PosRig.theoremB_b, ``PosRig.corollary_magic_a, ``PosRig.theoremD_nonstrict',
   ``PosRig.certificate_route, ``PosRig.near_rigidity, ``PosRig.near_rigidity_interval]

def showNames (l : List Name) : String :=
  if l.isEmpty then "none" else ", ".intercalate (l.map toString)

end PosRigAudit

open PosRigAudit in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut nDecl := 0
  let mut ledger : Array Name := #[]
  let mut outside : Array (Name × Name) := #[]
  for i in [0:mods.size] do
    let m := mods[i]!
    unless (`PositivityRigidity).isPrefixOf m do continue
    for n in env.header.moduleData[i]!.constNames do
      if n.isInternal then continue
      let some ci := env.find? n | continue
      nDecl := nDecl + 1
      if ci matches .axiomInfo _ then
        if m == `PositivityRigidity.Ledger then ledger := ledger.push n
        else outside := outside.push (m, n)
  let ledgerL := (ledger.qsort (·.toString < ·.toString)).toList
  let mut bad : Array (Name × Name) := #[]
  let mut sorryUsers : Array Name := #[]
  for i in [0:mods.size] do
    let m := mods[i]!
    unless (`PositivityRigidity).isPrefixOf m do continue
    for n in env.header.moduleData[i]!.constNames do
      if n.isInternal then continue
      let axs ← collectAxioms n
      for a in axs do
        unless standardAxioms.contains a || ledgerL.contains a do bad := bad.push (n, a)
      if axs.contains ``sorryAx then sorryUsers := sorryUsers.push n
  IO.println "== global scan of the PositivityRigidity.* modules =="
  IO.println s!"declarations scanned (non-internal): {nDecl}"
  IO.println s!"ledger axioms (axiom declarations in PositivityRigidity.Ledger): {ledger.size}"
  for n in ledgerL do IO.println s!"  {n}"
  IO.println s!"axiom declarations outside PositivityRigidity.Ledger: {if outside.isEmpty then "none" else toString outside}"
  IO.println s!"axioms other than propext / Classical.choice / Quot.sound and the ledger axioms (incl. sorryAx, Lean.ofReduceBool = native_decide, Lean.trustCompiler): {if bad.isEmpty then "none" else toString bad}"
  IO.println s!"declarations depending on sorryAx: {if sorryUsers.isEmpty then "none" else toString sorryUsers}"
  IO.println "== headline theorems =="
  for n in headlines do
    match env.find? n with
    | some (.thmInfo _) =>
      let axs ← collectAxioms n
      let nonstd := axs.toList.filter (fun a => !standardAxioms.contains a)
      IO.println s!"headline {n}: theorem; ledger axioms: {showNames nonstd}"
    | some _ => IO.println s!"headline {n}: NOT A THEOREM"
    | none => IO.println s!"headline {n}: MISSING"
