/-
Statement pin for the headline theorems and the axiom ledger (`scripts/audit.sh`, check (d)).

Starting from the roots below — the headline theorems of §1 (v1.0 and v1.1), the other v1.1 results
(Corollaries 4.11 and 5.3), and every ledger axiom — this script collects every declaration of the
`PositivityRigidity` modules that their statements unfold to: the types of the roots, and the transitive
closure through the types and bodies of definitions and the constructors of structures and inductives
(theorems other than the roots are not followed: a proof cannot change the meaning of a statement;
declarations of Mathlib / Zeta23 are pinned by `lake-manifest.json`).  For each declaration, sorted by name,
it prints its kind, name, universe parameters, type and (for definitions) body, pretty-printed with the
options fixed below (docstrings are not printed), and a structural hash of the type and body expressions,
which also catches differences the pretty-printer hides (coercions, implicit arguments).

The expected output is `scripts/Statements.baseline.txt`; `scripts/audit.sh` requires an exact match, so any
change to the meaning of a headline theorem or of a ledger axiom fails the audit.  A deliberate change must
regenerate the baseline:
  lake env lean scripts/Statements.lean > scripts/Statements.baseline.txt
Run (after `lake build`):  lake env lean scripts/Statements.lean
-/
import PositivityRigidity

open Lean Elab Command Meta

set_option pp.fullNames true
set_option pp.unicode.fun true
set_option format.width 110
set_option pp.numericTypes true
set_option pp.proofs false
set_option pp.funBinderTypes true
set_option pp.structureInstances true
set_option pp.fieldNotation false

namespace StatementsPin

/-- The headline theorems and the other v1.1 results whose statements are pinned. -/
def theoremRoots : List Name :=
  [``PosRig.theoremA, ``PosRig.logic_display, ``PosRig.conjS_equivalences, ``PosRig.theoremB',
   ``PosRig.corollary_magic, ``PosRig.theoremC, ``PosRig.theoremD', ``PosRig.theoremB_a,
   ``PosRig.theoremB_b, ``PosRig.corollary_magic_a, ``PosRig.theoremD_nonstrict',
   ``PosRig.certificate_route, ``PosRig.near_rigidity, ``PosRig.near_rigidity_interval]

/-- Every axiom declared in `PositivityRigidity.Ledger`. -/
def ledgerAxioms (env : Environment) : List Name := Id.run do
  let mods := env.header.moduleNames
  let mut out : Array Name := #[]
  for i in [0:mods.size] do
    if mods[i]! == `PositivityRigidity.Ledger then
      for n in env.header.moduleData[i]!.constNames do
        if let some (.axiomInfo _) := env.find? n then out := out.push n
  return (out.qsort (·.toString < ·.toString)).toList

/-- Is `n` declared in a module of this project (`PositivityRigidity.*`)? -/
def isOurs (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (`PositivityRigidity).isPrefixOf env.header.moduleNames[i.toNat]!
  | none => false

/-- The declaration that carries the meaning of `n` (constructors and recursors → their inductive). -/
def owner (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.ctorInfo v) => v.induct
  | some (.recInfo v) => v.all.headD n
  | _ => n

/-- The constants a declaration's meaning depends on (theorems and axioms: their type only). -/
def deps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.axiomInfo v) => v.type.getUsedConstants
  | some (.thmInfo v) => v.type.getUsedConstants
  | some (.inductInfo v) => v.ctors.foldl (init := v.type.getUsedConstants) fun acc c =>
      match env.find? c with
      | some ci => acc ++ ci.type.getUsedConstants
      | none => acc
  | _ => #[]

def closure (env : Environment) (roots : List Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut worklist : Array Name := roots.toArray
  let mut out : Array Name := #[]
  while !worklist.isEmpty do
    let n := owner env worklist.back!
    worklist := worklist.pop
    if seen.contains n || !isOurs env n then continue
    seen := seen.insert n
    -- theorems are followed only if they are roots
    if let some (.thmInfo _) := env.find? n then
      unless roots.contains n do continue
    out := out.push n
    worklist := worklist ++ deps env n
  return out.qsort (·.toString < ·.toString)

def kindOf (env : Environment) : ConstantInfo → String
  | .inductInfo v => if isStructure env v.name then "structure" else "inductive"
  | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quot"

end StatementsPin

open StatementsPin in
run_cmd liftTermElabM do
  let env ← getEnv
  for r in theoremRoots do
    unless env.contains r do throwError "root {r} not found"
  let axs := ledgerAxioms env
  let roots := theoremRoots ++ axs
  let names := closure env roots
  IO.println s!"== statement pin: {names.size} declarations (closure of {theoremRoots.length} theorems and {axs.length} ledger axioms) =="
  for n in names do
    let some ci := env.find? n | continue
    let us := if ci.levelParams.isEmpty then "" else s!".\{{", ".intercalate (ci.levelParams.map toString)}}"
    IO.println ""
    IO.println s!"{kindOf env ci} {n}{us}"
    IO.println s!"  : {← ppExpr ci.type}"
    let mut h : UInt64 := ci.type.hash
    match ci with
    | .defnInfo v =>
      IO.println s!"  := {← ppExpr v.value}"
      h := mixHash h v.value.hash
    | .opaqueInfo v =>
      IO.println s!"  := {← ppExpr v.value}"
      h := mixHash h v.value.hash
    | .inductInfo v =>
      for c in v.ctors do
        let some cc := env.find? c | continue
        IO.println s!"  | {c} : {← ppExpr cc.type}"
        h := mixHash h cc.type.hash
    | _ => pure ()
    IO.println s!"  hash {h}"
