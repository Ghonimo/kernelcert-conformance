/-
  kcheck — the reference checker as an executable.

  Usage: kcheck <input.json> [--diag], where the input is written by the front end
  (checker/front.py): two and-inverter graphs in AIGER literal numbering and the shared
  latch and input pairs. Prints one JSON line with the verdict and one entry per check.
  Exit status: 0 accept, 1 reject, 2 input refused (malformed, or an interface that is
  out of range or not injective). With --diag the line also carries `transCF` and
  `transD1`, Certifaiger's form of the Transition check and the D1-only variant
  (KernelCert/Diag.lean); they do not affect the verdict.

  The verdict is `(runChecks M κ).ok`; `check_sound` proves that `true` implies
  `Safe M` for the circuits built here. Running it trusts the compiler and the front end.
-/
import Lean.Data.Json
import KernelCert

open Lean KernelCert KernelCert.Aig

def natArr (j : Json) : Except String (Array Nat) := do
  (← j.getArr?).mapM fun x => x.getNat?

def pairArr (j : Json) : Except String (Array (Nat × Nat)) := do
  (← j.getArr?).mapM fun x => do
    let a ← natArr x
    if h : a.size = 2 then pure (a[0], a[1]) else throw "expected a pair"

def tripleArr (j : Json) : Except String (Array (Nat × Nat × Nat)) := do
  (← j.getArr?).mapM fun x => do
    let a ← natArr x
    if h : a.size = 3 then pure (a[0], a[1], a[2]) else throw "expected a triple"

def parseGraph (j : Json) : Except String Graph := do
  let nI ← (← j.getObjVal? "nI").getNat?
  let nL ← (← j.getObjVal? "nL").getNat?
  let maxVar ← (← j.getObjVal? "maxVar").getNat?
  let latchNext ← natArr (← j.getObjVal? "latchNext")
  let latchReset ← natArr (← j.getObjVal? "latchReset")
  let ands ← tripleArr (← j.getObjVal? "ands")
  let bad ← natArr (← j.getObjVal? "bad")
  let cons ← natArr (← j.getObjVal? "cons")
  unless latchNext.size = nL ∧ latchReset.size = nL do throw "latch count mismatch"
  unless maxVar ≥ nI + nL do throw "maxVar too small"
  -- every literal must name a variable, and each gate may read only earlier variables
  let litOk (l : Nat) : Bool := l / 2 ≤ maxVar
  unless (latchNext ++ latchReset ++ bad ++ cons).all litOk do throw "literal out of range"
  let mut defined := nI + nL
  for (lhs, r0, r1) in ands do
    unless lhs % 2 = 0 ∧ lhs / 2 ≤ maxVar ∧ lhs / 2 > defined ∧
        r0 / 2 ≤ defined ∧ r1 / 2 ≤ defined do
      throw "gates not in evaluation order"
    defined := lhs / 2
  pure { nI, nL, maxVar, latchNext, latchReset, ands, bad, cons }

def parseInput (j : Json) : Except String (Graph × Graph × Array (Nat × Nat) × Array (Nat × Nat)) := do
  let gm ← parseGraph (← j.getObjVal? "model")
  let gw ← parseGraph (← j.getObjVal? "witness")
  let lp ← pairArr (← j.getObjVal? "latchPairs")
  let ip ← pairArr (← j.getObjVal? "inputPairs")
  pure (gm, gw, lp, ip)

def refuse (reason : String) : IO UInt32 := do
  IO.println (Json.mkObj [("verdict", "refused"), ("reason", reason)]).compress
  pure 2

def main (args : List String) : IO UInt32 := do
  match args with
  | path :: rest =>
    let diag := rest == ["--diag"]
    unless rest.isEmpty || diag do
      IO.eprintln "usage: kcheck <input.json> [--diag]"
      return 2
    let text ← try IO.FS.readFile path catch e => return ← refuse s!"cannot read input: {e}"
    match Json.parse text >>= parseInput with
    | .error e => refuse e
    | .ok (gm, gw, lp, ip) =>
      let M := toCircuit gm
      match mkWitness M (toCircuit gw) lp ip with
      | none => refuse "shared pairs out of range or not injective"
      | some κ =>
        let t0 ← IO.monoMsNow
        let r := runChecks M κ
        let ok := r.ok
        let t1 ← IO.monoMsNow
        IO.println (Json.mkObj (([
          ("verdict", if ok then "accept" else "reject"),
          ("strat", toJson r.strat), ("reset", toJson r.reset), ("trans", toJson r.trans),
          ("prop", toJson r.prop), ("base", toJson r.base), ("step", toJson r.step),
          ("ms", toJson (t1 - t0))] : List (String × Json)) ++
          (if diag then [("transCF", toJson (decide (TransCheckCF κ))),
                         ("transD1", toJson (decide (TransCheckD1 κ)))] else []))).compress
        pure (if ok then 0 else 1)
  | _ =>
    IO.eprintln "usage: kcheck <input.json>"
    pure 2
