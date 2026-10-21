import SUCert.LowP

/-!
`genlow MODE ...`: tests and the certificate generator for the lower-bound checker (untrusted).
-/

open SignUnc.Chk SignUnc.LowData Ival Ival.Ball

def LP : Nat := 128

def unitsOf (num den : Nat) : Nat := (num * 2 ^ LP + den - 1) / den

def cfgL (eps delta m : Nat) : LCfg := ⟨LP, 24, 4, 24, 8, 8, m, eps, delta, 30, 300⟩

/-- Included terms for `y ∈ [ylo, yhi]` with omitted bounds below `tol` each (untrusted heuristic). -/
def lowSpecFor (g : GGroup) (ylo yhi tol : Float) : GSpec :=
  let a := g.an.toFloat / g.ad.toFloat
  let s0 := Float.ofInt g.s0n / g.s0d.toFloat
  let dl := g.dn.toFloat / g.dd.toFloat
  let N := g.cs.length
  let cm := (g.cs.map fun c => (Float.ofInt c.1 / c.2.toFloat).abs).foldl max 0.0
  let D := max (Float.sqrt (Float.log (2.0 * cm / tol) / (3.14159265 * a))) (1.5 / (2.0 * 3.14159265 * a * dl))
  let k1f := Float.ceil ((ylo - D - s0) / dl)
  let k2f := Float.floor ((yhi + D - s0) / dl) + 1.0
  let k1 := if k1f ≤ 0.0 then 0 else min N k1f.toUInt64.toNat
  let k2 := if k2f ≤ 0.0 then 0 else min N k2f.toUInt64.toNat
  let k2 := max k1 k2
  let kFf := Float.ceil ((D - ylo - s0) / dl)
  let kF := if kFf ≤ 0.0 then 0 else min N kFf.toUInt64.toNat
  let csum := (g.cs.map fun c => (Float.ofInt c.1 / c.2.toFloat).abs).foldl (· + ·) 0.0
  let hz := 2.0 / Float.sqrt a * Float.exp (-3.14159265 * ylo * ylo / a) * csum > tol
  ⟨k1, k2, kF, hz⟩

partial def lowerMain (args : List String) : IO Unit := do
  let eps := unitsOf 5 10000000
  let delta := unitsOf 1 1000000
  let m := unitsOf 1 10000
  let c := cfgL eps delta m
  match args with
  | ["lcheck", file] =>
    let lines := (← IO.FS.lines file).filter fun l => !(l.startsWith "FAIL") && !(l.startsWith "stuck") && l.length > 0
    for l in lines do
      let f := (l.splitOn " ").toArray
      if f.size < 11 then continue
      let lo := f[1]!.toInt!
      let M := f[2]!.toNat!
      let N := f[3]!.toNat!
      let sps := (f[4]!.splitOn ";").map fun t =>
        let q := (t.splitOn ",").toArray
        (⟨q[0]!.toNat!, q[1]!.toNat!, q[2]!.toNat!, q[3]! == "1"⟩ : GSpec)
      let ws := (f[5]!.splitOn ",").map fun t => let q := (t.splitOn ":").toArray; (q[0]!.toNat!, q[1]!.toNat!)
      let t0 ← IO.monoMsNow
      let ok := lsegOK c lowGroups lowCos lowP ⟨lo, M, N, sps, ws⟩
      let t1 ← IO.monoMsNow
      IO.println s!"{f[0]!} {ok} {(ws.map (·.2)).foldl (· + ·) 0} {t1 - t0}"
      (← IO.getStdout).flush
  | ["pall"] =>
    let t0 ← IO.monoMsNow
    IO.println s!"pOK {pOK LP 24 4 24 8 lowGroups lowCos lowPsi eps (lowPS.map (·.1)) (lowPS.map (·.2))} ({(← IO.monoMsNow) - t0} ms)"
  | ["p", tes] =>
    let some pgs := prepGroupsV LP 24 lowGroups | IO.println "prep failed"
    let psi := psiPoly LP lowPsi
    let tol := 2.0 ^ (-(tes.toNat!.toFloat))
    IO.println s!"chain {chainOK 0 lowP}"
    for pc in lowP do
      let t0 ← IO.monoMsNow
      let C := pcen LP pc
      let E := peta LP pc
      let lo := pc.1.toFloat / 10000.0
      let hi := pc.2.1.toFloat / 10000.0
      let sps := lowGroups.map fun g => lowSpecFor g lo hi tol
      let loI : Int := ((pc.1 * 2 ^ LP / 10000 : Nat) : Int)
      let hiI : Int := (((pc.2.1 * 2 ^ LP + 9999) / 10000 : Nat) : Int)
      let R := (omitAll LP 24 loI hiI pgs sps).getD 0
      IO.println s!"  specs {repr sps} R {R.toFloat / 2.0 ^ 128.0}"
      match phiJet LP 24 (expB' LP 24) (cosSinTurn LP 24 4) pgs sps lowCos psi C,
          phiJet LP 25 (expH LP 24) (cosSinTurnC LP 24 4) pgs sps lowCos psi ⟨C.m, C.r + E.m.natAbs + E.r⟩ with
      | some T, some T' =>
        let w := pc.2.1 - pc.1
        let S := ((List.zipWith (fun b B => sub b ⟨B, 0⟩) (scaleRat w 20000 T) pc.2.2).map absHi).sum
        let rem := (divNat (20000 ^ 25) (mulInt ((w ^ 25 : Nat) : Int) (absB (T'.getD 25 ⟨0, 0⟩)))).absHi
        let t1 ← IO.monoMsNow
        IO.println s!"piece {pc.1}-{pc.2.1}: S {S.toFloat / 2.0 ^ 128.0} rem {rem.toFloat / 2.0 ^ 128.0} phi(c) {Float.ofInt T.head!.m / 2.0 ^ 128.0} {t1 - t0} ms"
        let rads := (scaleRat w 20000 T).map fun b => b.r.toFloat / 2.0 ^ 128.0
        IO.println s!"    radii b_i: {rads}"
      | _, _ => IO.println "none"
  | ["rho"] =>
    let t0 ← IO.monoMsNow
    IO.println s!"rhoOK {rhoOK LP 30 lowPsi lowP eps delta} ({(← IO.monoMsNow) - t0} ms)"
  | ["tail", ys] =>
    let c' := { c with YT := ys.toNat! }
    IO.println s!"tail {ltailOK c' lowGroups lowCos lowP} J {(jumpsAll LP c'.YT 24 (0, 0, []) lowP + jumpsEnd LP c'.YT 24 lowP).toFloat / 2.0 ^ 128.0}"
  | ["w", yn, yd, Ms, Ns] =>
    let some pgs := prepGroupsV LP 24 lowGroups | IO.println "prep failed"
    let y : Int := (yn.toInt!) * ((2 ^ LP : Nat) : Int) / (yd.toNat! : Int)
    let M := Ms.toNat!
    let N := Ns.toNat!
    let moms := lowP.map (pieceMoms LP M N)
    let t0 ← IO.monoMsNow
    match vJet LP M (expB' LP 24) (cosSinTurn LP 24 4) pgs (fullSpecs lowGroups) lowCos ⟨y, 0⟩,
        phatJet LP 24 4 M N lowP moms (lowP.map pmaxOne) ⟨y, 0⟩ with
    | some V, some H =>
      let t1 ← IO.monoMsNow
      IO.println s!"v {Float.ofInt V.head!.m / 2.0 ^ 128.0} phat {Float.ofInt H.head!.m / 2.0 ^ 128.0} (r {H.head!.r.toFloat / 2.0 ^ 128.0}) W~ {Float.ofInt (2 ^ LP - V.head!.m + H.head!.m) / 2.0 ^ 128.0} {t1 - t0} ms"
    | _, _ => IO.println "none"
  | ["dbg", tn, td, Ds] =>
    let some pgs := prepGroupsV LP 24 lowGroups | IO.println "prep failed"
    let t : Int := (tn.toInt!) * ((2 ^ LP : Nat) : Int) / (td.toNat! : Int)
    let Y : Ball := ⟨t, 0⟩
    let D := Ds.toNat!
    let tf := Float.ofInt t / 2.0 ^ 128.0
    for (G, g) in pgs.zip lowGroups do
      let sp := lowSpecFor g tf tf (2.0 ^ (-70.0))
      let spE : GSpec := ⟨sp.k1, sp.k2, 0, false⟩
      let spF : GSpec := ⟨0, 0, sp.kF, false⟩
      let spH : GSpec := ⟨0, 0, 0, true⟩
      for (nm, s') in [("E", spE), ("F", spF), ("H", spH)] do
        match groupJetT LP D (expB' LP 24) (cosSinTurn LP 24 4) G s' Y with
        | some T => IO.println s!"a={g.an} {nm} {repr s'}: T_D {Float.ofInt (T.getD D ⟨0,0⟩).m / 2.0 ^ 128.0} rad {(T.getD D ⟨0,0⟩).r.toFloat / 2.0 ^ 128.0}"
        | none => IO.println "none"
    match cosJets LP D (cosSinTurn LP 24 4) Y lowCos with
    | some T => IO.println s!"cos: T_D rad {(T.getD D ⟨0,0⟩).r.toFloat / 2.0 ^ 128.0}"
    | none => pure ()
    let ps := padTake (D + 1) (bshift LP Y (psiPoly LP lowPsi))
    IO.println s!"psi: T_D {Float.ofInt (ps.getD D ⟨0,0⟩).m / 2.0 ^ 128.0} rad {(ps.getD D ⟨0,0⟩).r.toFloat / 2.0 ^ 128.0}"
  | ["mkp", Ds, Ls, epsn, epsd, tes, out] =>
    -- greedy pieces from r = 5502/10000 down to 0; coefficients = midpoints of the scaled point jets
    let some pgs := prepGroupsV LP 24 lowGroups | IO.println "prep failed"
    let psi := psiPoly LP lowPsi
    let D := Ds.toNat!
    let L := Ls.toNat!
    let epsU := unitsOf epsn.toNat! epsd.toNat!
    let tol := 2.0 ^ (-(tes.toNat!.toFloat))
    let mut hi : Nat := 5502
    let mut w : Nat := 200
    let mut acc : Array (PPiece × List GSpec) := #[]
    while hi > 0 do
      let ww := min w hi
      let lo := hi - ww
      let sps := lowGroups.map fun g => lowSpecFor g (lo.toFloat / 10000.0) (hi.toFloat / 10000.0) tol
      let C := pcen LP (lo, hi, [])
      match phiJet LP (D + L) (expB' LP 24) (cosSinTurn LP 24 4) pgs sps lowCos psi C with
      | some T =>
        let B := ((scaleRat ww 20000 T).take (D + 1)).map (·.m)
        let pc : PPiece := (lo, hi, B)
        if pieceP_OK' LP 24 4 D L pgs lowCos psi epsU (pc, sps) then
          acc := acc.push (pc, sps)
          IO.println s!"piece {lo}-{hi} ok"
          (← IO.getStdout).flush
          hi := lo
          w := ww + ww / 4
        else
          if ww ≤ 2 then
            IO.println s!"stuck at {hi}"
            return
          w := ww * 3 / 4
      | none => IO.println "none"; return
    let ps := acc.toList.reverse
    let lines := ps.map fun x =>
      s!"  (({x.1.1}, {x.1.2.1}, [" ++ ", ".intercalate (x.1.2.2.map fun b => if b ≥ 0 then s!"({b} : Int)" else s!"(Int.negSucc {(-b - 1).toNat})") ++ "]), [" ++
        ", ".intercalate (x.2.map fun sp => s!"⟨{sp.k1}, {sp.k2}, {sp.kF}, {if sp.hz then "true" else "false"}⟩") ++ "])"
    IO.FS.writeFile out ("def lowPS : List (PPiece × List GSpec) := [\n" ++ ",\n".intercalate lines ++ "\n]\n")
    IO.println s!"{ps.length} pieces written to {out}"
  | ["gen", kfs, kts, lds, Ms, Ns, tes] => lowerMain ["genL", kfs, kts, "1", lds, Ms, Ns, tes, "1024"]
  | ["genL", kfs, kts, lns, lds, Ms, Ns, tes] => lowerMain ["genL", kfs, kts, lns, lds, Ms, Ns, tes, "1024"]
  | ["genL", kfs, kts, lns, lds, Ms, Ns, tes, w0s] =>
    -- y-segments [k/LDEN, (k+1)/LDEN] (the first from ⌊r 2^P⌋), greedy pieces
    let some pgs := prepGroupsV LP 24 lowGroups | IO.println "prep failed"
    let kf := kfs.toNat!
    let kt := kts.toNat!
    let ld := lds.toNat!
    let ln := lns.toNat!
    let M := Ms.toNat!
    let N := Ns.toNat!
    let tol := 2.0 ^ (-(tes.toNat!.toFloat))
    let lor : Int := ((2751 * 2 ^ LP / 5000 : Nat) : Int)
    let base := c.m + (mul LP (mulInt 2 (ofRat LP 2751 5000)) ⟨(c.eps : Int), 0⟩).absHi
    let moms := lowP.map (pieceMoms LP M N)
    let pmax := pmaxHi lowP
    let mut w : Nat := 2 ^ LP / w0s.toNat!
    for kk in [kf:kt] do
      let lo0 : Int := max lor ((kk * ln * 2 ^ LP / ld : Nat) : Int)
      let hi : Int := (((kk + 1) * ln * 2 ^ LP / ld : Nat) : Int)
      if hi ≤ lo0 then continue
      let fl (x : Int) : Float := Float.ofInt x / 2.0 ^ 128.0
      let sps := lowGroups.map fun g => lowSpecFor g (fl lo0) (fl hi) tol
      let t0 ← IO.monoMsNow
      match omitAll LP 24 lo0 hi pgs sps with
      | none => IO.println s!"OMIT-FAIL {kk}"
      | some R =>
        let mut lo := lo0
        let mut runs : Array (Nat × Nat) := #[]
        let mut ok := true
        while lo < hi do
          let rem := (hi - lo).toNat
          let ww := if w ≥ rem then rem else w
          if lowPieceOK LP 24 4 M N 8 pgs sps lowCos lowP moms pmax R base lo ww then
            runs := if runs.size > 0 && runs.back!.1 == ww then runs.pop.push (ww, runs.back!.2 + 1) else runs.push (ww, 1)
            lo := lo + (ww : Int)
            if ww == w then w := min (2 * w) (2 ^ (LP + 3))
          else
            w := ww / 2
            if w < 2 ^ (LP - 44) then
              IO.println s!"stuck at {fl lo} (w {fl ww})"
              ok := false
              break
        if !ok then
          IO.println s!"FAIL {kk}"
          continue
        let t1 ← IO.monoMsNow
        let seg : LSeg := ⟨lo0, M, N, sps, runs.toList⟩
        let okc := lsegOK c lowGroups lowCos lowP seg
        let t2 ← IO.monoMsNow
        let np := (runs.toList.map (·.2)).foldl (· + ·) 0
        let wsStr := ",".intercalate (runs.toList.map fun r => s!"{r.1}:{r.2}")
        let spStr := ";".intercalate (sps.map fun s => s!"{s.k1},{s.k2},{s.kF},{if s.hz then 1 else 0}")
        IO.println s!"{kk} {lo0} {M} {N} {spStr} {wsStr} {np} {R} {t1 - t0} {okc} {t2 - t1}"
        (← IO.getStdout).flush
  | _ => IO.println "usage: genlow p | rho | tail YT | w YN YD M N | mkp D L epsn epsd tolexp out | gen KF KT LDEN M N tolexp"

def main (args : List String) : IO Unit := lowerMain args
