(* Paper strategy orchestration. The source-derived MCSAT core keeps its
   sample-cell explanations, resolution and backtracking. This file restores
   the published control flow; it is not an unchanged historical executable. *)
BeginPackage["PaperSolvers`"];
SolveProblem::usage = "SolveProblem[polynomials, pairCNF, variables, solver, config]";
FormulaOf::usage = "Exact CNF with atom {i,s} meaning s*polynomials[[i]]>0.";
ModelQ::usage = "Check a complete exact assignment against the original input.";
Begin["`Private`"];

FormulaOf[p_List, c_List] := And @@ (Or @@ ((#[[2]] p[[#[[1]]]] > 0) & /@ #) & /@ c);
ModelQ[p_List, c_List, v_List, a_Association] := Block[{$MaxExtraPrecision = Infinity},
  And[And @@ (KeyExistsQ[a, #] & /@ v),
    And @@ (FreeQ[#, _Real] && TrueQ[Element[#, Reals]] & /@ Lookup[a, v]),
    TrueQ[FormulaOf[p, c] /. Normal[a]]]];
ModelQ[___] := False;
CompleteAssignmentQ[v_List, a_] := AssociationQ[a] && And @@ (KeyExistsQ[a, #] & /@ v);
PairToSigned[c_List] := (#[[1]] #[[2]] & /@ #) & /@ c;

(* Both caches are scoped to ONE SolveProblem invocation. Their keys include
   the complete exact restricted problem; a hit never changes tie-breaking. *)
$RootCache = <||>; $PlaneCache = <||>;
$CacheEnabled = True; $CacheLimit = 20000;
$EngineeringEnabled = True;
$SearchContext = None; $SearchValueCache = <||>;
$SearchLastKey = Missing["NoAssignment"]; $SearchLastData = None;
$LastLocal = <||>;
PutRoot[key_, value_] := If[$CacheEnabled && Length[$RootCache] < $CacheLimit,
  AssociateTo[$RootCache, key -> value]];
PutPlane[key_, value_] := If[$CacheEnabled && Length[$PlaneCache] < $CacheLimit,
  AssociateTo[$PlaneCache, key -> value]];

(* A context belongs to ONE LocalSearch call, including its own residual CNF.
   Function performs exact symbolic substitution; no numeric compilation or
   approximation is used. Clause losses contain no dynamic weights. *)
PrepareSearchContext[p_, c_, v_, delta_] := Module[{atoms, atomIndex},
  atoms = DeleteDuplicates[Flatten[c, 1]];
  atomIndex = AssociationThread[atoms, Range[Length[atoms]]];
  <|"polynomials" -> p, "clauses" -> c, "variables" -> v, "delta" -> delta,
    "atoms" -> atoms, "clause_atom_indices" -> Map[atomIndex[#] &, c, {2}],
    "evaluator" -> Function[Evaluate[v], Evaluate[p]]|>
];

SetAttributes[WithSearchContext, HoldAll];
WithSearchContext[p_, c_, v_, delta_, body_] := Block[
  {$SearchContext = None, $SearchValueCache = <||>,
    $SearchLastKey = Missing["NoAssignment"], $SearchLastData = None},
  If[TrueQ[$EngineeringEnabled], $SearchContext = PrepareSearchContext[p, c, v, delta]];
  body
];

SearchData[p_, c_, a_Association, delta_: Automatic] := Module[
  {coordinates, values, atoms, truth, atomLoss, clauseLoss, data},
  If[! TrueQ[$EngineeringEnabled] || ! AssociationQ[$SearchContext] ||
      p =!= $SearchContext["polynomials"] || c =!= $SearchContext["clauses"] ||
      (delta =!= Automatic && delta =!= $SearchContext["delta"]) ||
      ! CompleteAssignmentQ[$SearchContext["variables"], a], Return[None]];
  coordinates = Lookup[a, $SearchContext["variables"]];
  If[coordinates === $SearchLastKey, Return[$SearchLastData]];
  If[$CacheEnabled && KeyExistsQ[$SearchValueCache, coordinates],
    $SearchLastKey = coordinates; $SearchLastData = $SearchValueCache[coordinates];
    Return[$SearchLastData]];
  values = $SearchContext["evaluator"] @@ coordinates;
  atoms = $SearchContext["atoms"];
  truth = (TrueQ[#[[2]] values[[#[[1]]]] > 0] &) /@ atoms;
  atomLoss = MapThread[If[#1, 0, Abs[#2] + $SearchContext["delta"]] &,
    {truth, values[[First /@ atoms]]}];
  clauseLoss = (Min[atomLoss[[#]]] &) /@ $SearchContext["clause_atom_indices"];
  data = <|"values" -> values, "false_atoms" -> Pick[atoms, truth, False],
    "clause_losses" -> clauseLoss,
    "satisfied" -> ((Or @@ truth[[#]]) & /@ $SearchContext["clause_atom_indices"])|>;
  $SearchLastKey = coordinates; $SearchLastData = data;
  If[$CacheEnabled && Length[$SearchValueCache] < $CacheLimit,
    AssociateTo[$SearchValueCache, coordinates -> data]];
  data
];
SearchData[___] := None;

ExactPolynomialValues[p_, a_] := Module[{data = None},
  If[AssociationQ[$SearchContext], data = SearchData[p, $SearchContext["clauses"], a]];
  If[AssociationQ[data], data["values"], p /. Normal[a]]
];

LocalModelQ[p_, c_, v_, a_] := Module[{data = SearchData[p, c, a]},
  If[AssociationQ[data] && v === $SearchContext["variables"],
    And @@ data["satisfied"], ModelQ[p, c, v, a]]
];

Loss[p_, c_, a_, w_, delta_] := Module[{data = SearchData[p, c, a, delta], values},
  If[AssociationQ[data], Return[Total[w data["clause_losses"]]]];
  values = p /. Normal[a];
  Total[MapThread[#2 Min[(If[TrueQ[#[[2]] values[[#[[1]]]] > 0],
    0, Abs[values[[#[[1]]]]] + delta] & /@ #1)] &, {c, w}]]];
FalseAtoms[p_, c_, a_] := Module[{data = SearchData[p, c, a], values},
  If[AssociationQ[data], Return[data["false_atoms"]]];
  values = p /. Normal[a];
  Select[DeleteDuplicates[Flatten[c, 1]], ! TrueQ[#[[2]] values[[#[[1]]]] > 0] &]];

RootSamples[q_, t_] := Module[{poly = Expand[q], key, roots, intervals, samples, width},
  key = {poly /. t -> HoldComplete[PaperUnivariate], "rational-sector-samples"};
  If[$CacheEnabled && KeyExistsQ[$RootCache, key], Return[$RootCache[key]]];
  If[FreeQ[poly, t], Return[{}]];
  roots = t /. Quiet[Solve[poly == 0, t, Reals, Cubics -> False, Quartics -> False]];
  If[! ListQ[roots] || ! And @@ (TrueQ[Element[#, Reals]] & /@ roots), Return[{}]];
  roots = Sort[DeleteDuplicates[roots], Less];
  samples = If[roots === {}, {1},
    width = 1/10000;
    intervals = IsolatingInterval[#, width] & /@ roots;
    If[! MatchQ[intervals, {{_, _} ..}], Return[{}]];
    (* Every open sector needs a sample, even when distinct algebraic roots
       are closer than the initial isolation width. All comparisons are exact. *)
    While[! And @@ Table[TrueQ[intervals[[k, 2]] < intervals[[k + 1, 1]]],
        {k, Length[intervals] - 1}],
      width = width/10;
      intervals = IsolatingInterval[#, width] & /@ roots];
    DeleteDuplicates[Join[{intervals[[1, 1]] - 1/10000},
      Table[(intervals[[k, 2]] + intervals[[k + 1, 1]])/2,
        {k, Length[intervals] - 1}], {intervals[[-1, 2]] + 1/10000}]]];
  PutRoot[key, samples]; samples
];

BestCandidate[p_, c_, v_, a_, w_, delta_, candidates_List] := Module[
  {valid, before, losses, best, positions},
  valid = DeleteDuplicates[Select[candidates, CompleteAssignmentQ[v, #] &]];
  If[valid === {}, Return[Missing["NoImprovement"]]];
  before = Loss[p, c, a, w, delta];
  losses = Loss[p, c, #, w, delta] & /@ valid;
  best = Min[losses];
  If[! TrueQ[before > best], Return[Missing["NoImprovement"]]];
  positions = Flatten[Position[losses, x_ /; TrueQ[x == best], {1}]];
  If[positions === {}, Return[Missing["NoImprovement"]]];
  valid[[RandomChoice[positions]]]
];

PlainLineCandidates[p_, atoms_, v_, a_, directions_List] := Module[
  {t, candidates = {}, restricted, samples, good, nearest, candidate},
  t = Unique["line$"];
  Do[
    restricted = Expand[p /. Thread[v -> (Lookup[a, v] + t d)]];
    Do[
      samples = RootSamples[restricted[[atom[[1]]]], t];
      good = Select[samples, TrueQ[atom[[2]] (restricted[[atom[[1]]]] /. t -> #) > 0] &];
      If[good =!= {},
        nearest = MinimalBy[good, Abs];
        candidate = Association[Thread[v -> (Lookup[a, v] + RandomChoice[nearest] d)]];
        AppendTo[candidates, candidate]],
      {atom, atoms}], {d, directions}];
  candidates
];

AtomWitness[q_, sign_, tvars_List] := Module[{key, ans},
  key = {Expand[q], sign, tvars};
  If[$CacheEnabled && KeyExistsQ[$PlaneCache, key], Return[$PlaneCache[key]]];
  ans = PaperMCSAT`MCSATSolver[{{sign}}, {Expand[q]}, tvars];
  If[MatchQ[ans, {"sat", _, _Association}] &&
      TrueQ[(sign q /. Normal[ans[[3]]]) > 0],
    ans = <|"status" -> "sat", "assignment" -> ans[[3]]|>,
    ans = If[MatchQ[ans, {"unsat", ___}], <|"status" -> "unsat"|>,
      <|"status" -> "unknown"|>]];
  (* Unknown/error/aborted computations are never cached as UNSAT. *)
  If[ans["status"] =!= "unknown", PutPlane[key, ans]];
  ans
];

PlainPlaneCandidates[p_, atoms_, v_, a_, planes_List] := Module[
  {t1, t2, restricted, candidates = {}, witness, point},
  t1 = Unique["plane$"]; t2 = Unique["plane$"];
  Do[
    If[TrueQ[MatrixRank[basis] == 2],
      restricted = Expand[p /. Thread[v -> (Lookup[a, v] + t1 basis[[1]] + t2 basis[[2]])]];
      Do[
        witness = AtomWitness[restricted[[atom[[1]]]], atom[[2]], {t1, t2}];
        If[witness["status"] === "sat",
          point = Lookup[a, v] + witness["assignment"][t1] basis[[1]] +
            witness["assignment"][t2] basis[[2]];
          AppendTo[candidates, Association[Thread[v -> point]]]],
        {atom, atoms}]], {basis, planes}];
  candidates
];

PlainAxesPlaneCandidates[p_, atoms_, v_, a_] := Module[
  {candidates = {}, partial, restricted, witness, pair},
  Do[
    pair = v[[indices]];
    partial = KeyDrop[a, pair];
    (* Use the two absolute coordinates, as in Section 3.1. Their current
       values are neither substituted into the atom nor used as solver seeds. *)
    restricted = Expand[p /. Normal[partial]];
    Do[
      witness = AtomWitness[restricted[[atom[[1]]]], atom[[2]], pair];
      If[witness["status"] === "sat",
        AppendTo[candidates, Join[a, witness["assignment"]]]],
      {atom, atoms}], {indices, Subsets[Range[Length[v]], {2}]}];
  candidates
];

(* Restrict just the polynomials referenced by the same ordered false atoms.
   Reap/Sow collects candidates in the original direction/atom iteration order.
   RandomChoice is still invoked once at each original call site. *)
RestrictPolynomials[p_, indices_List, rules_List, expand_: True] := Module[
  {restricted = p[[indices]] /. rules},
  AssociationThread[indices, If[TrueQ[expand], Expand[restricted], restricted]]
];

LineCandidates[p_, atoms_, v_, a_, directions_List] := If[! TrueQ[$EngineeringEnabled],
  PlainLineCandidates[p, atoms, v, a, directions], Module[
    {t, current, active, restricted, q, samples, good, nearest, candidate},
    t = Unique["line$"]; current = Lookup[a, v];
    active = DeleteDuplicates[First /@ atoms];
    Flatten[Reap[Do[
      restricted = RestrictPolynomials[p, active, Thread[v -> (current + t d)]];
      Do[
        q = restricted[atom[[1]]]; samples = RootSamples[q, t];
        good = Select[samples, TrueQ[atom[[2]] (q /. t -> #) > 0] &];
        If[good =!= {}, nearest = MinimalBy[good, Abs];
          candidate = Association[Thread[v -> (current + RandomChoice[nearest] d)]];
          Sow[candidate, CandidateOutput]], {atom, atoms}], {d, directions}],
      CandidateOutput][[2]], 1]
  ]
];

PlaneCandidates[p_, atoms_, v_, a_, planes_List] := If[! TrueQ[$EngineeringEnabled],
  PlainPlaneCandidates[p, atoms, v, a, planes], Module[
    {t1, t2, current, active, restricted, witness, point},
    t1 = Unique["plane$"]; t2 = Unique["plane$"];
    current = Lookup[a, v]; active = DeleteDuplicates[First /@ atoms];
    Flatten[Reap[Do[
      If[TrueQ[MatrixRank[basis] == 2],
        restricted = RestrictPolynomials[p, active,
          Thread[v -> (current + t1 basis[[1]] + t2 basis[[2]])]];
        Do[
          witness = AtomWitness[restricted[atom[[1]]], atom[[2]], {t1, t2}];
          If[witness["status"] === "sat",
            point = current + witness["assignment"][t1] basis[[1]] +
              witness["assignment"][t2] basis[[2]];
            Sow[Association[Thread[v -> point]], CandidateOutput]], {atom, atoms}]],
      {basis, planes}], CandidateOutput][[2]], 1]
  ]
];

AxesPlaneCandidates[p_, atoms_, v_, a_] := If[! TrueQ[$EngineeringEnabled],
  PlainAxesPlaneCandidates[p, atoms, v, a], Module[
    {active, partial, restricted, witness, pair},
    active = DeleteDuplicates[First /@ atoms];
    Flatten[Reap[Do[
      pair = v[[indices]]; partial = KeyDrop[a, pair];
      restricted = RestrictPolynomials[p, active, Normal[partial]];
      Do[
        witness = AtomWitness[restricted[atom[[1]]], atom[[2]], pair];
        If[witness["status"] === "sat",
          Sow[Join[a, witness["assignment"]], CandidateOutput]], {atom, atoms}],
      {indices, Subsets[Range[Length[v]], {2}]}], CandidateOutput][[2]], 1]
  ]
];

Reweight[p_, c_, a_, w_, probability_] := Module[{data = SearchData[p, c, a], values, satisfied},
  satisfied = If[AssociationQ[data], data["satisfied"],
    values = p /. Normal[a];
    (Or @@ (TrueQ[#[[2]] values[[#[[1]]]] > 0] & /@ #) &) /@ c];
  If[RandomReal[] >= probability,
    MapThread[If[#2, #1, #1 + 1] &, {w, satisfied}],
    MapThread[If[#2 && #1 > 1, #1 - 1, #1] &, {w, satisfied}]]
];

LocalSearch[p_, c_, v_, restarts_Integer, maxJumps_Integer, twoD_, cfg_Association,
    budget_: Infinity] := Block[{$SearchContext = None, $SearchValueCache = <||>,
      $SearchLastKey = Missing["NoAssignment"], $SearchLastData = None},
  Module[{a, w, atoms, directions, axes, planes,
    candidate, result, jumps = 0, n = Length[v], count, oneRun, delta, probability,
    foundTag = Unique["localModel$"]},
  delta = Lookup[cfg, "l2o_delta", 1];
  probability = Lookup[cfg, "weight_decrease_probability", 0.003];
  count = Lookup[cfg, "random_direction_count", 6];
  axes = If[n == 0, {}, IdentityMatrix[n]];
  $LastLocal = <|"status" -> "unknown", "assignment" -> Association[Thread[v -> ConstantArray[0, n]]],
    "num_jumps" -> 0|>;
  oneRun[] := Catch[
    If[TrueQ[$EngineeringEnabled], $SearchContext = PrepareSearchContext[p, c, v, delta]];
    Do[
      a = Association[Thread[v -> If[r == 1, ConstantArray[0, n], RandomInteger[{-1, 1}, n]]]];
      w = ConstantArray[1, Length[c]];
      $LastLocal = <|"status" -> "unknown", "assignment" -> a, "num_jumps" -> jumps|>;
      Do[
        If[LocalModelQ[p, c, v, a], Throw[<|"status" -> "sat", "assignment" -> a,
          "num_jumps" -> jumps|>, foundTag]];
        If[c === {} || MemberQ[c, {}] || n == 0, Break[]];
        atoms = FalseAtoms[p, c, a];
        candidate = BestCandidate[p, c, v, a, w, delta, LineCandidates[p, atoms, v, a, axes]];
        If[MissingQ[candidate],
          w = Reweight[p, c, a, w, probability];
          directions = Table[RandomInteger[{-1000, 1000}, n], {count}];
          directions = Select[directions, # =!= ConstantArray[0, n] &];
          candidate = BestCandidate[p, c, v, a, w, delta,
            LineCandidates[p, atoms, v, a, directions]];
          If[MissingQ[candidate] && TrueQ[twoD] && n >= 2,
            w = Reweight[p, c, a, w, probability];
            candidate = BestCandidate[p, c, v, a, w, delta,
              AxesPlaneCandidates[p, atoms, v, a]];
            If[MissingQ[candidate],
              w = Reweight[p, c, a, w, probability];
              planes = Partition[directions, 2];
              candidate = BestCandidate[p, c, v, a, w, delta,
                PlaneCandidates[p, atoms, v, a, planes]]]]];
        If[MissingQ[candidate], Break[]];
        a = candidate; jumps++;
        $LastLocal = <|"status" -> "unknown", "assignment" -> a, "num_jumps" -> jumps|>;
        If[LocalModelQ[p, c, v, a], Throw[<|"status" -> "sat", "assignment" -> a,
          "num_jumps" -> jumps|>, foundTag]], {maxJumps}], {r, restarts}];
    $LastLocal, foundTag
  ];
  result = If[budget === Infinity, oneRun[],
    TimeConstrained[oneRun[], Max[0.001, budget], $LastLocal]];
  result
]];

OpenCADSolve[p_, c_, v_] := Module[{formula = FormulaOf[p, c], cad, instances, a},
  If[TrueQ[formula], Return[<|"status" -> "sat", "stage" -> "OpenCAD",
    "assignment" -> Association[Thread[v -> ConstantArray[0, Length[v]]]]|>]];
  If[formula === False, Return[<|"status" -> "unsat", "stage" -> "OpenCAD"|>]];
  cad = Quiet[Check[GenericCylindricalDecomposition[formula, v], $Failed]];
  If[cad === {False, False}, Return[<|"status" -> "unsat", "stage" -> "OpenCAD"|>]];
  If[! MatchQ[cad, {_, _}], Return[<|"status" -> "unknown", "stage" -> "OpenCAD",
    "reason" -> "OpenCAD did not return a decomposition"|>]];
  If[cad[[1]] === False, Return[<|"status" -> "unknown", "stage" -> "OpenCAD",
    "reason" -> "no certified full-dimensional witness"|>]];
  instances = Quiet[Check[FindInstance[cad[[1]], v, Reals, 1], {}]];
  If[MatchQ[instances, {_List ..}],
    a = Association[First[instances]];
    If[ModelQ[p, c, v, a], Return[<|"status" -> "sat", "stage" -> "OpenCAD", "assignment" -> a|>]]];
  <|"status" -> "unknown", "stage" -> "OpenCAD", "reason" -> "exact model verification failed"|>
];

SolveInternal[p_, c_, v_, solver_, cfg_] := Module[
  {n = Length[v], polynum = Length[p], degrees, maxdeg, mindeg, maxJump, stage1Seconds,
    flags, local, initial, count = 0, stage2Start, threshold, after, conflict,
    shouldSwitch, options, raw, result, stage1, stage2, stage3, stage2LS, suggestions},
  If[solver === "OpenCAD", Return[OpenCADSolve[p, c, v]]];
  If[solver === "LS-WL", Return[PaperWolframLS`SolveLS[p, c, v, cfg]]];
  (* Total degrees via coefficient rules avoid substitution/capture and machine arithmetic. *)
  degrees = If[n == 0, ConstantArray[0, Length[p]],
    (If[# === 0, 0, Max[0, Sequence @@ (Total /@ (First /@ CoefficientRules[#, v]))]] &) /@ p];
  maxdeg = Max[0, Sequence @@ degrees]; mindeg = If[degrees === {}, 0, Min[degrees]];
  maxJump = Max[1, Lookup[cfg, "max_jump_multiplier", 100000] Max[1, polynum] Max[1, n]];
  If[MemberQ[{"2D-LS", "1D-control"}, solver],
    local = LocalSearch[p, c, v, Lookup[cfg, "standalone_restarts", 1], maxJump,
      solver === "2D-LS", cfg];
    Return[Join[local, <|"stage" -> solver|>]]];
  If[MemberQ[{"LiMbS", "MCSAT-core"}, solver],
    raw = PaperMCSAT`MCSATSolver[PairToSigned[c], p, v];
    Return[FromMCSAT[raw, "MCSAT"]]];
  flags = Switch[solver,
    "HELMS", {True, True, True, True, True},
    "V1", {False, True, True, True, True},
    "V2", {True, False, True, False, True},
    "V3", {True, True, False, True, True},
    "V4", {False, True, True, False, True},
    "V5", {True, True, True, True, False}, _, Return[<|"status" -> "error", "reason" -> "unknown solver"|>]];
  {stage1, stage2, stage3, stage2LS, suggestions} = flags;
  initial = Association[Thread[v -> ConstantArray[0, n]]];
  stage1Seconds = 2 3^(mindeg/5 - 2) + 2^(polynum/10 - 3/2) + 2^(n/10 - 3/2) + Length[c]/50 - 1/5;
  stage1Seconds = Lookup[cfg, "stage1_seconds_override", stage1Seconds];
  If[stage1,
    local = LocalSearch[p, c, v, Lookup[cfg, "max_restart_stage1", 1], maxJump, True, cfg, stage1Seconds];
    count += local["num_jumps"];
    If[local["status"] === "sat", Return[Join[local, <|"stage" -> "Stage1"|>]]];
    If[suggestions, initial = local["assignment"]]];
  If[! stage2, Return[OpenCADSolve[p, c, v]]];
  threshold = Lookup[cfg, "open_cad_threshold_multiplier", 0.1] Min[polynum, maxdeg] n;
  stage2Start = AbsoluteTime[];
  after = Function[{prefix, full, nextLevel, maxLevel}, Module[{level, residual, rest, sub},
    level = Length[prefix];
    If[stage2LS && Min[2 n/5, 9 maxLevel/10] < level < n - 2,
      residual = Expand[p /. Normal[prefix]]; rest = Drop[v, level];
      sub = LocalSearch[residual, c, rest, Lookup[cfg, "max_restart_stage2", 3], maxJump, True, cfg];
      count += sub["num_jumps"];
      If[sub["status"] === "sat" && ModelQ[p, c, v, Join[prefix, sub["assignment"]]],
        <|"status" -> "sat", "assignment" -> Join[prefix, sub["assignment"]]|>,
        <|"status" -> "unknown", "assignment" -> If[suggestions, sub["assignment"], <||>]|>],
      <|"status" -> "unknown", "assignment" -> <||>|>]
  ]];
  conflict = Function[Null, count++];
  shouldSwitch = Function[Null, TrueQ[stage3 &&
    AbsoluteTime[] - stage2Start > Lookup[cfg, "open_cad_min_stage2_seconds", 20] &&
    maxdeg > Lookup[cfg, "open_cad_min_degree_exclusive", 2] && count > threshold]];
  options = <|"InitialAssignment" -> initial, "AfterAssign" -> after,
    "OnTheoryConflict" -> conflict, "ShouldSwitch" -> shouldSwitch|>;
  raw = PaperMCSAT`MCSATSolver[PairToSigned[c], p, v, options];
  result = If[MatchQ[raw, {"switch", ___}], OpenCADSolve[p, c, v], FromMCSAT[raw, "Stage2"]];
  Join[result, <|"num_fail_cells_estimate" -> count|>]
];

FromMCSAT[raw_, stage_] := Which[
  MatchQ[raw, {"sat", _, _Association}], <|"status" -> "sat", "stage" ->
    If[MemberQ[{"mcsat-ELS", "MCSAT:local-search"}, raw[[2]]], "Stage2-2D-LS", stage], "assignment" -> raw[[3]]|>,
  MatchQ[raw, {"unsat", ___}], <|"status" -> "unsat", "stage" -> stage|>,
  True, <|"status" -> "unknown", "stage" -> stage, "reason" -> ToString[raw, InputForm]|>
];

SolveProblem[p_List, c_List, v_List, solver_String, cfg_Association] := Block[
  (* Exact algebraic comparisons may need more than Mathematica's default
     50 extra digits. Permit refinement within the existing outer time budget;
     no approximate arithmetic, tolerance or message suppression is introduced.
     This scope is shared by every solver mode, including LS-WL. *)
  {$MaxExtraPrecision = Infinity,
    $RootCache = <||>, $PlaneCache = <||>, $CacheEnabled = Lookup[cfg, "cache_enabled", True],
    $CacheLimit = Lookup[cfg, "cache_max_entries", 20000],
    $EngineeringEnabled = Lookup[cfg, "engineering_optimizations", True], $SearchContext = None},
  Module[{result = SolveInternal[p, c, v, solver, cfg]},
    If[AssociationQ[result] && Lookup[result, "status", "error"] === "sat" &&
      ! ModelQ[p, c, v, Lookup[result, "assignment", <||>]],
      <|"status" -> "error", "stage" -> Lookup[result, "stage", "unknown"],
        "reason" -> "SAT model does not satisfy original input"|>, result]]
];
End[];
EndPackage[];
Get[FileNameJoin[{DirectoryName[$InputFileName], "WolframLS.wl"}]];
