(* Paper strategy orchestration. The source-derived MCSAT core keeps its
   sample-cell explanations, resolution and backtracking. This file restores
   the published control flow; it is not an unchanged historical executable. *)
Get[FileNameJoin[{DirectoryName[$InputFileName], "LocalSearchSupport.wl"}]];
BeginPackage["TwoDLSCore`"];
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
$LocalIntervals = None;
$LocalBounds = {};
$CandidateSeconds = Infinity; $CandidateTimeouts = 0;
$LocalTracePath = None; $TraceRound = 0; $TraceJumps = 0; $TraceStage = "initialization";
$LocalDeadline = Infinity; $RoundDeadline = Infinity;
$LocalDeadlineTag = None; $RoundDeadlineTag = None;
DeadlineRemaining[deadline_] := If[deadline === Infinity, Infinity,
  Max[0, deadline - SessionTime[]]];
CheckLocalDeadline[] := (
  If[DeadlineRemaining[$LocalDeadline] <= 0, Throw["local-budget-exhausted", $LocalDeadlineTag]];
  If[DeadlineRemaining[$RoundDeadline] <= 0, Throw["round-budget-exhausted", $RoundDeadlineTag]]);
TraceLocal[event_String, fields_Association: <||>] := If[StringQ[$LocalTracePath],
  Module[{stream},
    stream = Quiet[Check[OpenAppend[$LocalTracePath, CharacterEncoding -> "UTF-8"], $Failed]];
    If[Head[stream] === OutputStream,
      WriteString[stream, ExportString[Join[<|"event" -> event,
        "session_seconds" -> SessionTime[], "round" -> $TraceRound,
        "num_jumps" -> $TraceJumps, "stage" -> $TraceStage|>, fields], "RawJSON"], "\n"];
      Close[stream]]], Null];
RationalAssignmentBits[a_Association] := Max[0, Sequence @@ Map[
  If[IntegerQ[#] || Head[#] === Rational,
    Max[IntegerLength[Abs[Numerator[#]], 2], IntegerLength[Denominator[#], 2]], 0] &,
  Values[a]]];
SetAttributes[BoundedCandidate, HoldAll];
BoundedCandidate[expression_, fallback_, kind_String: "candidate"] := Module[
  {value, localRemaining, roundRemaining, cap, capKind,
   timedOut = Unique["candidateTimedOut$"]},
  CheckLocalDeadline[];
  localRemaining = DeadlineRemaining[$LocalDeadline];
  roundRemaining = DeadlineRemaining[$RoundDeadline];
  cap = Min[$CandidateSeconds, localRemaining, roundRemaining];
  capKind = Which[localRemaining <= Min[$CandidateSeconds, roundRemaining], "local",
    roundRemaining <= $CandidateSeconds, "round", True, "candidate"];
  TraceLocal["candidate_started", <|"kind" -> kind|>];
  value = If[cap === Infinity,
    expression, TimeConstrained[expression, cap, timedOut]];
  (* Do not Throw from a native TimeConstrained fallback. Handle its marker
     after the timed evaluation has unwound, then apply the explicit deadline. *)
  If[value === timedOut,
    Switch[capKind,
      "local", Throw["local-budget-exhausted", $LocalDeadlineTag],
      "round", Throw["round-budget-exhausted", $RoundDeadlineTag],
      _, $CandidateTimeouts++; TraceLocal["candidate_budget_exhausted", <|"kind" -> kind|>];
        value = fallback]];
  CheckLocalDeadline[];
  TraceLocal["candidate_finished", <|"kind" -> kind|>]; value];
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

SatisfiedClauseCount[p_, c_, a_] := Module[{data = SearchData[p, c, a], values},
  If[AssociationQ[data], Return[Count[data["satisfied"], True]]];
  values = p /. Normal[a];
  Count[(Or @@ (TrueQ[#[[2]] values[[#[[1]]]] > 0] & /@ #) &) /@ c, True]
];

(* Every bound is a necessary open constraint of the original local CNF.
   No bound is extracted from a disjunction. Bounds do not establish SAT. *)
BoundPolynomials[v_, intervals_] := Flatten[Table[
  Join[If[intervals[x][[1]] === -Infinity, {}, {x - intervals[x][[1]]}],
    If[intervals[x][[2]] === Infinity, {}, {intervals[x][[2]] - x}]], {x, v}]];
InLocalBoundsQ[v_, a_] := ! AssociationQ[$LocalIntervals] ||
  And @@ (TrueQ[$LocalIntervals[#][[1]] < a[#] < $LocalIntervals[#][[2]]] & /@ v);
LineDomain[v_, a_, d_] := If[AssociationQ[$LocalIntervals],
  TwoDLSLocalSupport`LineParameterInterval[v, a, d, $LocalIntervals], {-Infinity, Infinity}];
LineGoodSamples[q_, sign_, t_, domain_] := BoundedCandidate[If[domain === {-Infinity, Infinity},
  Select[RootSamples[q, t], TrueQ[sign (q /. t -> #) > 0] &],
  TwoDLSLocalSupport`IntervalLineSamples[q, sign, t, domain]], {}, "line"];

RootSamples[q_, t_] := Module[{poly = Expand[q], key, samples},
  key = {poly /. t -> HoldComplete[PaperUnivariate], "primitive-rational-sector-samples-v3",
    TwoDLSLocalSupport`$SectorSamplePolicy};
  If[$CacheEnabled && KeyExistsQ[$RootCache, key], Return[$RootCache[key]]];
  If[FreeQ[poly, t], Return[{}]];
  samples = TwoDLSLocalSupport`PolynomialSectorSamples[poly, t];
  PutRoot[key, samples]; samples
];

BestCandidate[p_, c_, v_, a_, w_, delta_, candidates_List] := Module[
  {valid, before, losses, best, positions},
  valid = DeleteDuplicates[Select[candidates, CompleteAssignmentQ[v, #] && InLocalBoundsQ[v, #] &]];
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
  {t, candidates = {}, restricted, good, nearest, candidate, domain},
  t = Unique["line$"];
  Do[
    domain = LineDomain[v, a, d]; If[MissingQ[domain], Continue[]];
    restricted = Expand[p /. Thread[v -> (Lookup[a, v] + t d)]];
    Do[
      good = LineGoodSamples[restricted[[atom[[1]]]], atom[[2]], t, domain];
      If[good =!= {},
        nearest = MinimalBy[good, Abs];
        candidate = Association[Thread[v -> (Lookup[a, v] + RandomChoice[nearest] d)]];
        AppendTo[candidates, candidate]],
      {atom, atoms}], {d, directions}];
  candidates
];

AtomWitness[q_, sign_, tvars_List, extra_List: {}] := Module[
  {key, ans, conditions, constantConditions, cnf},
  conditions = DeleteDuplicates[Expand /@ Prepend[extra, sign q]];
  constantConditions = Select[conditions, FreeQ[#, Alternatives @@ tvars] &];
  If[AnyTrue[constantConditions, TrueQ[# <= 0] &], Return[<|"status" -> "unsat"|>]];
  conditions = Select[conditions, ! TrueQ[# > 0] &];
  key = {conditions, tvars, "unit-bound-constrained-atom"};
  If[$CacheEnabled && KeyExistsQ[$PlaneCache, key], Return[$PlaneCache[key]]];
  cnf = List /@ Range[Length[conditions]];
  ans = BoundedCandidate[PaperMCSAT`MCSATSolver[cnf, conditions, tvars],
    {"candidate-budget-exhausted"}, "plane"];
  If[MatchQ[ans, {"sat", _, _Association}] &&
      CompleteAssignmentQ[tvars, ans[[3]]] &&
      And @@ (TrueQ[(# /. Normal[ans[[3]]]) > 0] & /@ conditions),
    ans = <|"status" -> "sat", "assignment" -> ans[[3]]|>,
    ans = If[MatchQ[ans, {"unsat", ___}], <|"status" -> "unsat"|>, <|"status" -> "unknown"|>]];
  If[ans["status"] =!= "unknown", PutPlane[key, ans]];
  ans
];

(* A separate SAT-only check of the complete residual CNF, restoring a
   capability present in the original ELS0 implementation.  Only the chosen
   coordinates are free. UNSAT of this restriction is not global UNSAT.
   BoundedCandidate includes both the solve and exact full-formula check. *)
FullResidualPlaneCheck[p_, c_, v_, a_, indices_List] := BoundedCandidate[
  Module[{pair = v[[indices]], fixed, restricted, answer, candidate},
    fixed = KeyDrop[a, pair];
    restricted = Expand[p /. Normal[fixed]];
    answer = PaperMCSAT`MCSATSolver[PairToSigned[c], restricted, pair];
    If[MatchQ[answer, {"unsat", ___}],
      Return[<|"status" -> "restricted-unsat"|>]];
    If[! MatchQ[answer, {"sat", _, _Association}] ||
        ! CompleteAssignmentQ[pair, answer[[3]]],
      Return[<|"status" -> "unknown", "reason" -> "no complete plane witness"|>]];
    candidate = Join[a, KeyTake[answer[[3]], pair]];
    If[ModelQ[p, c, v, candidate],
      <|"status" -> "sat", "assignment" -> candidate|>,
      <|"status" -> "unknown", "reason" -> "full original model check failed"|>]],
  <|"status" -> "unknown", "reason" -> "candidate budget exhausted"|>,
  "full-residual-coordinate-plane"];

PlainPlaneCandidates[p_, atoms_, v_, a_, planes_List] := Module[
  {t1, t2, restricted, candidates = {}, witness, point},
  t1 = Unique["plane$"]; t2 = Unique["plane$"];
  Do[
    If[TrueQ[MatrixRank[basis] == 2],
      restricted = Expand[p /. Thread[v -> (Lookup[a, v] + t1 basis[[1]] + t2 basis[[2]])]];
      Do[
        witness = AtomWitness[restricted[[atom[[1]]]], atom[[2]], {t1, t2},
          Expand[$LocalBounds /. Thread[v -> (Lookup[a, v] + t1 basis[[1]] + t2 basis[[2]])]]];
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
      witness = AtomWitness[restricted[[atom[[1]]]], atom[[2]], pair, Expand[$LocalBounds /. Normal[partial]]];
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
    {t, current, active, restricted, q, good, nearest, candidate, domain},
    t = Unique["line$"]; current = Lookup[a, v];
    active = DeleteDuplicates[First /@ atoms];
    Flatten[Reap[Do[
      domain = LineDomain[v, a, d]; If[MissingQ[domain], Continue[]];
      restricted = RestrictPolynomials[p, active, Thread[v -> (current + t d)]];
      Do[
        q = restricted[atom[[1]]]; good = LineGoodSamples[q, atom[[2]], t, domain];
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
          witness = AtomWitness[restricted[atom[[1]]], atom[[2]], {t1, t2},
            Expand[$LocalBounds /. Thread[v -> (current + t1 basis[[1]] + t2 basis[[2]])]]];
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
        witness = AtomWitness[restricted[atom[[1]]], atom[[2]], pair, Expand[$LocalBounds /. Normal[partial]]];
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
      $SearchLastKey = Missing["NoAssignment"], $SearchLastData = None,
      $LocalIntervals = None, $LocalBounds = {},
      $CandidateSeconds = Lookup[cfg, "local_candidate_seconds", 2], $CandidateTimeouts = 0,
      $LocalTracePath = Lookup[cfg, "local_trace_path", None], $TraceRound = 0, $TraceJumps = 0,
      $TraceStage = "initialization", $LocalDeadline = Infinity, $RoundDeadline = Infinity,
      $LocalDeadlineTag = Unique["localDeadline$"], $RoundDeadlineTag = Unique["roundDeadline$"],
      TwoDLSLocalSupport`$SectorSamplePolicy = "near-origin"},
  Module[{a, w, atoms, directions, axes, planes,
    candidate, result, jumps = 0, n = Length[v], count, oneRun, oneRound, delta, probability,
    foundTag = Unique["localModel$"], preprocessing, directionFamily, attempted = 0,
    totalBudget, requestBudget, configuredBudget, roundBudget, roundTimeouts = 0,
    experimentDeadline, experimentRemaining, wholeExperimentBudget,
    totalBudgetExhausted = False, experimentBudgetExhausted = False, cycleRestarts = 0,
    assignmentBitLimit = Lookup[cfg, "local_assignment_bit_limit", 4096],
    assignmentBits = 0, maximumAssignmentBits = 0, complexityRestarts = 0,
    stagnationLimit = Lookup[cfg, "local_stagnation_jump_limit", 64],
    bestSatisfied = 0, currentSatisfied = 0, maximumSatisfied = 0,
    jumpsWithoutClauseImprovement = 0, stagnationRestarts = 0,
    sectorPolicy = Lookup[cfg, "local_sector_policy", "alternating"],
    effectiveRoundBudget, roundCapKind, roundTimedOut = Unique["roundTimedOut$"],
    fullPlaneCheck = TrueQ[twoD] && TrueQ[Lookup[cfg, "local_full_plane_check", False]],
    fullPlanePairs, fullPlaneIndices, fullPlaneResult,
    fullPlaneChecks = 0, fullPlaneRestrictedUnsat = 0, fullPlaneUnknown = 0,
    fullPlaneModels = 0,
    visited, cycleState, cycleKey, roundResult},
  delta = Lookup[cfg, "l2o_delta", 1];
  probability = Lookup[cfg, "weight_decrease_probability", 0.003];
  count = Lookup[cfg, "random_direction_count", 6];
  requestBudget = Lookup[cfg, "experiment_timeout_seconds", Infinity];
  If[! TrueQ[requestBudget === Infinity || (NumberQ[requestBudget] && requestBudget > 0)],
    requestBudget = Infinity];
  experimentDeadline = Lookup[cfg, "experiment_deadline_session_seconds",
    If[requestBudget === Infinity, Infinity, SessionTime[] + requestBudget]];
  experimentRemaining = DeadlineRemaining[experimentDeadline];
  configuredBudget = Lookup[cfg, "local_search_seconds",
    If[requestBudget === Infinity, 1200, requestBudget]];
  If[! TrueQ[configuredBudget === Infinity || (NumberQ[configuredBudget] && configuredBudget > 0)],
    configuredBudget = If[requestBudget === Infinity, 1200, requestBudget]];
  totalBudget = Min[budget, configuredBudget, requestBudget, experimentRemaining];
  wholeExperimentBudget = experimentDeadline =!= Infinity &&
    TrueQ[totalBudget >= experimentRemaining];
  roundBudget = Lookup[cfg, "local_round_seconds", totalBudget/Max[1, restarts]];
  If[! TrueQ[$CandidateSeconds === Infinity || (NumberQ[$CandidateSeconds] && $CandidateSeconds > 0)],
    $CandidateSeconds = 2];
  If[! TrueQ[totalBudget === Infinity || (NumberQ[totalBudget] && totalBudget > 0)],
    totalBudget = 0];
  If[! TrueQ[roundBudget === Infinity || (NumberQ[roundBudget] && roundBudget > 0)],
    roundBudget = totalBudget/Max[1, restarts]];
  If[! TrueQ[assignmentBitLimit === Infinity ||
      (IntegerQ[assignmentBitLimit] && assignmentBitLimit > 0)], assignmentBitLimit = 4096];
  If[stagnationLimit === 0, stagnationLimit = Infinity];
  If[! TrueQ[stagnationLimit === Infinity ||
      (IntegerQ[stagnationLimit] && stagnationLimit > 0)], stagnationLimit = 64];
  If[! MemberQ[{"alternating", "near-origin", "interior"}, sectorPolicy], sectorPolicy = "alternating"];
  $LocalDeadline = If[totalBudget === Infinity, Infinity,
    Min[SessionTime[] + totalBudget, experimentDeadline]];
  axes = If[n == 0, {}, IdentityMatrix[n]];
  fullPlanePairs = If[fullPlaneCheck && n >= 2, Subsets[Range[n], {2}], {}];
  preprocessing = TwoDLSLocalSupport`UnitLinearIntervals[p, c, v];
  If[! TrueQ[preprocessing["consistent"]],
    Return[<|"status" -> "unknown", "assignment" -> AssociationThread[v, ConstantArray[0, n]],
      "num_jumps" -> 0, "restarts_attempted" -> 0,
      "reason" -> "inconsistent necessary unit bounds; local search does not report UNSAT"|>]];
  $LocalIntervals = preprocessing["intervals"];
  $LocalBounds = BoundPolynomials[v, $LocalIntervals];
  $LastLocal = <|"status" -> "unknown", "assignment" -> Association[Thread[v -> ConstantArray[0, n]]],
    "num_jumps" -> 0|>;
  oneRound[r_] := (
      $TraceRound = r;
      $TraceStage = "initialization";
      TwoDLSLocalSupport`$SectorSamplePolicy = If[sectorPolicy === "alternating",
        If[OddQ[r], "near-origin", "interior"], sectorPolicy];
      TraceLocal["round_started"];
      a = TwoDLSLocalSupport`OriginalStyleInitialAssignment[v, $LocalIntervals, r];
      w = ConstantArray[1, Length[c]];
      visited = <||>;
      bestSatisfied = SatisfiedClauseCount[p, c, a];
      maximumSatisfied = Max[maximumSatisfied, bestSatisfied];
      jumpsWithoutClauseImprovement = 0;
      $LastLocal = <|"status" -> "unknown", "assignment" -> a, "num_jumps" -> jumps|>;
      CheckLocalDeadline[];
      If[LocalModelQ[p, c, v, a], Throw[<|"status" -> "sat", "assignment" -> a,
        "num_jumps" -> jumps|>, foundTag]];
      (* One deterministic coordinate plane per restart, independent of case
         names and labels. This check is separate from target-atom cell jumps. *)
      If[fullPlanePairs =!= {},
        fullPlaneIndices = fullPlanePairs[[1 + Mod[r - 1, Length[fullPlanePairs]]]];
        fullPlaneChecks++;
        $TraceStage = "full-residual-coordinate-plane";
        TraceLocal["full_residual_plane_started", <|"plane_indices" -> fullPlaneIndices|>];
        fullPlaneResult = FullResidualPlaneCheck[p, c, v, a, fullPlaneIndices];
        TraceLocal["full_residual_plane_finished", <|"plane_indices" -> fullPlaneIndices,
          "status" -> fullPlaneResult["status"]|>];
        Switch[fullPlaneResult["status"],
          "sat", fullPlaneModels++;
            Throw[<|"status" -> "sat", "assignment" -> fullPlaneResult["assignment"],
              "num_jumps" -> jumps|>, foundTag],
          "restricted-unsat", fullPlaneRestrictedUnsat++,
          _, fullPlaneUnknown++]];
      Do[
        CheckLocalDeadline[];
        $TraceStage = "model-check";
        assignmentBits = RationalAssignmentBits[a];
        maximumAssignmentBits = Max[maximumAssignmentBits, assignmentBits];
        If[LocalModelQ[p, c, v, a], Throw[<|"status" -> "sat", "assignment" -> a,
          "num_jumps" -> jumps|>, foundTag]];
        If[c === {} || MemberQ[c, {}] || n == 0, Break[]];
        (* Strictly positive continuous-loss moves can keep approaching a
           boundary while no additional clause becomes true. Restart after a
           configurable plateau in the best unweighted clause count. This does
           not change the four-strategy priority or bypass a positive line jump. *)
        If[stagnationLimit =!= Infinity && jumpsWithoutClauseImprovement >= stagnationLimit,
          stagnationRestarts++;
          TraceLocal["clause_count_stagnation_restart", <|
            "best_satisfied_clauses" -> bestSatisfied,
            "jumps_without_clause_improvement" -> jumpsWithoutClauseImprovement|>];
          Break[]];
        If[assignmentBitLimit =!= Infinity && assignmentBits > assignmentBitLimit,
          complexityRestarts++;
          TraceLocal["assignment_complexity_restart", <|"rational_assignment_bits" -> assignmentBits|>];
          Break[]];
        (* Reweighting can make a previous assignment useful again. Only the
           complete assignment AND exact weight vector identify a repeat.
           Hash buckets retain exact states, so collisions do not end a run. *)
        cycleState = {a, w}; cycleKey = Hash[cycleState, "SHA256"];
        If[KeyExistsQ[visited, cycleKey] &&
            AnyTrue[visited[cycleKey], SameQ[#, cycleState] &],
          cycleRestarts++; TraceLocal["cycle_restart"]; Break[]];
        If[KeyExistsQ[visited, cycleKey],
          AssociateTo[visited, cycleKey -> Append[visited[cycleKey], cycleState]],
          AssociateTo[visited, cycleKey -> {cycleState}]];
        atoms = FalseAtoms[p, c, a];
        $TraceStage = "coordinate-lines"; TraceLocal["stage_started"];
        candidate = BestCandidate[p, c, v, a, w, delta, LineCandidates[p, atoms, v, a, axes]];
        TraceLocal["stage_finished"];
        If[MissingQ[candidate],
          w = Reweight[p, c, a, w, probability];
          directionFamily = TwoDLSLocalSupport`SourceDirectionFamily[p, v, a, count];
          directions = directionFamily["all"];
          $TraceStage = "general-lines"; TraceLocal["stage_started"];
          candidate = BestCandidate[p, c, v, a, w, delta,
            LineCandidates[p, atoms, v, a, directions]];
          TraceLocal["stage_finished"];
          If[MissingQ[candidate] && TrueQ[twoD] && n >= 2,
            w = Reweight[p, c, a, w, probability];
            $TraceStage = "coordinate-planes"; TraceLocal["stage_started"];
            candidate = BestCandidate[p, c, v, a, w, delta,
              AxesPlaneCandidates[p, atoms, v, a]];
            TraceLocal["stage_finished"];
            If[MissingQ[candidate],
              w = Reweight[p, c, a, w, probability];
              planes = Partition[directionFamily["random"], 2];
              $TraceStage = "random-planes"; TraceLocal["stage_started"];
              candidate = BestCandidate[p, c, v, a, w, delta,
                PlaneCandidates[p, atoms, v, a, planes]];
              TraceLocal["stage_finished"]]]];
        If[MissingQ[candidate], Break[]];
        a = candidate; jumps++;
        maximumAssignmentBits = Max[maximumAssignmentBits, RationalAssignmentBits[a]];
        currentSatisfied = SatisfiedClauseCount[p, c, a];
        If[currentSatisfied > bestSatisfied,
          bestSatisfied = currentSatisfied; jumpsWithoutClauseImprovement = 0,
          jumpsWithoutClauseImprovement++];
        maximumSatisfied = Max[maximumSatisfied, currentSatisfied];
        $TraceJumps = jumps;
        $LastLocal = <|"status" -> "unknown", "assignment" -> a, "num_jumps" -> jumps|>;
        If[LocalModelQ[p, c, v, a], Throw[<|"status" -> "sat", "assignment" -> a,
          "num_jumps" -> jumps|>, foundTag]], {maxJumps}];
      Null
  );
  oneRun[] := Catch[
    CheckLocalDeadline[];
    If[TrueQ[$EngineeringEnabled], $SearchContext = PrepareSearchContext[p, c, v, delta]];
    Do[
      $RoundDeadline = Infinity; CheckLocalDeadline[];
      attempted = r;
      effectiveRoundBudget = Min[roundBudget, DeadlineRemaining[$LocalDeadline]];
      roundCapKind = If[DeadlineRemaining[$LocalDeadline] <= roundBudget, "local", "round"];
      $RoundDeadline = If[effectiveRoundBudget === Infinity, Infinity,
        Min[SessionTime[] + effectiveRoundBudget, $LocalDeadline]];
      roundResult = Catch[
        If[effectiveRoundBudget === Infinity, oneRound[r],
          TimeConstrained[oneRound[r], effectiveRoundBudget, roundTimedOut]],
        $RoundDeadlineTag, Function[{value, tag},
          roundTimeouts++; TraceLocal["round_budget_exhausted"]; value]];
      If[roundResult === roundTimedOut,
        If[roundCapKind === "local", Throw["local-budget-exhausted", $LocalDeadlineTag],
          roundTimeouts++; TraceLocal["round_budget_exhausted"]]];
      $RoundDeadline = Infinity; CheckLocalDeadline[];
      TraceLocal["round_finished"],
      {r, restarts}];
    $LastLocal, foundTag
  ];
  result = Catch[
    oneRun[],
    $LocalDeadlineTag, Function[{value, tag}, totalBudgetExhausted = True;
      experimentBudgetExhausted = wholeExperimentBudget || DeadlineRemaining[experimentDeadline] <= 0;
      TraceLocal["local_budget_exhausted"]; $LastLocal]];
  If[experimentBudgetExhausted,
    result = Join[result, <|"status" -> "timeout", "stage" -> "timeout"|>]];
  Join[result, <|"restarts_attempted" -> attempted,
    "reason" -> Which[result["status"] === "sat", "", experimentBudgetExhausted,
      "experiment time budget exhausted without a model", totalBudgetExhausted,
      "local search time budget exhausted without a model",
      roundTimeouts > 0, "finite local-search rounds exhausted; some rounds reached their time budget",
      True, "finite local-search rounds exhausted without a model"],
    "solver_metadata" -> <|"local_search_revision" -> "primitive-rational-residual-plane-v5",
      "full_residual_plane_check" -> fullPlaneCheck,
      "full_residual_plane_policy" -> "one rotating coordinate pair at initialization of each search round; complete residual original CNF; SAT only after full exact model check",
      "full_residual_plane_checks" -> fullPlaneChecks,
      "full_residual_planes_unsat" -> fullPlaneRestrictedUnsat,
      "full_residual_planes_inconclusive" -> fullPlaneUnknown,
      "full_residual_plane_verified_models" -> fullPlaneModels,
      "full_residual_plane_candidate_seconds" -> If[$CandidateSeconds === Infinity, "Infinity", $CandidateSeconds],
      "standalone_restart_limit" -> restarts,
      "restarts_attempted" -> attempted,
      "local_search_seconds" -> If[totalBudget === Infinity, "Infinity", totalBudget],
      "local_round_seconds" -> If[roundBudget === Infinity, "Infinity", roundBudget],
      "local_candidate_seconds" -> If[$CandidateSeconds === Infinity, "Infinity", $CandidateSeconds],
      "experiment_timeout_seconds" -> If[requestBudget === Infinity, "Infinity", requestBudget],
      "total_local_budget_exhausted" -> totalBudgetExhausted,
      "experiment_time_budget_exhausted" -> experimentBudgetExhausted,
      "candidate_budget_exhaustions" -> $CandidateTimeouts,
      "round_budget_exhaustions" -> roundTimeouts,
      "cycle_restarts" -> cycleRestarts,
      "cycle_state" -> "complete exact assignment and clause weights",
      "local_assignment_bit_limit" -> If[assignmentBitLimit === Infinity, "Infinity", assignmentBitLimit],
      "maximum_rational_assignment_bits" -> maximumAssignmentBits,
      "assignment_complexity_restarts" -> complexityRestarts,
      "local_stagnation_jump_limit" -> If[stagnationLimit === Infinity, "Infinity", stagnationLimit],
      "clause_count_stagnation_restarts" -> stagnationRestarts,
      "maximum_satisfied_clause_count" -> maximumSatisfied,
      "stagnation_basis" -> "jumps without improving the best unweighted satisfied-clause count within a round",
      "sector_sampling_policy" -> sectorPolicy,
      "local_trace_enabled" -> StringQ[$LocalTracePath],
      "unit_bound_count" -> Length[preprocessing["used_atoms"]],
      "direction_policy" -> "source gradients/current plus configured random vectors",
      "initialization_policy" -> "strict unit-bound interior; source one/sign/rational preferences",
      "plane_policy" -> "one target-atom witness subject to necessary unit bounds; highest positive score"|>|>]
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
  If[solver === "LS-WL", Return[TwoDLSWolframLS`SolveLS[p, c, v, cfg]]];
  (* Total degrees via coefficient rules avoid substitution/capture and machine arithmetic. *)
  degrees = If[n == 0, ConstantArray[0, Length[p]],
    (If[# === 0, 0, Max[0, Sequence @@ (Total /@ (First /@ CoefficientRules[#, v]))]] &) /@ p];
  maxdeg = Max[0, Sequence @@ degrees]; mindeg = If[degrees === {}, 0, Min[degrees]];
  maxJump = Max[1, Lookup[cfg, "max_jump_multiplier", 100000] Max[1, polynum] Max[1, n]];
  If[MemberQ[{"2D-LS", "1D-control"}, solver],
    local = LocalSearch[p, c, v, Lookup[cfg, "standalone_restarts", 1], maxJump,
      solver === "2D-LS", If[solver === "2D-LS",
        Join[cfg, <|"local_full_plane_check" ->
          TrueQ[Lookup[cfg, "standalone_full_plane_check", True]]|>], cfg]];
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
